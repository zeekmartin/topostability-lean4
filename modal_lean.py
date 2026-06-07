"""
Modal.com build environment for the `topostability` Lean 4 project.

Lean toolchain : leanprover/lean4:v4.30.0-rc2   (from lean-toolchain)
Mathlib        : pinned via lake-manifest.json   (master @ 42a89fc…)
Repo           : https://github.com/zeekmartin/topostability-lean4.git

Usage
-----
    modal run modal_lean.py::setup        # one-time: clone + cache get + first build
    modal run modal_lean.py::build        # incremental `lake build`
    modal run modal_lean.py::check_sorry  # grep -n sorry across all .lean files
    modal run modal_lean.py::lean_check --code "example : 1 = 1 := rfl"

The Mathlib `.lake` cache and the project checkout are persisted in a Modal
Volume ("lean-mathlib-cache"), so the ~8000-file Mathlib download only happens
once. Lean is CPU-only — no GPU is requested anywhere.
"""

import subprocess

import modal

# --------------------------------------------------------------------------- #
# Versions / constants
# --------------------------------------------------------------------------- #
LEAN_TOOLCHAIN = "leanprover/lean4:v4.30.0-rc2"
REPO_URL = "https://github.com/zeekmartin/topostability-lean4.git"

# Where the persistent volume is mounted, and where the repo lives inside it.
# Use a dedicated, never-referenced path so Modal sees an empty mount point.
VOLUME_MOUNT = "/vol"
PROJECT_DIR = f"{VOLUME_MOUNT}/topostability-lean4"

# elan / lake live here once the image is built.
ELAN_HOME = "/root/.elan"
BASE_PATH = "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

# Baked into the image. Must NOT reference VOLUME_MOUNT, or Modal refuses to
# mount the volume ("cannot mount volume on non-empty path").
IMAGE_ENV = {
    "PATH": f"{ELAN_HOME}/bin:{BASE_PATH}",
    "ELAN_HOME": ELAN_HOME,
}

# Applied at runtime inside each function. Keeps Lake's downloaded Mathlib
# .ltar cache on the volume too, so even a fresh container that needs to
# re-unpack doesn't re-download from the net.
ENV = {
    **IMAGE_ENV,
    "XDG_CACHE_HOME": f"{VOLUME_MOUNT}/.xdg-cache",
}

# --------------------------------------------------------------------------- #
# Image: elan + Lean v4.30.0-rc2 + git, toolchain baked in at build time.
# --------------------------------------------------------------------------- #
image = (
    modal.Image.debian_slim(python_version="3.12")
    .apt_install("git", "curl", "build-essential")
    .run_commands(
        # Install elan and the exact toolchain the project pins. Baking the
        # toolchain into the image layer means containers start build-ready.
        #
        # We download the elan-init binary directly (with retries) rather than
        # piping the installer script through `sh`, because the script's own
        # internal curl has no retry and flakes on transient GitHub TLS resets
        # ("curl: (35) Recv failure: Connection reset by peer").
        "curl -sSfL --retry 8 --retry-all-errors --retry-delay 5 "
        "-o /tmp/elan.tar.gz "
        "https://github.com/leanprover/elan/releases/latest/download/"
        "elan-x86_64-unknown-linux-gnu.tar.gz",
        "tar -xzf /tmp/elan.tar.gz -C /tmp",
        f"/tmp/elan-init -y --no-modify-path --default-toolchain {LEAN_TOOLCHAIN}",
        "rm -f /tmp/elan.tar.gz /tmp/elan-init",
        f"{ELAN_HOME}/bin/lean --version",
    )
    .env(IMAGE_ENV)
)

app = modal.App("topostability-lean")

# Persists the project checkout AND the Mathlib .lake build cache.
volume = modal.Volume.from_name("lean-mathlib-cache", create_if_missing=True)

# Common resource config for every Lean task. cpu=16 / 32 GiB for fast builds.
RESOURCES = dict(
    image=image,
    volumes={VOLUME_MOUNT: volume},
    cpu=16.0,
    memory=32768,
    timeout=7200,  # cache get + cold Mathlib build can take a while
)


# --------------------------------------------------------------------------- #
# Helpers (run inside the container)
# --------------------------------------------------------------------------- #
def _run(cmd, cwd=PROJECT_DIR, check=False):
    """Run a shell command, streaming combined output line-by-line.

    Streaming (rather than capturing) means the live Modal log shows progress
    in real time — essential for `lake build`, where a silent capture gives no
    clue whether lake is loading oleans, rebuilding Mathlib, or stuck.
    """
    import os

    print(f"$ {cmd}  (cwd={cwd})", flush=True)
    proc = subprocess.Popen(
        cmd,
        shell=True,
        cwd=cwd,
        env={**os.environ, **ENV},
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        bufsize=1,
    )
    lines = []
    for line in proc.stdout:
        lines.append(line)
        print(line, end="", flush=True)
    proc.wait()
    out = "".join(lines)
    if check and proc.returncode != 0:
        raise RuntimeError(f"command failed ({proc.returncode}): {cmd}\n{out}")
    return proc.returncode, out


def _is_cloned():
    import os

    return os.path.isdir(os.path.join(PROJECT_DIR, ".git"))


def _sync_repo():
    """Clone if needed, otherwise hard-reset to origin/main.

    A hard reset (rather than `git pull`) guarantees the committed
    `lean-toolchain` and `lake-manifest.json` are restored exactly — important
    because `lake update` rewrites both, and we must build against the pin the
    repo actually commits to. `.lake/` is gitignored, so the reset leaves the
    Mathlib build cache untouched.
    """
    if _is_cloned():
        print("Repo present — fetching + hard-reset to origin/main.", flush=True)
        _run("git fetch origin --quiet", check=False)
        _run("git reset --hard origin/main", check=False)
    else:
        print("Cloning repo into volume…", flush=True)
        _run(f"git clone {REPO_URL} {PROJECT_DIR}", cwd=VOLUME_MOUNT, check=True)


# --------------------------------------------------------------------------- #
# setup(): clone + (cache get) + first build, against the committed pin.
# --------------------------------------------------------------------------- #
@app.function(**RESOURCES)
def setup(fresh: bool = False, update: bool = False):
    """One-time environment setup.

    fresh  : wipe the volume's checkout and re-clone (use to recover a clean
             baseline, e.g. after a stray `lake update` drifted the toolchain).
    update : run `lake update` to re-resolve Mathlib from `master`. OFF by
             default — the repo pins Lean v4.30.0-rc2 and an exact Mathlib rev
             in lake-manifest.json, and `lake update` would bump both (it
             pulled in v4.31.0-rc1, which breaks the current proofs). Only pass
             --update when you deliberately want to move to newer Mathlib.
    """
    import os
    import shutil

    os.makedirs(VOLUME_MOUNT, exist_ok=True)

    if fresh and _is_cloned():
        print("fresh=True → removing existing checkout.", flush=True)
        shutil.rmtree(PROJECT_DIR, ignore_errors=True)

    _sync_repo()

    # Show exactly what Lean/Mathlib pin we're about to build against.
    _run("cat lean-toolchain", check=False)

    # Make sure elan has the pinned toolchain (no-op if already baked in).
    _run(f"elan toolchain install {LEAN_TOOLCHAIN}", check=False)

    if update:
        print("update=True → re-resolving Mathlib from master (lake update).", flush=True)
        _run("lake update", check=False)

    # Fetch the prebuilt Mathlib cache for the pinned rev. This is the
    # expensive, once-per-environment step that the volume saves us from.
    rc_cache, _ = _run("lake exe cache get", check=False)
    if rc_cache != 0:
        print("WARNING: `lake exe cache get` returned non-zero — see output above.", flush=True)

    # Initial build so subsequent `build()` calls are incremental.
    rc_build, out = _run("lake build", check=False)

    # Persist everything (repo + .lake build artifacts + xdg cache) to the volume.
    volume.commit()

    status = "OK" if rc_build == 0 else f"build returned {rc_build}"
    print(f"\n=== setup complete: {status} ===", flush=True)
    return {"build_returncode": rc_build, "tail": out[-4000:]}


# --------------------------------------------------------------------------- #
# build(): incremental `lake build`, returns errors/warnings.
# --------------------------------------------------------------------------- #
@app.function(**RESOURCES)
def build(reset: bool = True):
    """Incremental `lake build`.

    reset : when True (default), hard-reset the checkout to origin/main first
            (normal flow: build the latest pushed state). Pass --no-reset to
            build whatever is currently in the volume instead — e.g. after
            `modal volume put`-ing locally edited files you want to verify
            without pushing to GitHub.
    """
    if not _is_cloned():
        return {"error": "project not set up — run `modal run modal_lean.py::setup` first"}

    if reset:
        # Sync to the latest pushed state (hard reset; never fails on a dirty tree).
        _sync_repo()
    else:
        print("reset=False → building current volume state (local edits / uploads).",
              flush=True)

    # Always ensure the prebuilt Mathlib oleans are present/decompressed, so
    # `lake build` never decides to rebuild Mathlib from source (hours). Cheap
    # when already cached ("No files to download").
    _run("lake exe cache get", check=False)

    rc, out = _run("lake build", check=False)
    volume.commit()

    # Surface just the lines that matter.
    diagnostics = [
        line
        for line in out.splitlines()
        if any(k in line.lower() for k in ("error", "warning", "sorry"))
    ]
    result = {
        "returncode": rc,
        "ok": rc == 0,
        "diagnostics": diagnostics,
        "tail": out[-4000:],
    }
    print(f"\n=== build {'OK' if rc == 0 else 'FAILED'} | "
          f"{len(diagnostics)} diagnostic line(s) ===", flush=True)
    return result


# --------------------------------------------------------------------------- #
# check_sorry(): grep -n sorry across all .lean files.
# --------------------------------------------------------------------------- #
@app.function(**RESOURCES)
def check_sorry():
    if not _is_cloned():
        return {"error": "project not set up — run `modal run modal_lean.py::setup` first"}

    # Search project sources only (skip the .lake dependency tree).
    rc, out = _run(
        "grep -rn --include='*.lean' -e 'sorry' . "
        "| grep -v '/.lake/' || true",
        check=False,
    )
    hits = [line for line in out.splitlines() if line.strip()]
    print(f"\n=== {len(hits)} sorry occurrence(s) ===", flush=True)
    return {"count": len(hits), "occurrences": hits}


# --------------------------------------------------------------------------- #
# lean_check(code): write a scratch file, run `lake env lean` on it.
# --------------------------------------------------------------------------- #
@app.function(**RESOURCES)
def lean_check(code: str):
    import os

    if not _is_cloned():
        return {"error": "project not set up — run `modal run modal_lean.py::setup` first"}

    scratch = os.path.join(PROJECT_DIR, "_scratch_modal.lean")
    with open(scratch, "w", encoding="utf-8") as f:
        f.write(code)

    # `lake env lean` runs the file with the project's full import environment
    # (Mathlib + Topostability) available.
    rc, out = _run(f"lake env lean {scratch!r}", check=False)

    try:
        os.remove(scratch)
    except OSError:
        pass

    print(f"\n=== lean_check {'OK' if rc == 0 else 'has diagnostics'} ===", flush=True)
    return {"returncode": rc, "ok": rc == 0, "diagnostics": out}


# --------------------------------------------------------------------------- #
# check_file(path): run `lake env lean` on a file already on the volume.
# Use this to avoid CLI unicode mangling: `modal volume put` the UTF-8 file
# first, then run lean on it directly.
# --------------------------------------------------------------------------- #
@app.function(**RESOURCES)
def check_file(path: str = "_scratch_modal.lean"):
    import os

    if not _is_cloned():
        return {"error": "project not set up — run `modal run modal_lean.py::setup` first"}

    target = os.path.join(PROJECT_DIR, path)
    if not os.path.isfile(target):
        return {"error": f"file not found on volume: {target}"}

    rc, out = _run(f"lake env lean {target!r}", check=False)
    print(f"\n=== check_file {'OK' if rc == 0 else 'has diagnostics'} ===", flush=True)
    return {"returncode": rc, "ok": rc == 0, "diagnostics": out}


# --------------------------------------------------------------------------- #
# Local entrypoint so `modal run modal_lean.py` (no ::func) does something sane.
# --------------------------------------------------------------------------- #
@app.local_entrypoint()
def main():
    print(setup.remote())
