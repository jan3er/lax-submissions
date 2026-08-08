#!/usr/bin/env bash
# Seed submissions' own `.lake/build` from the archive's published capture
# artifacts, so a checkout that has never compiled anything still starts warm.
# On demand, never automatic:
#
#   .claude/capture-seed.sh                     every submission with a capture
#   .claude/capture-seed.sh word-ram lax-11     only these (folder or id)
#
# What a capture is. Every `lax submit` that builds leaves a sealed tar of the
# submission's compiled output — per package, the `.olean`/`.ilean`/`.trace`
# companions and the C artifacts under `ir` — pushed to ghcr as an OCI blob
# addressed by its own sha256. The archive record names it:
# `<record>/build-output.json` carries `capture.registryBlob`, its digest, the
# `sourceCommit` it was built from, and a per-file sha256 inventory. The
# trusted validation path materializes these as read-only path dependencies
# when one submission requires another; this script installs the *same* bytes
# into the *same* layout the local build uses, for our own submissions.
#
# Why it works. The capture is exactly what lake reads to decide a module is up
# to date: seal.ts captures the trace and hash companions precisely because the
# olean alone is not enough. Verified 2026-08-08 on finite-ramsey, whose tree is
# byte-identical to its capture's sourceCommit: wiped both packages' build
# directories, installed the capture, and `lake build` compiled 0 of the 11
# modules it had just compiled from scratch.
#
# What it is worth, measured the same day on word-ram, the largest submission
# whose tree still matches its capture (165 MB, 148 proof modules):
#
#     cold `lake build`     stopped at 121/148 modules after 30 minutes
#     capture-seeded        6 s to seed, 3 s to build, 0 modules compiled
#
# Drift is expected to be safe, not fatal: when our tree has moved past the
# capture's sourceCommit, lake's content-hash traces should rebuild whatever
# actually differs and replay the rest — the same bargain worktree-seed.sh
# makes when it copies a possibly-stale `.lake/build` from main. Treat that as
# reasoning from lake's model, not as a measurement: what was measured is the
# identical case, plus one drifted submission whose *concept* package had not
# changed and replayed all 12 of its modules. Partial reuse inside a package
# whose sources moved has not been timed. This script reports the drift per
# submission, so a build that recompiles more than you expected is at least
# never a surprise.
#
# It never overwrites work. A package that already has a `.lake/build` is left
# alone; seeding is for cold packages only. Pass --force to override.
#
# Anonymous pull: ghcr's token endpoint issues a pull token for a public
# package with no credential, so this needs no GitHub login (measured: the
# 1.5 MB finite-ramsey capture in 0.75 s). Every blob is verified against the
# digest the archive record names before a single file is extracted.
set -euo pipefail

root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
force=""
targets=()
for arg in "$@"; do
  case "$arg" in
    --force) force=1 ;;
    -h|--help) awk 'NR>1 && /^#/ {print; next} NR>1 {exit}' "${BASH_SOURCE[0]}"; exit 0 ;;
    *) targets+=("$arg") ;;
  esac
done

REPO_ROOT="$root" FORCE="$force" TARGETS="${targets[*]-}" python3 - <<'PY'
import hashlib, json, os, subprocess, sys, tarfile, tempfile, urllib.request

root = os.environ["REPO_ROOT"]
force = os.environ["FORCE"] != ""
targets = set(os.environ["TARGETS"].split())
db = os.path.expanduser("~/.lax/lax-database")
REGISTRY = "https://ghcr.io"

if not os.path.isdir(db):
    sys.exit(f"no archive database at {db}; run `lax pull-db` first")


def get(url, headers, limit=2 * 1024**3):
    request = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(request, timeout=120) as response:
        return response.read(limit)


def pull_token(repository):
    """ghcr issues a pull token for a public package without a credential."""
    scope = f"repository:{repository}:pull"
    body = get(f"{REGISTRY}/token?service=ghcr.io&scope={scope}", {})
    return json.loads(body)["token"]


def candidates():
    """Every submission of this checkout that the archive has a capture for."""
    for entry in sorted(os.listdir(db)):
        record = os.path.join(db, entry, "record.json")
        output = os.path.join(db, entry, "build-output.json")
        if not (os.path.isfile(record) and os.path.isfile(output)):
            continue
        source = (json.load(open(record)).get("source") or {})
        folder = source.get("folder")
        # `.` is a whole-repository record from an older layout, not one of ours
        if not folder or folder == "." or not os.path.isdir(os.path.join(root, folder)):
            continue
        if "lax-submissions" not in source.get("repository", ""):
            continue
        capture = (json.load(open(output)) or {}).get("capture")
        if capture is None:
            continue
        if targets and entry not in targets and folder not in targets:
            continue
        yield entry, folder, capture


def freshness(commit, folder):
    """How our tree relates to the commit the capture was built at. An unknown
    commit is not drift: a shallow or partial clone simply cannot answer, and
    the capture is still worth installing."""
    done = subprocess.run(["git", "-C", root, "diff", "--quiet", commit, "HEAD", "--", folder],
                          capture_output=True)
    if done.returncode == 0:
        return "identical"
    if done.returncode == 1:
        return "DRIFTED — partial reuse"
    return "commit not in this clone — reuse unknown"


def install(capture_dir, package_dir):
    """Lay the capture out where lake looks: lib/ becomes the package's
    `.lake/build/lib/lean`, ir/ its `.lake/build/ir`.

    The trusted container path additionally seals what it installs read-only
    and stamps the mtimes, because there a capture is another submission's
    immutable dependency. This is a working checkout, so neither is done here:
    the extracted files land at 0644, which is no stricter than the 0444 lake
    writes for its own outputs, and the epoch mtimes the capture carries are
    the ones lake itself produces."""
    build = os.path.join(package_dir, ".lake", "build")
    for section, destination in (("lib", os.path.join(build, "lib", "lean")),
                                 ("ir", os.path.join(build, "ir"))):
        source = os.path.join(capture_dir, section)
        if not os.path.isdir(source):
            continue
        os.makedirs(destination, exist_ok=True)
        subprocess.run(["cp", "-a", f"{source}/.", destination], check=True)


seeded = skipped = 0
for entry, folder, capture in candidates():
    blob = capture["registryBlob"]                       # ghcr.io/<repo>@sha256:<digest>
    repository = blob.split("/", 1)[1].split("@")[0]
    digest = capture["digest"]
    megabytes = sum(f["bytes"] for f in capture["files"]) / 1e6

    cold = [k for k in ("concepts", "proofs")
            if os.path.isdir(os.path.join(root, folder, k))
            and (force or not os.path.isdir(os.path.join(root, folder, k, ".lake", "build")))]
    if not cold:
        print(f"  {folder}: already built, left alone")
        skipped += 1
        continue

    state = freshness(capture["sourceCommit"], folder)
    print(f"  {folder} ({entry}): {megabytes:.1f} MB, {capture['sourceCommit'][:12]} {state}")

    body = get(f"{REGISTRY}/v2/{repository}/blobs/sha256:{digest}",
               {"Authorization": f"Bearer {pull_token(repository)}"})
    actual = hashlib.sha256(body).hexdigest()
    if actual != digest:
        print(f"    REFUSED: blob is {actual[:12]}, the record names {digest[:12]}")
        continue

    with tempfile.TemporaryDirectory() as work:
        archive = os.path.join(work, "capture.tar")
        with open(archive, "wb") as handle:
            handle.write(body)
        with tarfile.open(archive) as tar:
            # the capture is digest-verified above, but keep extraction inside
            # the temporary directory regardless
            destination = os.path.join(work, "capture")
            try:
                tar.extractall(destination, filter="data")
            except TypeError:  # the filter argument predates this Python
                tar.extractall(destination)
        for kind in cold:
            section = os.path.join(work, "capture", kind)
            if not os.path.isdir(section):
                continue
            install(section, os.path.join(root, folder, kind))
            print(f"    {kind}: installed")
    seeded += 1

print(f"capture-seed: seeded {seeded} submission(s), left {skipped} built one(s) alone")
PY
