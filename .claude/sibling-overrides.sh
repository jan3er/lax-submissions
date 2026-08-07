#!/usr/bin/env bash
# Point this checkout's cross-submission dependencies at its own sibling
# folders, so `lake build` uses the working tree instead of the pinned commits.
# Pure local bookkeeping — no arguments, idempotent, safe to rerun:
#
#   .claude/sibling-overrides.sh
#
# Why it exists. The spec forbids a sibling `path` require across submissions:
# every cross-submission edge must be a `(git, rev, subDir)` triple equal to the
# dependency's current archive record, so a submission's commit transitively
# pins its whole source closure. Checked-in lakefiles therefore name commits,
# not siblings — but a commit is worthless while both submissions are still
# being written, and rebuilding a dependency's pinned clone from source is a
# pointless hour. Lake's package overrides close that gap: an entry in
# `<pkg>/.lake/package-overrides.json` replaces a manifest entry of the same
# name after manifest validation, so the pins stay honest in git while the
# build reads the folder next door. Both files are generated and gitignored
# (`lax build` rejects a checked-in overrides file outright).
#
# What it writes, per package, for the transitive closure of its
# cross-submission requires:
#   - lake-manifest.json           the locked `git` entry the lakefile declares
#     (from the archive record), so lake never reports the manifest out of date
#     and never suggests the forbidden `lake update`;
#   - .lake/package-overrides.json a `path` entry redirecting that same name to
#     the sibling folder, relative to the package — so the file survives being
#     copied into a worktree (see worktree-seed.sh).
# Existing entries are merged, not replaced: the warm-store redirects lax wrote
# for mathlib and friends stay exactly as they are.
#
# Rerun it after `lax build`, which rewrites both files from the pins alone —
# that is the honest, archive-faithful build, and it is what `lax submit` and
# the server do. This script is for the fast local loop only.
set -euo pipefail

python3 - "$(git rev-parse --show-toplevel)" <<'PY'
import json, os, re, sys

root = sys.argv[1]
# the CLI's own database clone: one `lax-N` folder per id, refreshed by
# `lax pull-db`. (An old CLI kept a second clone at ~/.lax/db with `LaxN`
# folders; it is not the archive lax validates against — do not read it.)
db = os.path.expanduser("~/.lax/lax-database")

# --- the packages of this checkout, and what each one requires --------------

def parse_lakefile(path):
    """Package name plus one dict per [[require]] block. The lakefiles are the
    whitelisted TOML the spec allows, so a line scanner is enough."""
    name, requires, cur = None, [], None
    for line in open(path):
        line = line.strip()
        if line == "[[require]]":
            cur = {}
            requires.append(cur)
            continue
        if line.startswith("["):
            cur = None
            continue
        m = re.match(r'^(\w+)\s*=\s*"([^"]*)"$', line)
        if not m:
            continue
        key, value = m.group(1), m.group(2)
        if cur is not None:
            cur[key] = value
        elif key == "name" and name is None:
            name = value
    return name, requires

packages = {}  # package name -> {dir, kind, requires}
for submission in sorted(os.listdir(root)):
    for kind in ("concepts", "proofs"):
        lakefile = os.path.join(root, submission, kind, "lakefile.toml")
        if not os.path.isfile(lakefile):
            continue
        name, requires = parse_lakefile(lakefile)
        packages[name] = {"dir": os.path.join(root, submission, kind),
                          "kind": kind, "requires": requires}

def record(package):
    """The archive record of the submission owning `package`, or None. Package
    LaxN / LaxNProofs belongs to submission lax-N (contracts.ts)."""
    base = package[:-len("Proofs")] if package.endswith("Proofs") else package
    number = re.match(r"^Lax([1-9][0-9]*)$", base)
    path = os.path.join(db, f"lax-{number.group(1)}", "record.json") if number else None
    if path is None or not os.path.isfile(path):
        return None
    return json.load(open(path))

def closure(package):
    """Every locally present package reachable through `package`'s requires,
    excluding itself — the set lake must find an entry for."""
    seen, stack = set(), [package]
    while stack:
        for require in packages[stack.pop()]["requires"]:
            dep = require["name"]
            if dep in packages and dep not in seen:
                seen.add(dep)
                stack.append(dep)
    seen.discard(package)
    return sorted(seen)

# --- rewrite the two generated files ---------------------------------------

def merge(path, key, entries):
    """Replace same-named entries under `key`, keeping everything else."""
    if not os.path.isfile(path):
        return False
    document = json.load(open(path))
    ours = {entry["name"] for entry in entries}
    kept = [entry for entry in document[key] if entry["name"] not in ours]
    document[key] = entries + kept
    open(path, "w").write(json.dumps(document, indent=1) + "\n")
    return True

problems, touched = [], 0
for name in sorted(packages):
    package = packages[name]
    deps = closure(name)
    if not deps:
        continue
    own_concepts = name[:-len("Proofs")] if package["kind"] == "proofs" else None
    declared = {r["name"]: r for r in package["requires"]}

    manifest_entries, override_entries = [], []
    for dep in deps:
        if dep == own_concepts:
            # the one path require the spec allows; nothing to redirect
            manifest_entries.append({
                "type": "path", "scope": "", "name": dep,
                "manifestFile": "lake-manifest.json", "inherited": False,
                "dir": "../concepts", "configFile": "lakefile.toml"})
            continue
        source = (record(dep) or {}).get("source")
        if source is None:
            problems.append(f"{name}: {dep} has no archive record — left as is")
            continue
        subdir = f"{source['folder']}/{packages[dep]['kind']}"
        pinned = declared.get(dep)
        if pinned and "git" in pinned and (
                pinned["git"] != source["repository"]
                or pinned["rev"] != source["commit"]
                or pinned.get("subDir") != subdir):
            problems.append(f"{name}: the {dep} require does not match the archive "
                            f"record ({source['repository']} {source['commit'][:12]} "
                            f"{subdir}) — `lax build` will reject it")
        manifest_entries.append({
            "url": source["repository"], "type": "git", "subDir": subdir,
            "scope": "", "rev": source["commit"], "name": dep,
            "manifestFile": "lake-manifest.json", "inputRev": source["commit"],
            "inherited": False, "configFile": "lakefile.toml"})
        override_entries.append({
            "type": "path", "name": dep, "inherited": False, "scope": "",
            "dir": os.path.relpath(packages[dep]["dir"], package["dir"])})

    if not override_entries:  # nothing of this checkout to reach for
        continue

    manifest = os.path.join(package["dir"], "lake-manifest.json")
    overrides = os.path.join(package["dir"], ".lake", "package-overrides.json")
    if not (os.path.isfile(manifest) and os.path.isfile(overrides)):
        problems.append(f"{name}: no generated manifest or overrides yet — run "
                        f"`lax build --only {package['kind']} <submission>` once, "
                        f"or seed the worktree, then rerun")
        continue
    merge(manifest, "packages", manifest_entries)
    merge(overrides, "packages", override_entries)
    touched += 1
    print(f"{name}: {', '.join(entry['name'] for entry in override_entries)}")

print(f"sibling-overrides: redirected {touched} package(s) to this checkout")
for problem in problems:
    print(f"warning: {problem}")
PY
