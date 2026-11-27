#!/usr/bin/env python3
"""check-pins.py: fail when a dependency pin stated in two places disagrees.

Checks, for the repository containing this script:
  1. each `require <pkg> from git "<url>" @ "<rev>"` in lakefile.lean (and each [[require]]
     with `git`/`rev` in lakefile.toml) against lake-manifest.json: a 40-hex rev must equal
     the manifest's `rev`, any other rev (a branch or tag) its `inputRev`;
  2. each submodule's checked-out commit against its gitlink (`git submodule status` `+`);
  3. each foundry.lock entry against the submodule gitlink, and its tag (when the submodule
     has that tag locally) against the same commit.

--staged reads lakefile, manifest, foundry.lock and gitlinks from the index, as the
pre-commit hook (.githooks/pre-commit) needs. Silent and exit 0 when every pin agrees;
otherwise one line per disagreement and exit 1. Standard library only.

    python3 scripts/check-pins.py            # working tree and index
    python3 scripts/check-pins.py --staged   # what the next commit records
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

HEX40 = re.compile(r"^[0-9a-f]{40}$")
LEAN_REQUIRE = re.compile(
    r'^\s*require\s+[«"]?([\w.\-]+)[»"]?\s+from\s+git\s+"([^"]+)"\s*@\s*"([^"]+)"', re.M
)


def git(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", "-C", str(root), *args], check=True, capture_output=True, text=True
    ).stdout


def read(root: Path, path: str, staged: bool) -> str | None:
    """The file's text from the index (staged) or the working tree; None when absent."""
    if staged:
        r = subprocess.run(
            ["git", "-C", str(root), "show", f":{path}"], capture_output=True, text=True
        )
        return r.stdout if r.returncode == 0 else None
    p = root / path
    return p.read_text() if p.exists() else None


def lake_requires(root: Path, staged: bool) -> list[tuple[str, str, str, str]]:
    """(file, package, url, rev) for every git require with a rev."""
    out = []
    lean = read(root, "lakefile.lean", staged)
    if lean is not None:
        # Drop line comments so a commented-out require does not count.
        text = "\n".join(line.split("--", 1)[0] for line in lean.splitlines())
        out += [("lakefile.lean", n, u, r) for n, u, r in LEAN_REQUIRE.findall(text)]
    toml = read(root, "lakefile.toml", staged)
    if toml is not None:
        import tomllib

        for req in tomllib.loads(toml).get("require", []):
            if "git" in req and "rev" in req:
                out.append(("lakefile.toml", req["name"], req["git"], req["rev"]))
    return out


def check_lake(root: Path, staged: bool) -> list[str]:
    requires = lake_requires(root, staged)
    if not requires:
        return []
    manifest_text = read(root, "lake-manifest.json", staged)
    if manifest_text is None:
        return ["lake-manifest.json missing while the lakefile pins git requires"]
    packages = {p.get("name"): p for p in json.loads(manifest_text).get("packages", [])}
    problems = []
    for file, name, url, rev in requires:
        pkg = packages.get(name)
        if pkg is None:
            problems.append(f"{file}: {name} is not in lake-manifest.json")
            continue
        if pkg.get("url", "").removesuffix(".git") != url.removesuffix(".git"):
            problems.append(f"{file}: {name} url {url} but lake-manifest.json has {pkg.get('url')}")
        if HEX40.match(rev):
            if pkg.get("rev") != rev:
                problems.append(f"{file}: {name} @ {rev[:9]} but lake-manifest.json has {str(pkg.get('rev'))[:9]}")
        elif pkg.get("inputRev") != rev:
            problems.append(f"{file}: {name} @ {rev} but lake-manifest.json inputRev is {pkg.get('inputRev')}")
    return problems


def gitlinks(root: Path) -> dict[str, str]:
    """Submodule path -> commit recorded in the index."""
    links = {}
    for line in git(root, "ls-files", "-s").splitlines():
        meta, path = line.split("\t", 1)
        mode, sha = meta.split()[:2]
        if mode == "160000":
            links[path] = sha
    return links


def check_submodules(root: Path) -> list[str]:
    problems = []
    for line in git(root, "submodule", "status").splitlines():
        if line.startswith("+"):
            sha, path = line[1:].split()[:2]
            problems.append(f"{path}: checked out at {sha[:9]}, but the gitlink records another commit")
        elif line.startswith("U"):
            problems.append(f"{line[1:].split()[1]}: submodule has merge conflicts")
    return problems


def check_foundry_lock(root: Path, staged: bool, links: dict[str, str]) -> list[str]:
    text = read(root, "foundry.lock", staged)
    if text is None:
        return []
    problems = []
    for path, entry in json.loads(text).items():
        ref_kind = next((k for k in ("tag", "branch") if isinstance(entry.get(k), dict)), None)
        rev = entry[ref_kind]["rev"] if ref_kind else entry.get("rev")
        link = links.get(path)
        if link is None:
            problems.append(f"foundry.lock: {path} is not a submodule")
            continue
        if rev != link:
            label = f" ({ref_kind} {entry[ref_kind]['name']})" if ref_kind else ""
            problems.append(f"foundry.lock: {path} @ {str(rev)[:9]}{label} but the gitlink is {link[:9]}")
        if ref_kind == "tag" and (root / path / ".git").exists():
            r = subprocess.run(
                ["git", "-C", str(root / path), "rev-parse", "--verify", "-q",
                 f"refs/tags/{entry['tag']['name']}^{{commit}}"],
                capture_output=True, text=True,
            )
            if r.returncode == 0 and r.stdout.strip() != rev:
                problems.append(
                    f"foundry.lock: {path} tag {entry['tag']['name']} is {r.stdout.strip()[:9]}, not {str(rev)[:9]}"
                )
    return problems


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    ap.add_argument("--staged", action="store_true", help="check what the next commit records")
    args = ap.parse_args()
    root = Path(git(Path(__file__).resolve().parent, "rev-parse", "--show-toplevel").strip())
    links = gitlinks(root)
    problems = check_lake(root, args.staged) + check_submodules(root) + check_foundry_lock(root, args.staged, links)
    for p in problems:
        print(p)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
