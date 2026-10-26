#!/usr/bin/env python3
"""Verify the published release bytes; optionally build and audit Lean."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import os
import subprocess
import sys

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def verify(root):
    manifest = json.loads((root / "MANIFEST.json").read_text(encoding="utf-8"))
    listed = {}
    for item in manifest["files"]:
        relative = item["path"]
        path = PurePosixPath(relative)
        if path.is_absolute() or ".." in path.parts or "\\" in relative or ":" in relative:
            raise ValueError(f"Unsafe manifest path: {relative}")
        if relative in listed:
            raise ValueError(f"Duplicate manifest path: {relative}")
        target = root / relative
        target.resolve().relative_to(root)
        if any(parent.is_symlink() for parent in target.parents if parent != root and root in parent.parents):
            raise ValueError(f"Manifest path traverses a symbolic link: {relative}")
        if not target.is_file() or target.is_symlink():
            raise ValueError(f"Missing or non-regular file: {relative}")
        if target.stat().st_size != item["bytes"] or digest(target) != item["sha256"]:
            raise ValueError(f"File differs from the verified release: {relative}")
        listed[relative] = item["sha256"]
    checksums = {}
    for line in (root / "SOURCE_MANIFEST.sha256").read_text(encoding="utf-8").splitlines():
        expected, relative = line.split("  ", 1)
        if relative in checksums:
            raise ValueError(f"Duplicate checksum path: {relative}")
        checksums[relative] = expected
    expected_checksums = {**listed, "MANIFEST.json": digest(root / "MANIFEST.json")}
    if checksums != expected_checksums:
        raise ValueError("The JSON and SHA-256 manifests disagree.")
    # Local dependency/build output and Git metadata may appear after extraction.
    ignored_roots = {".lake", ".git", "__pycache__"}
    ignored_tex_suffixes = {".aux", ".log", ".out", ".toc", ".fls", ".fdb_latexmk"}
    actual = set()
    for directory, directories, filenames in os.walk(root):
        directories[:] = [name for name in directories if name not in ignored_roots]
        for filename in filenames:
            path = Path(directory) / filename
            relative = path.relative_to(root)
            if relative.parts[0] == "paper" and (path.suffix in ignored_tex_suffixes or path.name.endswith('.synctex.gz')):
                continue
            actual.add(relative.as_posix())
    expected_files = set(expected_checksums) | {"SOURCE_MANIFEST.sha256"}
    if actual != expected_files:
        raise ValueError(f"Unexpected/missing release files: {sorted(actual ^ expected_files)}")
    print(f"Verified {len(actual)} release files, all sizes and SHA-256 hashes.")

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="also build Lean and run both acceptance suites")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent.parent
    verify(root)
    if args.build:
        for command in (["lake", "build", "WeightedPilz"],
                        ["lake", "env", "lean", "WeightedPilzFinalChecks.lean"],
                        ["lake", "env", "lean", "WeightedPilzChecks.lean"]):
            subprocess.run(command, cwd=root, check=True)
        print("Lean build and both acceptance suites passed.")

if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"Verification failed: {error}", file=sys.stderr)
        sys.exit(1)
