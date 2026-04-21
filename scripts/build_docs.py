#!/usr/bin/env python3
#
# Build the API documentation for the Lean project using doc-gen4.
#
# This script creates a temporary docbuild project, patches known issues,
# builds documentation, and copies the output to the website directory.
#
# Usage: build_docs.py <lean_project> <lean_version> <references>
#                      <docs_build_dir> <docs_dir> <docs_target>

import shutil
import subprocess
import sys
from pathlib import Path


UNICODE_BASIC_LAKEFILE = Path(".lake/packages/UnicodeBasic/lakefile.lean")


# Workaround for lean4-unicode-basic#81
#
# On non-Windows platforms, Lake's `moreLinkObjs` doesn't correctly link the
# UnicodeCLib C static library into UnicodeBasic's dynlibs. The upstream fix
# (extern_lib) is Windows-only. We patch the lakefile to make it unconditional.
#
# See: https://github.com/fgdorais/lean4-unicode-basic/issues/81

def apply_unicode_basic_patch():
    if not UNICODE_BASIC_LAKEFILE.exists():
        print(
            f"Warning: {UNICODE_BASIC_LAKEFILE} not found, skipping patch.",
            file=sys.stderr,
        )
        return

    orig = UNICODE_BASIC_LAKEFILE.with_suffix(".lean.orig")
    shutil.copy2(UNICODE_BASIC_LAKEFILE, orig)

    lines = UNICODE_BASIC_LAKEFILE.read_text().splitlines(keepends=True)
    lines = [l for l in lines if "meta if System.Platform.isWindows then" not in l]
    UNICODE_BASIC_LAKEFILE.write_text("".join(lines))

    print("Applied UnicodeBasic lakefile patch (lean4-unicode-basic#81).")


def restore_unicode_basic_patch():
    orig = UNICODE_BASIC_LAKEFILE.with_suffix(".lean.orig")
    if orig.exists():
        shutil.move(str(orig), str(UNICODE_BASIC_LAKEFILE))
        print("Restored original UnicodeBasic lakefile.")


def run(cmd, **kwargs):
    print(f"  $ {' '.join(cmd)}")
    subprocess.run(cmd, check=True, **kwargs)


def main():
    if len(sys.argv) != 7:
        print(
            f"Usage: {sys.argv[0]} <lean_project> <lean_version> <references>"
            " <docs_build_dir> <docs_dir> <docs_target>",
            file=sys.stderr,
        )
        sys.exit(1)

    lean_project = sys.argv[1]
    lean_version = sys.argv[2]
    references = Path(sys.argv[3])
    docs_build_dir = Path(sys.argv[4])
    docs_dir = Path(sys.argv[5])
    docs_target = Path(sys.argv[6])

    # Prepare docbuild directory
    print("==> Preparing docbuild directory")
    if docs_build_dir.exists():
        shutil.rmtree(docs_build_dir)
    docs_build_dir.mkdir(parents=True)

    shutil.copy2("lean-toolchain", docs_build_dir / "lean-toolchain")

    lakefile_content = f"""\
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "{lean_project}"
path = "../"

[[require]]
name = "doc-gen4"
scope = "leanprover"
rev = "{lean_version}"
"""
    (docs_build_dir / "lakefile.toml").write_text(lakefile_content)

    docs_subdir = docs_build_dir / "docs"
    docs_subdir.mkdir(parents=True, exist_ok=True)
    shutil.copy2(references, docs_subdir / references.name)

    # Update Lake dependencies
    print("==> Updating Lake dependencies")
    run(
        ["lake", "update", lean_project],
        cwd=docs_build_dir,
        env={**__import__("os").environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"},
    )

    # Apply patches and build
    print("==> Applying patches")
    apply_unicode_basic_patch()
    try:
        print("==> Building documentation")
        run(["lake", "build", f"{lean_project}:docs"], cwd=docs_build_dir)
    finally:
        restore_unicode_basic_patch()

    # Copy output
    print(f"==> Copying documentation to {docs_target}")
    if docs_target.exists():
        shutil.rmtree(docs_target)
    shutil.copytree(docs_dir, docs_target)

    print("==> Done")


if __name__ == "__main__":
    main()
