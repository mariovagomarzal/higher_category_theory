#!/usr/bin/env bash
#
# Build the API documentation for the Lean project using doc-gen4.
#
# This script creates a temporary docbuild project, patches known issues,
# builds documentation, and copies the output to the website directory.
#
# Usage: build_docs.sh <lean_project> <lean_version> <references> \
#                       <docs_build_dir> <docs_dir> <docs_target>

set -euo pipefail

# Arguments

if [[ $# -ne 6 ]]; then
  echo "Usage: $0 <lean_project> <lean_version> <references>" \
    "<docs_build_dir> <docs_dir> <docs_target>" >&2
  exit 1
fi

LEAN_PROJECT="$1"
LEAN_VERSION="$2"
REFERENCES="$3"
DOCS_BUILD_DIR="$4"
DOCS_DIR="$5"
DOCS_TARGET="$6"

# Workaround for lean4-unicode-basic#81
#
# On non-Windows platforms, Lake's `moreLinkObjs` doesn't correctly link the
# UnicodeCLib C static library into UnicodeBasic's dynlibs. The upstream fix
# (extern_lib) is Windows-only. We patch the lakefile to make it unconditional.
#
# See: https://github.com/fgdorais/lean4-unicode-basic/issues/81

UNICODE_BASIC_LAKEFILE=".lake/packages/UnicodeBasic/lakefile.lean"

apply_unicode_basic_patch() {
  if [[ ! -f "$UNICODE_BASIC_LAKEFILE" ]]; then
    echo "Warning: $UNICODE_BASIC_LAKEFILE not found, skipping patch." >&2
    return
  fi

  cp "$UNICODE_BASIC_LAKEFILE" "$UNICODE_BASIC_LAKEFILE.orig"
  sed -i.bak '/^meta if System.Platform.isWindows then$/d' "$UNICODE_BASIC_LAKEFILE"
  rm -f "$UNICODE_BASIC_LAKEFILE.bak"
  echo "Applied UnicodeBasic lakefile patch (lean4-unicode-basic#81)."
}

restore_unicode_basic_patch() {
  if [[ -f "$UNICODE_BASIC_LAKEFILE.orig" ]]; then
    mv "$UNICODE_BASIC_LAKEFILE.orig" "$UNICODE_BASIC_LAKEFILE"
    echo "Restored original UnicodeBasic lakefile."
  fi
}

# Main

echo "==> Preparing docbuild directory"
rm -rf "$DOCS_BUILD_DIR"
mkdir -p "$DOCS_BUILD_DIR"

cp lean-toolchain "$DOCS_BUILD_DIR/"

cat > "$DOCS_BUILD_DIR/lakefile.toml" <<EOF
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "$LEAN_PROJECT"
path = "../"

[[require]]
name = "doc-gen4"
scope = "leanprover"
rev = "$LEAN_VERSION"
EOF

mkdir -p "$DOCS_BUILD_DIR/docs"
cp "$REFERENCES" "$DOCS_BUILD_DIR/docs/"

echo "==> Updating Lake dependencies"
(cd "$DOCS_BUILD_DIR" && MATHLIB_NO_CACHE_ON_UPDATE=1 lake update "$LEAN_PROJECT")

echo "==> Applying patches"
apply_unicode_basic_patch
trap restore_unicode_basic_patch EXIT

echo "==> Building documentation"
(cd "$DOCS_BUILD_DIR" && lake build "$LEAN_PROJECT":docs)

echo "==> Copying documentation to $DOCS_TARGET"
rm -rf "$DOCS_TARGET"
cp -r "$DOCS_DIR" "$DOCS_TARGET"

echo "==> Done"
