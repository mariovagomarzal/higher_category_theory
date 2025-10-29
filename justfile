[private]
default:
    @just --list --unsorted

lean_project := "HigherCategoryTheory"
get_lean_version := "$(cat lean-toolchain | cut -d':' -f2)"

[group("env")]
[doc("Cache dependencies for the Lean project.")]
cache:
  lake exe cache get

[doc("Build the Lean project.")]
build TARGETS=lean_project:
  lake build {{TARGETS}}

website_dir := "website/"
website_target := website_dir + "_site/"
docs_build_dir := "docbuild/"
docs_dir := docs_build_dir + ".lake/build/doc/"
docs_target := website_dir + "docs/"
blueprint_dir := "blueprint/"
blueprint_print_dir := blueprint_dir + "print/"
blueprint_print_file := blueprint_print_dir + "print.pdf"
blueprint_print_target := website_dir + "print.pdf"
blueprint_web_dir := blueprint_dir + "web/"
blueprint_web_target := website_dir + "blueprint/"

[group("docs")]
[doc("Build the documentation for the Lean project.")]
docs:
  #!/usr/bin/env bash
  set -euxo pipefail

  rm -rf {{docs_build_dir}}

  mkdir -p {{docs_build_dir}}
  cd {{docs_build_dir}}

  cp ../lean-toolchain .
  cat << EOF > lakefile.toml
  name = "docbuild"
  reservoir = false
  version = "0.1.0"
  packagesDir = "../.lake/packages"

  [[require]]
  name = "{{lean_project}}"
  path = "../"

  [[require]]
  name = "doc-gen4"
  scope = "leanprover"
  rev = "{{get_lean_version}}"
  EOF

  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update {{lean_project}}
  lake build {{lean_project}}:docs

  cd ..
  rm -rf {{docs_target}}
  cp -r {{docs_dir}} {{docs_target}}

[group("docs")]
[doc("Build the Blueprint PDF.")]
blueprint-print:
  rm -rf {{blueprint_print_dir}}
  leanblueprint pdf

  rm -f {{blueprint_print_target}}
  cp {{blueprint_print_file}} {{blueprint_print_target}}

[group("docs")]
[doc("Build the Blueprint website.")]
blueprint-web:
  rm -rf {{blueprint_web_dir}}
  leanblueprint web

  rm -rf {{blueprint_web_target}}
  cp -r {{blueprint_web_dir}} {{blueprint_web_target}}

[group("docs")]
[doc("Build the Blueprint (PDF and web).")]
blueprint: blueprint-print blueprint-web

[group("docs")]
[doc("Build the project website.")]
website JEKYLL_ENV="":
  rm -rf {{website_target}}
  cd {{website_dir}} && bundle install
  cd {{website_dir}} && JEKYLL_ENV={{JEKYLL_ENV}} bundle exec jekyll build -d ../{{website_target}}

[group("docs")]
[doc("Serve the project website locally.")]
serve:
  cd {{website_target}} && python -m http.server 8000
