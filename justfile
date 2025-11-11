[private]
default:
    @just --list --unsorted

# Lean project variables
lean_project := "HigherCategoryTheory"
get_lean_version := "$(cat lean-toolchain | cut -d':' -f2)"

# Documentation variables
website_dir := "website/"
website_target := website_dir + "_site/"
references := "docs/references.bib"
docs_build_dir := "docbuild/"
docs_dir := docs_build_dir + ".lake/build/doc/"
docs_target := website_dir + "docs/"
blueprint_dir := "blueprint/"
blueprint_src := blueprint_dir + "src/"
blueprint_print_dir := blueprint_dir + "print/"
blueprint_print_file := blueprint_print_dir + "print.pdf"
blueprint_print_target := website_dir + "print.pdf"
blueprint_web_dir := blueprint_dir + "web/"
blueprint_web_target := website_dir + "blueprint/"

[group("env")]
[doc("Cache dependencies for the Lean project.")]
cache:
  lake exe cache get

[group("env")]
[doc("Install Ruby dependencies for the website.")]
bundler:
  cd {{website_dir}} && bundle install

[group("env")]
[doc("Run all the environment setup tasks. Intended for non-Nix environments.")]
env: cache bundler

[group("lean")]
[doc("Build the Lean project.")]
build TARGETS=lean_project:
  lake build {{TARGETS}}

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

  mkdir -p docs/
  cp ../{{references}} docs/

  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update {{lean_project}}
  lake build {{lean_project}}:docs

  cd ..
  rm -rf {{docs_target}}
  cp -r {{docs_dir}} {{docs_target}}

[private]
[group("docs")]
[doc("Copy the references file to the blueprint source directory.")]
blueprint-references:
  cp {{references}} {{blueprint_src}}

[private]
[group("docs")]
[doc("Build the blueprint PDF.")]
blueprint-print:
  rm -rf {{blueprint_print_dir}}
  leanblueprint pdf

  rm -f {{blueprint_print_target}}
  cp {{blueprint_print_file}} {{blueprint_print_target}}

[private]
[group("docs")]
[doc("Build the blueprint website.")]
blueprint-web:
  rm -rf {{blueprint_web_dir}}
  leanblueprint web

  rm -rf {{blueprint_web_target}}
  cp -r {{blueprint_web_dir}} {{blueprint_web_target}}

[group("docs")]
[doc("Build the project blueprint (PDF and web).")]
blueprint: blueprint-references blueprint-print blueprint-web

[group("docs")]
[doc("Build the project website.")]
website JEKYLL_ENV="":
  rm -rf {{website_target}}
  cd {{website_dir}} && JEKYLL_ENV={{JEKYLL_ENV}} bundle exec jekyll build -d ../{{website_target}}

[group("docs")]
[doc("Serve the project website locally.")]
serve:
  cd {{website_target}} && jekyll serve

[group("style")]
[doc("Format references files with bibtool.")]
format-references INPUT_FILES=references:
  @./scripts/bibtool_format.py {{INPUT_FILES}}

alias fr := format-references
