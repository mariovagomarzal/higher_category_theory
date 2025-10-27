[private]
default:
    @just --list --unsorted

lean_project := "HigherCategoryTheory"

[doc("Cache dependencies for the Lean project.")]
cache:
  lake exe cache get

[doc("Build the Lean project.")]
build TARGETS=lean_project:
  lake build {{TARGETS}}
