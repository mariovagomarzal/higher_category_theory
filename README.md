# A Formalization of Higher-Order Categories in Lean 4

A formal verification project based on the work by Enric Cosme Llópez on
_Higher-order categories_.

## Overview

In many works on (Higher) Category Theory, in addition to the usual many-sorted
notions of n-categories and of ω-categories, the single-sorted versions of them
are also commonly used.

The aim of this project is to provide a formalization of the latter notions and
the proof of their equivalence in Lean 4.

> [!NOTE]
> For the moment, this is an active research project for a Mathematics degree
> final project. The project is in early stages and the following documentation
> is intended for self-reference only.

## Development

This section documents how to set up and work with the repository.

### Code editor

It is recommended to work with [Visual Studio Code][vscode]. We have included
a `.vscode` directory with recommended settings and extensions.

### Running tasks

Development tasks (building, documentation, etc.) are managed using
[Just][just], a command runner similar to `make`. To see all available recipes,
run:

```bash
just
```

This will display a list of available commands with their descriptions. You can
inspect the `justfile` in the root of the repository to see the detailed
implementation of each recipe.

### Nix setup

The development environment is configured with [Nix][nix] and
_[devenv][devenv]_, which automatically installs all required tools and
dependencies.

To enter the development shell, run:

```bash
devenv shell
```

> [!TIP]
> If using [direnv][direnv], you can automatically load the development
> environment by running `direnv allow` once in the root of the repository.

Once inside the shell, all tools will be available. Run `devenv info` to see
what's included.

### Manual setup

If not using Nix, you need to manually install the following tools:

- **Git**: Version control system.
- **Lean 4**: Theorem prover and toolchain (recommended: install via
  [elan][elan]).
- **Just**: Command runner for development tasks.

For building documentation, you'll also need:

- **Ruby** with Bundler: For Jekyll static site generation.
- **TeX Live**: For LaTeX/PDF generation (blueprint).
- **leanblueprint**: Tool for generating Lean blueprints.
- **Python**: For serving the documentation website locally.

After installing Lean, cache the upstream dependencies to avoid long
compilation times:

```bash
just cache
```

## Conventions

In this section, we document the workflow and conventions used in this
repository.

### Commit messages

This project follows the [Conventional Commits][conventional-commits]
specification for commit messages. The commit message format is as follows:

```text
<type>[optional scope]: <description>

[optional body]

[optional footer(s)]
```

Where `<type>` is one of the following: `feat`, `fix`, `docs`, `style`,
`refactor`, `test`, `chore`, `build`, `ci`, `perf`, `revert`.

> [!TIP]
> If working with the development environment defined with _devenv_, a git hook
> is automatically installed to check the commit messages before committing.

### Branching

There are no strict rules for branching in this repository.

## Authors

- [Enric Cosme Llópez][enric]
- [Raul Ruiz Mora][raul]
- [Mario Vago Marzal][mario]

## License

Copyright (c) 2025 Mario Vago Marzal. All rights reserved.

This project is licensed under the Apache License 2.0. See the
[LICENSE](LICENSE) file for details.

<!-- External links -->
[nix]: https://nixos.org/
[devenv]: https://devenv.sh/
[vscode]: https://code.visualstudio.com/
[direnv]: https://direnv.net/
[elan]: https://github.com/leanprover/elan
[just]: https://just.systems/
[conventional-commits]: https://www.conventionalcommits.org/en/v1.0.0/
[enric]: https://github.com/encosllo
[raul]: https://github.com/ruizmoraraul
[mario]: https://github.com/mariovagomarzal
