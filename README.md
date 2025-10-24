# A Formalization of ∞-Categories in Lean 4

A formal verification project based on the work by Enric Cosme Llópez on
_Higher-order categories_.

## Overview

In many works on Category Theory, in addition to the usual many-sorted notions
of n-categories and of ∞-categories, the single-sorted versions of them are
also commonly used.

The aim of this project is to provide a formalization of the latter notions and
the proof of their equivalence in Lean 4.

> [!NOTE]
> For the moment, this is an active research project for a Mathematics degree
> final project. The project is in early stages and the following documentation
> is intended for self-reference only.

## Development

In this section, we document how to work with the repository. The development
environment is mainly managed with [Nix][nix] and _[devenv][devenv]_. However,
it is also documented how to work without the latter.

It is recommended to work with [Visual Studio Code][vscode]. We have also
included a `.vscode` directory with recommended settings and extensions for
working with the repository.

### Nix setup

To set up the development environment with Nix, you need to have Nix and
_devenv_ installed. Once you have them, you can enter the development shell
by running the following command in the root of the repository:

```bash
devenv shell
```

> [!TIP]
> If using [direnv][direnv], you can automatically load the development
> environment whenever you enter the repository directory by running
> `direnv allow` once in the root of the repository.

Once inside the development shell, all the necessary tools and dependencies
will be available. Run the following command to see available packages, scripts,
tasks and processes:

```bash
devenv info
```

Check out the `devenv.nix` file for more details on the development environment.

### Manual setup

This section provides manual setup instructions for working with the repository
without _devenv_. It documents the same dependencies and tasks configured in
`devenv.nix`.

The following tools are required to work with the repository:

- **Git**: The version control system.
- **Lean 4**: The Lean theorem prover and its toolchain (including Lake, the
  Lean build tool). If installing Lean manually, it is recommended to use
  [elan][elan] to manage Lean installations.
- **Python**: For running the documentation server.

After installing the Lean dependencies, cache the upstream Lean dependencies to
save time compiling Mathlib and other dependencies:

```bash
lake exe cache get
```

#### Common tasks

- For building the project, run:

  ```bash
  lake build InfinityCategories
  ```

- When updating Lean dependencies, it is also important to update the
  dependencie that points to the current project in the `docbuild` directory. To
  do so, run:

  ```bash
  lake update # or `lake update <dependency>` for a specific dependency

  # Update the dependency pointing to this project
  cd docbuild
  lake update InfinityCategories
  ```

- To build the documentation, run:

  ```bash
  cd docbuild
  DOCGEN_SRC="github" lake build InfinityCategories:docs
  ```

- For updating the documentation generation tool you have to update the
  `doc-gen4` dependency in the `docbuild` directory. To do so, run:

  ```bash
  cd docbuild
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
  ```

- For serving the documentation locally, run:

  ```bash
  cd docbuild/.lake/build/doc # make sure to build the docs first
  python -m http.server 8000 # or any other port
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
[conventional-commits]: https://www.conventionalcommits.org/en/v1.0.0/
[enric]: https://github.com/encosllo
[raul]: https://github.com/ruizmoraraul
[mario]: https://github.com/mariovagomarzal
