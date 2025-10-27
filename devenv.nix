{
  pkgs,
  config,
  ...
}: {
  env = {
    GREET = "Lean 4 Development Environment";
    DOCS_SERVER_PORT = "8000";
  };

  packages = with pkgs; [
    git
  ];

  languages.lean4.enable = true;
  languages.python.enable = true;

  git-hooks = {
    hooks = {
      gitlint = {
        enable = true;
        description = "Run gitlint to check commit messages";
      };

      markdownlint = {
        enable = true;
        description = "Run markdownlint to check Markdown files";
      };

      alejandra = {
        enable = true;
        description = "Run the Alejandra formatter on Nix files";
      };
    };
  };

  files = {
    ".gitlint".ini = {
      general = {
        contrib = "contrib-title-conventional-commits";
        ignore = "body-is-missing";
      };

      title-max-length.line-length = 120;
      body-max-line-length.line-length = 120;
    };
  };

  enterShell = ''
    echo $GREET
  '';

  scripts = {
    "build" = {
      exec = ''
        lake build HigherCategoryTheory $@
      '';
      description = "Build the Lean project using Lake";
    };

    "update" = {
      exec = ''
        lake update $1
        cd docbuild || exit 1
        lake update HigherCategoryTheory
        cd ..
      '';
      description = "Update dependencies for the Lean project";
    };

    "docs" = {
      exec = ''
        cd docbuild || exit 1
        DOCGEN_SRC="github" lake build HigherCategoryTheory:docs $@
        cd ..
      '';
      description = "Build the documentation for the Lean project";
    };

    "update-docs" = {
      exec = ''
        cd docbuild || exit 1
        MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
        cd ..
      '';
    };
  };

  tasks = {
    "lean:cache" = {
      exec = "lake exe cache get";
      after = ["devenv:enterShell"];
      cwd = ".";
      description = ''
        Cache upstream Lean dependencies to save time compiling Mathlib and
        other dependencies
      '';
    };
  };

  processes = {
    "docs-server" = {
      exec = ''
        python -m http.server $DOCS_SERVER_PORT
      '';
      cwd = "docbuild/.lake/build/doc";
    };
  };
}
