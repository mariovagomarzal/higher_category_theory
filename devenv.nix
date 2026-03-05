{
  pkgs,
  lib,
  config,
  ...
}: {
  env = {
    GREET = "Lean 4 Development Environment";
  };

  # Use 'elan' to (automatically) manage Lean toolchains.
  languages.lean4 = {
    enable = true;
    package = pkgs.elan;
  };

  languages.ruby = {
    enable = true;
    bundler.enable = true;
  };

  languages.texlive = {
    enable = true;
    base = pkgs.texliveMedium;
  };

  languages.python.enable = true;

  packages = with pkgs; [
    just
    git
    leanblueprint
  ];

  git-hooks = {
    hooks = {
      gitlint = {
        enable = true;
        description = "Run gitlint to check commit messages";
      };

      markdownlint = {
        enable = true;
        excludes = ["^website/"];
        description = "Run markdownlint to check Markdown files";
      };

      alejandra = {
        enable = true;
        description = "Run the Alejandra formatter on Nix files";
      };

      bibtool = {
        enable = true;
        name = "bibtool";
        description = "Format BibTeX files using bibtool";
        # Override bibtool to fix compilation with newer GCC versions (>= 14) that treat
        # old-style (K&R) function definitions as errors by default.
        package = pkgs.bibtool.overrideAttrs (prev: {
          env =
            (prev.env or {})
            // {
              # Use the gnu89 C standard to restore legacy behavior for old-style
              # function definitions and implicit declarations.
              NIX_CFLAGS_COMPILE =
                (prev.env.NIX_CFLAGS_COMPILE or "")
                + " -std=gnu89";
            };
        });
        entry = "./scripts/bibtool_format.py";
        files = "\\.bib$";
        pass_filenames = true;
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

  tasks = {
    "env:cache" = {
      exec = "just cache";
      after = ["devenv:enterShell"];
      cwd = ".";
      description = "Run the 'cache' Just recipe";
    };

    "env:bundler" = {
      exec = "just bundler";
      after = ["devenv:enterShell"];
      cwd = ".";
      description = "Run the 'bundler' Just recipe";
    };
  };
}
