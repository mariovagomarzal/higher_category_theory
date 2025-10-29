{
  pkgs,
  config,
  ...
}: {
  env = {
    GREET = "Lean 4 Development Environment";
  };

  languages.lean4.enable = true;

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
  };
}
