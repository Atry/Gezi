{
  nixConfig = {
    extra-substituters = [
      "https://cache.nixos.org"
      "https://devenv.cachix.org"
      "https://nix-community.cachix.org"
      "https://install.determinate.systems"
      "https://cache.nixos-cuda.org"

    ];
    extra-trusted-substituters = [
      "https://cache.nixos.org"
      "https://devenv.cachix.org"
      "https://nix-community.cachix.org"
      "https://install.determinate.systems"
      "https://cache.nixos-cuda.org"
    ];
    extra-trusted-public-keys = [
      "cache.flakehub.com-3:hJuILl5sVK4iKm86JzgdXW12Y2Hwd5G07qKtHTOcDCM="
      "cache.nixos-cuda.org:74DUi4Ye579gUqzH4ziL9IyiJBlDpMRn9MBN8oNan9M="
      "devenv.cachix.org-1:w1cLUi8dv3hnoSPGAuibQv+f9TZLr6cv/Hm9XgU50cw="
      "nix-community.cachix.org-1:mB9FSh9qf2dCimDSUo8Zy7bkq5CX+/rkCWyvRCYg3Fs="
    ];
  };
  # Gezi's build artifacts, the same modules the monorepo imports in its
  # modules/artifacts.nix, so that `nix build .#<name>` from this directory and from the
  # monorepo's root build the same derivation (the monorepo's CONTRIBUTING.md,
  # "Development Environment and Builds"). There is no dev shell here: the monorepo's
  # dev shell is the one Gezi is developed in.
  #
  # The pins follow the monorepo's: flake.lock locks each input below to the revision
  # the monorepo locks it to (the root flake.lock for nixpkgs, flake-parts, systems and
  # sbt-derivation; dev/flake.lock for nix-ml-ops and what it brings), and the inputs
  # of nix-ml-ops are overridden here as dev/flake.nix overrides them. Relock this flake
  # whenever the monorepo's locks of these inputs move.
  inputs = {
    systems.url = "github:nix-systems/default";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts = {
      url = "github:hercules-ci/flake-parts";
      inputs.nixpkgs-lib.follows = "nixpkgs";
    };
    sbt-derivation = {
      url = "github:zaninime/sbt-derivation";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # The monorepo vendors nix-ml-ops at dev/nix-ml-ops, a subrepo of github:Atry/nix-ml-ops
    # last pushed as this commit (dev/nix-ml-ops/.gitrepo; the branch it names is gone
    # from the remote, and the commit is the head of its pull request 3), and devenv at
    # dev/devenv, a subrepo of github:Atry/devenv whose one local change (package.nix's
    # buildInputs on darwin) changes no derivation on Linux.
    nix-ml-ops = {
      url = "github:Atry/nix-ml-ops/8600de06cecf75b9b07bada0ef6116eea7629193";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        systems.follows = "systems";
        devenv.url = "github:Atry/devenv";
        devenv.inputs.nixpkgs.follows = "nixpkgs";
        devenv.inputs.nix.inputs.nixpkgs.follows = "nixpkgs";
        devenv.inputs.cachix.inputs.nixpkgs.follows = "nixpkgs";
      };
    };
    # Required by devenv's `containers`, which looks them up at the top level.
    nix2container.follows = "nix-ml-ops/nix2container";
    mk-shell-bin.follows = "nix-ml-ops/mk-shell-bin";
  };
  # `systems` is not set here: nix-ml-ops's jobs module, which
  # modules/gezi-jupyter-image.nix imports, sets it from the `systems` input.
  outputs = inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        ./modules/lean.nix
        ./modules/opentheory.nix
        ./modules/gezi-jupyter-image.nix
      ];
    };
}
