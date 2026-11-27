{ ... }: {
  # The two tools of a round certificate's check (https://github.com/Atry/private-overlay/issues/1528,
  # route B): lean4export, which writes the closure of the Lean library's constants a certificate
  # names in Lean's export format, and nanoda, an independent type checker of that format, which
  # checks the closure followed by the certificate (`com.yang_bo.gezi.proofs.RoundCertificates`). They are
  # in the certificate's trusted base with the scripts that call them. Surfaced via
  # modules/artifacts.nix as `nix build .#lean4export -L` and `nix build .#nanoda -L`, and put on
  # the dev shell's PATH by modules/lean-devshell.nix.
  #
  # The versions are the ones the prototype of 2026-11-09 measured (#1528, section 3): lean4export
  # at 5a9a355 (its tag v4.35.0, the version of the Lean the package builds with, nixpkgs'
  # `leanPackages.lean4`), whose export format is version 3.1.0, and nanoda_lib at 0da9f98 (0.4.32).
  config.perSystem = { pkgs, ... }: {
    packages.lean4export = pkgs.stdenv.mkDerivation {
      pname = "lean4export";
      version = "4.35.0";

      src = pkgs.fetchFromGitHub {
        owner = "leanprover";
        repo = "lean4export";
        rev = "5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe";
        hash = "sha256-LysjGOikBaaOdZdwxA+RwzfnQweTaU3kpFuWc6LxmXc=";
      };

      nativeBuildInputs = [ pkgs.leanPackages.lean4 ];

      # The package has no dependency (its lake-manifest.json lists none), so Lake fetches nothing.
      buildPhase = ''
        runHook preBuild
        export HOME=$TMPDIR
        lake build lean4export
        runHook postBuild
      '';

      installPhase = ''
        runHook preInstall
        install -D .lake/build/bin/lean4export $out/bin/lean4export
        runHook postInstall
      '';
    };

    packages.nanoda = pkgs.rustPlatform.buildRustPackage {
      pname = "nanoda";
      version = "0.4.32";

      src = pkgs.fetchFromGitHub {
        owner = "ammkrn";
        repo = "nanoda_lib";
        rev = "0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929";
        hash = "sha256-Gr7KkmIwOJHBsQ9s+fU5lnZAOeDHxnyxsOGYKjuwHDs=";
      };

      cargoHash = "sha256-op1SXq5u99nUPwX6PLoE8ovvLeTrvY4AgtGH70lsMI0=";
    };
  };
}
