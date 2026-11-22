{ ... }: {
  # Build the Gezi Lean 4 package (gezi/lean) as a Nix artifact, mirroring
  # MIXINv2/modules/lean.nix (see there for the fuller comments). Surfaced via
  # modules/artifacts.nix. The package uses Lean's core library only (no Mathlib,
  # https://github.com/Atry/private-overlay/issues/1561 D8), so there are no `leanDeps`; the
  # source still ships an empty `lake-manifest.json` so that Lake resolves nothing.
  #
  # The toolchain is nixpkgs' `leanPackages.lean4` (4.35.0 at nixpkgs 1c89083e4, with
  # `lake`); lean/lean-toolchain names the same version.
  config.perSystem = { pkgs, ... }: {
    packages.lambda-jit-lean = pkgs.leanPackages.buildLakePackage {
      pname = "lambda-jit-lean";
      version = "0.1.0";
      src = ../lean;

      # Must match the package/lean_lib name declared in lean/lakefile.lean.
      leanPackageName = "LambdaJit";
    };
  };
}
