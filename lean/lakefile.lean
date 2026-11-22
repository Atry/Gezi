import Lake
open Lake DSL

-- No `require`: the design (D8) keeps this
-- package on Lean's core library only, without Mathlib.

package LambdaJit where
  -- Lake's local artifact cache: outputs are stored under their input hash in the user's
  -- cache directory, so a build in another git worktree of the same sources and toolchain
  -- reuses them instead of compiling cold. The dev shell sets LAKE_ARTIFACT_CACHE as well,
  -- for Lake packages that do not set this option.
  enableArtifactCache := true
  -- With the cache, Lake keeps a cached target's outputs in the cache and not in their usual place
  -- in the build directory, unless it restores them (Lake 5.0.0's PackageConfig docs). `lake env
  -- lean`, lean4export and the checkers read the build directory, so every artifact is restored
  -- (without it, a build reported success while `lake env lean` found no
  -- LambdaJit/Interpretation.olean).
  restoreAllArtifacts := true

@[default_target]
lean_lib LambdaJit where
