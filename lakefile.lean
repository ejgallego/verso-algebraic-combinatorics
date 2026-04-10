import Lake
open Lake DSL

require algcomb from "algebraic-combinatorics"
require VersoBlueprint from git "https://github.com/ejgallego/verso-blueprint.git" @ "v4.28.0"

package AlgebraicCombinatoricsBlueprint where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`verso.blueprint.math.lint, true⟩,
    ⟨`verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`verso.code.warnLineLength, .ofNat 0⟩
  ]

@[default_target]
lean_lib AlgebraicCombinatoricsBlueprint where

lean_exe «blueprint-gen» where
  root := `BlueprintMain
  supportInterpreter := true
