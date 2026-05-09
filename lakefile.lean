import Lake
open Lake DSL

package «lean-black» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «LeanBlack» where
  srcDir := "."

lean_exe «smoke» where
  root := `Smoke
