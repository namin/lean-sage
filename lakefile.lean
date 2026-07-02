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

lean_exe «demos» where
  root := `Demos

lean_exe «demo» where
  root := `Demo

lean_exe «proofBasedSmoke» where
  root := `ProofBasedSmoke

lean_exe «demoGuarded» where
  root := `DemoGuarded

lean_exe «booth» where
  root := `Booth
