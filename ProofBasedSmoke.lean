/-
  Smoke tests for proof-bearing admission (`proof-based` branch).

  Demonstrates the integration of `approvedPolicy` with the tower
  runtime. The key claim is that `approvedPolicy : BlackPolicy` —
  it slots into `PolicyTable`, gets installed at a level via
  `(installPolicy n)`, and gates `(set! ...)` during evaluation
  exactly like any other `BlackPolicy`. The novelty is in *how*
  the policy was constructed: from a list of `ApprovedModification`s,
  each carrying a Lean term of type `CE_weak_strong`.

  Two scenes:

  1. **Approved identity mod admitted.** Install
     `approvedPolicy [identityApproval 1 [] .builtinBaseApply]` at
     level 1, then run `(em (set! base-apply base-apply))` — an
     identity modification (RHS evaluates to the current value,
     which is `.builtinBaseApply`). The gate consults the approval
     list, the match succeeds, the `.set` returns `.bool true`.
     A subsequent `(+ 1 2)` still returns `3` because the
     modification was identity.

  2. **Non-matching mod refused.** Same setup, but the mutation is
     `(em (set! base-apply (lam (op args) 42)))` — a constant-42
     wrapper. The approval list has only the identity approval; the
     `newVal` mismatch means no approval matches; the gate refuses;
     `.set` returns `.bool false`. The heap is *not* updated, so
     `(+ 1 2)` still returns `3`.

  Run with `lake build proofBasedSmoke && lake exe proofBasedSmoke`.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.ProofBased

open LeanBlack

def fuel : Nat := 10000

/-! ## Approvals + policy table

    One approval: the identity modification on `.builtinBaseApply`
    at level 1, with the admission heap `[]` (trivially a prefix
    of anything). The `proof` field is `CE_weak_to_strong`-widened
    from `CE_weak_refl`.

    Policy table entry index 0 is `approvedPolicy [identity]`;
    `(installPolicy 0)` installs it. -/

def identityApprovals : List ApprovedModification :=
  [identityApproval 1 [] .builtinBaseApply]

def proofBasedTable : PolicyTable :=
  [approvedPolicy identityApprovals]

/-- `(em (installPolicy 0))` at level 0 installs `proofBasedTable[0]`
    at level 1. From level 1's perspective, future `.set` ops will
    consult `approvedPolicy identityApprovals`. -/
def installApprovedAt1 : Expr := .em (.installPolicy 0)

/-! ## Scene 1: admit (identity mod)

    `(em (set! base-apply base-apply))` at level 0:
      - Shift to level 1.
      - At level 1, evaluate `.set "base-apply" (.var "base-apply")`.
      - RHS lookup: `.var "base-apply"` resolves to the current
        cell value `.builtinBaseApply`.
      - `.set` gates: `approvedPolicy identityApprovals ctx
        .builtinBaseApply .builtinBaseApply`. The approval's
        `(level=1, heap=[], oldVal=.builtinBaseApply,
        newVal=.builtinBaseApply)` matches. Gate returns `true`.
      - `.set` returns `.bool true`. Heap cell updated (to the same
        value).

    After: `(+ 1 2)` still returns `3` (identity mod preserves
    arithmetic). -/

def identityModExpr : Expr := .em (.set "base-apply" (.var "base-apply"))

def test_identity_admitted : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, identityModExpr]

def test_identity_preserves_plus : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, identityModExpr,
          .app [.var "+", .num 1, .num 2]]

/-! ## Scene 2: refuse (non-matching mod)

    `(em (set! base-apply (lam (op args) 42)))`:
      - At level 1, evaluate `.set "base-apply" (lam ["op","args"] 42)`.
      - RHS evaluates to a closure value (constant-42).
      - `.set` gates: `approvedPolicy identityApprovals ctx
        .builtinBaseApply <closure>`. No approval matches (newVal
        differs from `.builtinBaseApply`). Gate returns `false`.
      - `.set` returns `.bool false`. Heap *not* updated.

    After: `(+ 1 2)` still returns `3` (no modification in effect). -/

def badModExpr : Expr :=
  .em (.set "base-apply" (.lam ["op", "args"] (.num 42)))

def test_badmod_refused : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, badModExpr]

def test_badmod_preserves_plus : Option Val :=
  evalProgram fuel proofBasedTable <|
    .seq [installApprovedAt1, badModExpr,
          .app [.var "+", .num 1, .num 2]]

/-! ## Runner -/

def shortRepr : Option Val → String
  | none            => "<none>"
  | some (.num n)   => s!"num({n})"
  | some (.bool b)  => s!"bool({b})"
  | some .nilV      => "nilV"
  | some (.cons _ _) => "cons(...)"
  | some (.sym s)   => s!"sym({s})"
  | some (.prim s)  => s!"prim({s})"
  | some (.closure _ _ _) => "<closure>"
  | some .builtinBaseApply => "<builtinBaseApply>"

def runOne (label : String) (expected : String) (actual : Option Val) : IO Unit := do
  let got := shortRepr actual
  let mark := if got == expected then "OK " else "XX "
  IO.println s!"  {mark} {label}: expected {expected}, got {got}"

def main : IO Unit := do
  IO.println "Scene 1: proof-bearing admission — identity mod ADMITTED"
  runOne "(em (set! base-apply base-apply)) ⇒ bool(true)"
         "bool(true)" test_identity_admitted
  runOne "post-admit, (+ 1 2) still 3"
         "num(3)"     test_identity_preserves_plus
  IO.println ""
  IO.println "Scene 2: proof-bearing admission — non-matching mod REFUSED"
  runOne "(em (set! base-apply (lam … 42))) ⇒ bool(false)"
         "bool(false)" test_badmod_refused
  runOne "post-refuse, (+ 1 2) still 3 (no mod in effect)"
         "num(3)"      test_badmod_preserves_plus
