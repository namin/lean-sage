/-
  Demo.lean — the gate accepting and rejecting, driven from SOURCE.

  This is the minimal "from source" companion to `ProofBasedSmoke.lean`.
  Everything a user *installs* here is an ordinary source program
  (`Expr` lambdas) run through `evalProgram`. You watch two reflective
  modifications of the interpreter's `base-apply` rule:

    • ADMITTED — multiplication when a number is applied.
        `(set! base-apply (lam (op args)
            (if (num? op) (mul-list (cons op args)) (orig op args))))`
      Applying a number was undefined in the baseline, so this only
      *adds* successes and preserves every baseline success. It carries
      a kernel-checked `CE_weak_strong` certificate, so the gate admits.
      Post-admission `(2 3 4) ⇒ 24`, while `(+ 1 2)` still returns `3`.

    • REJECTED — changing the meaning of addition.
        `(set! base-apply (lam (op args)
            (let ((result (orig op args)))
               (if (num? result) (+ result result) result))))`
      This doubles every numeric result, so `(+ 1 2)` would become `6`.
      That is NOT a conservative extension, so no `CE_weak_strong` value
      exists, so no `ApprovedModification` can be built for it, so the
      gate finds no match and refuses. The `.set` returns `bool(false)`
      and `(+ 1 2)` still returns `3`.

  ── On the "why a Val, not the source?" question ──────────────────────
  The certificate (`ApprovedModification.newVal`) is a `Val`, because
  conservative extension is a property of the *installed closure's*
  behavior and the gate matches on the value the evaluator produces.
  In `ProofBasedSmoke.lean` Scene 8 that closure is hand-reconstructed
  by re-running `freshLevelEnv`. Here we instead DERIVE it from the
  source: `multnClosure` below is literally what `eval` builds from the
  `multnWrapper` lambda (see `multnProbe`), so there is no reconstructed
  environment to drift from the evaluator — the value comes from the
  evaluator itself.

  Run:  lake exe demo
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.HeapAgree

open LeanBlack

def demoFuel : Nat := 10000

/-! ## 1. The two reflective modifications, as SOURCE programs -/

/-- multn wrapper body: `if (num? op) then (mul-list (cons op args)) else (orig op args)`. -/
def multnBody : Expr :=
  .ifte (.primApp (.var "num?") [.var "op"])
    (.primApp (.var "mul-list") [.primApp (.var "cons") [.var "op", .var "args"]])
    (.primApp (.var "orig") [.var "op", .var "args"])

def multnWrapper : Expr := .lam ["op", "args"] multnBody

/-- doubling wrapper body: `let result = (orig op args) in
    if (num? result) then (+ result result) else result`. -/
def doublingBody : Expr :=
  .letE "result" (.primApp (.var "orig") [.var "op", .var "args"])
    (.ifte (.primApp (.var "num?") [.var "result"])
      (.primApp (.var "+") [.var "result", .var "result"])
      (.var "result"))

def doublingWrapper : Expr := .lam ["op", "args"] doublingBody

/-- Install a wrapper at level 1: `(em (let ((orig base-apply)) (set! base-apply <w>)))`. -/
def installWrapper (w : Expr) : Expr :=
  .em (.letE "orig" (.var "base-apply") (.set "base-apply" w))

def installMultn    : Expr := installWrapper multnWrapper
def installDoubling : Expr := installWrapper doublingWrapper

/-- Install the gate (policy table index 0) at level 1. -/
def installGate : Expr := .em (.installPolicy 0)

/-! ## 2. Derive the admission closure by RUNNING eval on the source

    `multnProbe` is `installMultn` with the `set!` stripped, so eval
    returns exactly the closure it would install. We read the closure
    value and heap out of the evaluator's own output — no hand-built
    environment. -/

def multnProbe : Expr :=
  .em (.letE "orig" (.var "base-apply") multnWrapper)

def probe : Option (Val × TowerState) :=
  let T := initTower.setPolicyAt 0 acceptAllPolicy
  match T.envAt? 0 with
  | some env => eval demoFuel [] 0 multnProbe env T
  | none     => none

/-- The multn closure exactly as the evaluator builds it from source. -/
def multnClosure : Val := (probe.map (·.1)).getD .nilV

/-- The heap the evaluator holds at the install point. -/
def installHeap : Heap := (probe.map (·.2.heap)).getD []

/-! ## 3. Build the certificate — the gate constructor is the admission

    `multnApproval` will not typecheck unless the kernel accepts a
    `CE_weak_strong` proof for `multnClosure`. The admit obligation is
    the structural shape check; the CE proof rides through
    `multnExact_soundForCE_first_install_tower` inside `multnApproval`. -/

theorem multnClosure_admits :
    multnExactPolicy
      { target := "base-apply", heap := installHeap, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      .builtinBaseApply multnClosure = true := by native_decide

def multnCertificate : ApprovedModification :=
  multnApproval 1 installHeap .nil .nil 0 multnClosure multnClosure_admits

/-- The runtime gate: a `BlackPolicy` built from one kernel-checked
    certificate. There is NO certificate for doubling. -/
def gate : PolicyTable := [approvedPolicy [multnCertificate]]

/-! ## 4. Run it — accept, reject, and the ungated contrast -/

-- ADMITTED: the gated `set!` succeeds.
def acceptSet : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installMultn])
-- expected: bool(true)

-- ADMITTED: applying a number now multiplies.
def acceptCompute : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installMultn, .app [.num 2, .num 3, .num 4]])
-- expected: num(24)

-- ADMITTED, yet addition is untouched (the point of conservative extension).
def acceptPreservesPlus : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installMultn, .app [.var "+", .num 1, .num 2]])
-- expected: num(3)

-- REJECTED: the gated `set!` for doubling is refused.
def rejectSet : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installDoubling])
-- expected: bool(false)

-- REJECTED: because it was refused, addition still means addition.
def rejectPreservesPlus : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installDoubling, .app [.var "+", .num 1, .num 2]])
-- expected: num(3)

-- CONTRAST: with NO gate (acceptAll), the same doubling source installs
-- and breaks addition — this is what the gate prevents.
def ungatedDoublingBreaksPlus : Option Val :=
  evalProgram demoFuel [acceptAllPolicy]
    (.seq [.em (.installPolicy 0), installDoubling, .app [.var "+", .num 1, .num 2]])
-- expected: num(6)

/-! ## 5. Proving the installation sound (not just exhibiting it)

    Two halves, both as kernel theorems:

    (a) SAFETY — universal, straight from the machinery. Every `.set`
        this gate admits at level 1 carries a `CE_weak_strong` witness.
        Follows in two lines from `approvedPolicy_soundForCE_weak_strong`;
        the only side-condition is that each approval binds to level 1. -/

theorem gate_soundForCE :
    BlackPolicy.SoundForCE_weak_strong 1 (approvedPolicy [multnCertificate]) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp only [List.mem_singleton] at h_mem
  subst h_mem
  rfl

/-- (b) OPERATIONAL — the source install actually triggers that gate.
    Together with `gate_soundForCE`: the modification the source program
    installs is admitted, and everything admitted is conservative. -/
theorem installMultn_admits :
    evalProgram demoFuel gate (.seq [installGate, installMultn]) = some (.bool true) := by
  native_decide

theorem installDoubling_refused :
    evalProgram demoFuel gate (.seq [installGate, installDoubling]) = some (.bool false) := by
  native_decide

/-- The Expr→Val link, as a theorem, for the `.lam` case: evaluating a
    lambda IS the closure over the current environment — definitional,
    no reconstruction. Composing this up through `.em`/`.letE`/`.set`
    (so that `multnClosure` need not be eval-derived at all) is the
    remaining, larger, "make it fully proved" step. -/
theorem eval_lam (n : Nat) (pt : PolicyTable) (lv : Nat)
    (ps : List String) (b : Expr) (env : Env) (T : TowerState) :
    eval (n + 1) pt lv (.lam ps b) env T = some (.closure ps b env, T) := by
  simp [eval]

/-! ## 6. Runner -/

def shortRepr : Option Val → String
  | none                   => "<none>"
  | some (.num n)          => s!"num({n})"
  | some (.bool b)         => s!"bool({b})"
  | some .nilV             => "nilV"
  | some (.cons _ _)       => "cons(...)"
  | some (.sym s)          => s!"sym({s})"
  | some (.prim s)         => s!"prim({s})"
  | some (.closure _ _ _)  => "<closure>"
  | some .builtinBaseApply => "<builtinBaseApply>"

def check (label expected : String) (actual : Option Val) : IO Unit := do
  let got := shortRepr actual
  let mark := if got == expected then "OK " else "XX "
  IO.println s!"  {mark} {label}: expected {expected}, got {got}"

def main : IO Unit := do
  IO.println "ADMITTED — multiplication when a number is applied (multn):"
  check "gated (set! base-apply multn) succeeds" "bool(true)" acceptSet
  check "(2 3 4) ⇒ 24 via new base-apply"        "num(24)"    acceptCompute
  check "(+ 1 2) still 3 (addition preserved)"   "num(3)"     acceptPreservesPlus
  IO.println ""
  IO.println "REJECTED — changing the meaning of addition (doubling):"
  check "gated (set! base-apply doubling) refused" "bool(false)" rejectSet
  check "(+ 1 2) still 3 (mod never installed)"    "num(3)"      rejectPreservesPlus
  IO.println ""
  IO.println "CONTRAST — no gate, same doubling source breaks addition:"
  check "(+ 1 2) ⇒ 6 under acceptAll" "num(6)" ungatedDoublingBreaksPlus
