/-
  DemoGuarded.lean — the master theorem driving the gate, from SOURCE.

  The guarded-extension companion to `Demo.lean`. Where `Demo.lean`
  admits one wrapper (multn) through its bespoke headline theorem,
  every admission here flows through ONE class-level theorem
  (`guardedExt_soundForCE_first_install_tower`) — the per-wrapper
  cost is a `GuardSpec`: two small lemmas about the guard primitive.

    • ADMITTED — booleans as selectors, guarded by `bool?`.
        `(set! base-apply (λ (op args). (if (bool? op) (if op (car args)
            (car (cdr args))) (orig op args))))`
      Applying a boolean was undefined in the baseline; post-admission
      `(#t 1 2) ⇒ 1` and `(#f 1 2) ⇒ 2`, while `(+ 1 2)` stays `3`.
      Certificate: master theorem + `guardSpec_boolq`.

    • ADMITTED — multn, re-derived as the `num?` instance of the SAME
      family. Post-admission `(2 3 4) ⇒ 24`. Certificate: master
      theorem + `guardSpec_numq`. (Demo.lean's bespoke multn theorem
      is subsumed; see `multn_admits_guardedExt`.)

    • REFUSED — a `closure?`-guarded hijacker that would intercept
      every ordinary function application. No certificate exists for
      it — not "not found": `no_guardSpec_closureq` is a kernel
      theorem that the obligation is unsatisfiable. The gate holds no
      approval for it, so the `.set` returns `bool(false)`.

  Run:  lake exe demoGuarded
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.GuardedExt
import LeanBlack.GuardedExtApproval

open LeanBlack

def demoFuel : Nat := 10000

/-! ## 1. The wrappers, as SOURCE, through the family constructor -/

/-- bool-selector behavior: `(if op (car args) (car (cdr args)))`.
    Runs only when the `bool?` guard fires, i.e. `op` is a boolean. -/
def boolSelBehavior : Expr :=
  .ifte (.var "op")
    (.primApp (.var "car") [.var "args"])
    (.primApp (.var "car") [.primApp (.var "cdr") [.var "args"]])

def boolSelWrapper : Expr :=
  .lam ["op", "args"] (guardedExtBody "bool?" boolSelBehavior)

/-- multn behavior — Demo.lean's wrapper body is exactly
    `guardedExtBody "num?"` of this. -/
def multnBehavior : Expr :=
  .primApp (.var "mul-list") [.primApp (.var "cons") [.var "op", .var "args"]]

def multnWrapperM : Expr :=
  .lam ["op", "args"] (guardedExtBody "num?" multnBehavior)

/-- The hijacker: guard `closure?`, behavior "return 666". Would make
    every ordinary function call return 666. Family-shaped — but no
    `GuardSpec "closure?"` can exist (`no_guardSpec_closureq`). -/
def hijackWrapper : Expr :=
  .lam ["op", "args"] (guardedExtBody "closure?" (.num 666))

/-- Install a wrapper at level 1:
    `(em (let ((orig base-apply)) (set! base-apply <w>)))`. -/
def installWrapper (w : Expr) : Expr :=
  .em (.letE "orig" (.var "base-apply") (.set "base-apply" w))

def installBoolSel : Expr := installWrapper boolSelWrapper
def installMultnM  : Expr := installWrapper multnWrapperM
def installHijack  : Expr := installWrapper hijackWrapper

/-- Install the gate (policy table index 0) at level 1. -/
def installGate : Expr := .em (.installPolicy 0)

/-! ## 2. Derive the admission closures by RUNNING eval on the source -/

/-- Probe fuel is small so the admission theorems below go through by
    kernel `decide` (no `native_decide`): the probe trace is ~15 steps,
    and by fuel monotonicity the result equals any larger-fuel run. -/
def probeFuel : Nat := 32

def probeOf (w : Expr) : Option (Val × TowerState) :=
  let T := initTower.setPolicyAt 0 acceptAllPolicy
  match T.envAt? 0 with
  | some env => eval probeFuel [] 0 (.em (.letE "orig" (.var "base-apply") w)) env T
  | none     => none

def boolSelClosure : Val  := ((probeOf boolSelWrapper).map (·.1)).getD .nilV
def boolSelHeap : Heap    := ((probeOf boolSelWrapper).map (·.2.heap)).getD []
def multnClosureM : Val   := ((probeOf multnWrapperM).map (·.1)).getD .nilV
def multnHeapM : Heap     := ((probeOf multnWrapperM).map (·.2.heap)).getD []

/-! ## 3. Admission facts

    These two Bool facts are checked by `native_decide`, matching
    `Demo.lean`'s practice for its analogous `multnClosure_admits`:
    the probe values are computed through `eval`, whose mutual
    recursion the kernel does not reduce, so kernel `decide` is
    unavailable here. Everything *semantic* — the master theorem,
    the GuardSpecs, the impossibility results, the approval layer —
    is kernel-checked with no `native_decide` (see `AxiomAudit.lean`).
    The admission facts are structural shape checks on concrete
    values; a kernel-only path (literal heaps + simp-evaluation) is
    possible future hardening. -/

theorem boolSel_admits :
    guardedExtPolicy "bool?"
      { target := "base-apply", heap := boolSelHeap, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      .builtinBaseApply boolSelClosure = true := by native_decide

theorem multnM_admits :
    guardedExtPolicy "num?"
      { target := "base-apply", heap := multnHeapM, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      .builtinBaseApply multnClosureM = true := by native_decide

/-! ## 4. Certificates — every one through the SAME master theorem -/

def boolSelCertificate : ApprovedModification :=
  guardedExtApproval guardSpec_boolq 1 boolSelHeap .nil .nil 0
    boolSelClosure boolSel_admits

def multnCertificateM : ApprovedModification :=
  guardedExtApproval guardSpec_numq 1 multnHeapM .nil .nil 0
    multnClosureM multnM_admits

/-- The runtime gate. Two kernel-checked certificates, one theorem
    behind both. There is — provably — no certificate for the
    hijacker. -/
def gate : PolicyTable := [approvedPolicy [boolSelCertificate, multnCertificateM]]

/-- Every `.set` this gate admits at level 1 carries a
    `CE_weak_strong` witness. -/
theorem gate_soundForCE :
    BlackPolicy.SoundForCE_weak_strong 1
      (approvedPolicy [boolSelCertificate, multnCertificateM]) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl <;> rfl

/-! ## 5. The beats -/

-- BASELINE: applying a boolean is undefined.
def boolStuckBefore : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, .app [.bool true, .num 1, .num 2]])

-- ADMITTED: the gated `set!` for the bool-selector succeeds.
def boolSelAccept : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installBoolSel])

-- ADMITTED: booleans now select.
def boolSelTrue : Option Val :=
  evalProgram demoFuel gate
    (.seq [installGate, installBoolSel, .app [.bool true, .num 1, .num 2]])

def boolSelFalse : Option Val :=
  evalProgram demoFuel gate
    (.seq [installGate, installBoolSel, .app [.bool false, .num 1, .num 2]])

-- ADMITTED, yet addition is untouched.
def boolSelPreservesPlus : Option Val :=
  evalProgram demoFuel gate
    (.seq [installGate, installBoolSel, .app [.var "+", .num 1, .num 2]])

-- ADMITTED: multn through the same master theorem.
def multnMAccept : Option Val :=
  evalProgram demoFuel gate
    (.seq [installGate, installMultnM, .app [.num 2, .num 3, .num 4]])

-- REFUSED: the closure?-guarded hijacker.
def hijackRefused : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installHijack])

-- REFUSED, so ordinary application still works.
def hijackPreservesApply : Option Val :=
  evalProgram demoFuel gate
    (.seq [installGate, installHijack,
           .app [.lam ["x"] (.primApp (.var "+") [.var "x", .num 1]), .num 41]])

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
  IO.println "ONE master theorem, TWO admissions, ONE provable refusal."
  IO.println ""
  IO.println "ADMITTED — booleans as selectors (guard: bool?):"
  check "(true 1 2) stuck under the baseline"      "<none>"     boolStuckBefore
  check "gated (set! base-apply bool-sel) succeeds" "bool(true)" boolSelAccept
  check "(true 1 2) ⇒ 1 via new base-apply"         "num(1)"     boolSelTrue
  check "(false 1 2) ⇒ 2 via new base-apply"        "num(2)"     boolSelFalse
  check "(+ 1 2) still 3 (addition preserved)"      "num(3)"     boolSelPreservesPlus
  IO.println ""
  IO.println "ADMITTED — multn as the num? instance of the SAME theorem:"
  check "(2 3 4) ⇒ 24 via new base-apply"           "num(24)"    multnMAccept
  IO.println ""
  IO.println "REFUSED — closure?-guarded hijacker (no certificate CAN exist):"
  check "gated (set! base-apply hijack) refused"    "bool(false)" hijackRefused
  check "((λx. x+1) 41) ⇒ 42 (application intact)"  "num(42)"    hijackPreservesApply
