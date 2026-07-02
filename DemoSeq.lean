/-
  DemoSeq.lean — a USEFUL admitted change: sequences become applicable.

  The objection this file answers: multn and the bool-selector prove the
  gate works, but nobody wants `(2 3 4) ⇒ 24`. Why would you do this to
  a language?

  The change admitted here is one a real language shipped: in Clojure,
  vectors ARE functions of their indices — `(v i)` is indexing. Here the
  same feature enters a RUNNING system through the master theorem
  (`guardedExt_soundForCE_first_install_tower`), with a kernel
  certificate that no existing program changes meaning:

      (set! base-apply
        (λ (op args). (if (pair? op) (nth op (car args)) (orig op args))))

  What makes it useful, and measurable — three beats:

    • CLIENTS UNLOCKED. Six client programs that put data in operator
      position are stuck under the baseline (0/6 converge) and run
      after admission (6/6). Dispatch tables, permutation composition,
      matrix rows — nested indexing `((m 1) 0)` works with no extra
      machinery, because application is uniform.

    • OLD CODE GAINS REACH WITHOUT BEING EDITED. A higher-order library
      (`twice`, `sum-to`, `compose`) is written BEFORE the change, for
      closures. After admission the same unmodified library consumes
      plain lists — `(sum-to vec 3)` sums a vector. Application is the
      language's choke point: only a semantic change retrofits every
      existing higher-order function at once, and only a certified one
      is safe to install in a running system. A library can't do this;
      that is why you do it to the language.

    • OLD PROMISES KEPT, BY THEOREM. The same library applied to
      closures, and the arithmetic baseline, evaluate identically
      before and after — and that is not a test suite's word: the
      certificate IS conservative extension over the baseline.

  The frontier, honestly: the NEXT feature a user would ask for is
  partial application — apply a closure to too few arguments, get a
  closure. Its guard in this family is `closure?`, and
  `no_guardSpec_closureq` is a kernel theorem that no certificate can
  exist for it (the guard would intercept defined behavior: every
  ordinary call). Currying needs a guard that observes arity — i.e.
  (op, args)-sensitive guards, the family generalization named open in
  SCOPE.md. The useful demand is what forces the theory forward.

  Run:  lake exe demoSeq
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.GuardedExt
import LeanBlack.GuardedExtApproval

open LeanBlack

def demoFuel : Nat := 100000

/-! ## 1. The per-proposal cost: `GuardSpec "pair?"` — two small lemmas -/

/-- `pair?` misses everything the baseline defines: `applyDirect` on a
    cons is `none`. Same two-lemma shape as `guardSpec_numq`. -/
theorem guardSpec_pairq : GuardSpec "pair?" where
  ne_op := by decide
  ne_args := by decide
  total := by
    intro op
    show ∃ b, applyPrim_pairQ [op] = some (.bool b)
    cases op <;> exact ⟨_, rfl⟩
  misses := by
    intro op h_true fuel ptable level operands T
    have : ∃ a b, op = .cons a b := by
      cases op with
      | cons a b => exact ⟨a, b, rfl⟩
      | num _ => simp [applyPrim, applyPrim_pairQ] at h_true
      | bool _ => simp [applyPrim, applyPrim_pairQ] at h_true
      | nilV => simp [applyPrim, applyPrim_pairQ] at h_true
      | sym _ => simp [applyPrim, applyPrim_pairQ] at h_true
      | closure _ _ _ => simp [applyPrim, applyPrim_pairQ] at h_true
      | prim _ => simp [applyPrim, applyPrim_pairQ] at h_true
      | builtinBaseApply => simp [applyPrim, applyPrim_pairQ] at h_true
    obtain ⟨a, b, rfl⟩ := this
    cases fuel with
    | zero => simp [applyDirect]
    | succ k => simp [applyDirect]

/-! ## 2. The modification, as SOURCE -/

/-- List indexing, in the object language, by self-application:
    `(λ (self lst i) (if (= i 0) (car lst) (self self (cdr lst) (- i 1))))` -/
def nthLam : Expr :=
  .lam ["self", "lst", "i"]
    (.ifte (.primApp (.var "=") [.var "i", .num 0])
      (.primApp (.var "car") [.var "lst"])
      (.app [.var "self", .var "self",
             .primApp (.var "cdr") [.var "lst"],
             .primApp (.var "-") [.var "i", .num 1]]))

/-- The guard-true behavior: index `op` (the sequence) at `(car args)`.
    Note the behavior itself uses `.app` — the new semantics is written
    in the language and runs under the modified tower. -/
def seqIndexBehavior : Expr :=
  .letE "nth" nthLam
    (.app [.var "nth", .var "nth", .var "op",
           .primApp (.var "car") [.var "args"]])

def seqWrapper : Expr :=
  .lam ["op", "args"] (guardedExtBody "pair?" seqIndexBehavior)

/-- The feature the room would ask for next: partial application.
    Family-shaped, guard `closure?` — and `no_guardSpec_closureq`
    proves no certificate exists for that guard. Refused below. -/
def curryBehavior : Expr :=
  .lam ["more"]
    (.app [.var "op", .primApp (.var "car") [.var "args"], .var "more"])

def curryWrapper : Expr :=
  .lam ["op", "args"] (guardedExtBody "closure?" curryBehavior)

def installWrapper (w : Expr) : Expr :=
  .em (.letE "orig" (.var "base-apply") (.set "base-apply" w))

def installSeq : Expr := installWrapper seqWrapper
def installCurry : Expr := installWrapper curryWrapper
def installGate : Expr := .em (.installPolicy 0)

/-! ## 3. Probe, admission, certificate -/

def probeFuel : Nat := 64

def probe : Option (Val × TowerState) :=
  let T := initTower.setPolicyAt 0 acceptAllPolicy
  match T.envAt? 0 with
  | some env => eval probeFuel [] 0
      (.em (.letE "orig" (.var "base-apply") seqWrapper)) env T
  | none     => none

def seqClosure : Val := (probe.map (·.1)).getD .nilV
def seqHeap : Heap := (probe.map (·.2.heap)).getD []

-- `native_decide`, matching DemoGuarded's practice: the probe closure
-- is computed through `eval`, whose mutual recursion the kernel does
-- not reduce. Everything semantic (the master theorem, the GuardSpec,
-- the impossibility) is kernel-checked.
theorem seq_admits :
    guardedExtPolicy "pair?"
      { target := "base-apply", heap := seqHeap, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      .builtinBaseApply seqClosure = true := by native_decide

def seqCertificate : ApprovedModification :=
  guardedExtApproval guardSpec_pairq 1 seqHeap .nil .nil 0
    seqClosure seq_admits

/-- The runtime gate: one certificate, and — provably — none for the
    currying wrapper (`no_guardSpec_closureq`). -/
def gate : PolicyTable := [approvedPolicy [seqCertificate]]

theorem gate_soundForCE :
    BlackPolicy.SoundForCE_weak_strong 1 (approvedPolicy [seqCertificate]) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl <;> rfl

/-! ## 4. The higher-order library — written for closures, never edited -/

def twiceLam : Expr :=
  .lam ["f", "x"] (.app [.var "f", .app [.var "f", .var "x"]])

/-- `(sum-to f n)` = `f 0 + … + f (n-1)`, self-application recursion. -/
def sumToLam : Expr :=
  .lam ["self", "f", "n"]
    (.ifte (.primApp (.var "=") [.var "n", .num 0])
      (.num 0)
      (.primApp (.var "+")
        [.app [.var "f", .primApp (.var "-") [.var "n", .num 1]],
         .app [.var "self", .var "self", .var "f",
               .primApp (.var "-") [.var "n", .num 1]]]))

def composeLam : Expr :=
  .lam ["f", "g", "x"] (.app [.var "f", .app [.var "g", .var "x"]])

def withLib (e : Expr) : Expr :=
  .letE "twice" twiceLam (.letE "sum-to" sumToLam (.letE "compose" composeLam e))

def runBefore (e : Expr) : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, withLib e])

def runAfter (e : Expr) : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installSeq, withLib e])

/-! ## 5. The clients — data in operator position -/

def vec : Expr := .quote (listToVal [.num 10, .num 20, .num 30])
def perm : Expr := .quote (listToVal [.num 2, .num 0, .num 1])
def price : Expr := .quote (listToVal [.num 100, .num 200, .num 300])
def matrix : Expr :=
  .quote (listToVal [listToVal [.num 1, .num 2], listToVal [.num 3, .num 4]])

/-- A dispatch table holding CLOSURES, selected by opcode — built
    in-language because closures capture their environment. -/
def opsTable : Expr :=
  .primApp (.var "cons")
    [.lam ["x", "y"] (.primApp (.var "+") [.var "x", .var "y"]),
     .primApp (.var "cons")
       [.lam ["x", "y"] (.primApp (.var "*") [.var "x", .var "y"]),
        .quote .nilV]]

def client1 : Expr := .app [vec, .num 2]                        -- (v 2)            ⇒ 30
def client2 : Expr := .app [.var "twice", perm, .num 0]         -- perm∘perm at 0   ⇒ 1
def client3 : Expr := .app [.var "sum-to", .var "sum-to", vec, .num 3]  -- Σ v      ⇒ 60
def client4 : Expr := .app [.var "compose", price, perm, .num 1]  -- price[perm[1]] ⇒ 100
def client5 : Expr :=                                            -- ((ops 0) 6 7)   ⇒ 13
  .letE "ops" opsTable (.app [.app [.var "ops", .num 0], .num 6, .num 7])
def client6 : Expr := .app [.app [matrix, .num 1], .num 0]       -- ((m 1) 0)       ⇒ 3

def clients : List (String × Expr × String) :=
  [("(v 2)                    — direct indexing",        client1, "num(30)"),
   ("(twice perm 0)           — perm composed w/ itself", client2, "num(1)"),
   ("(sum-to v 3)             — library sums a LIST",     client3, "num(60)"),
   ("(compose price perm 1)   — two tables composed",     client4, "num(100)"),
   ("((ops 0) 6 7)            — dispatch table of closures", client5, "num(13)"),
   ("((m 1) 0)                — nested: matrix row, then cell", client6, "num(3)")]

/-! ## 6. The baseline — old promises, checked before AND after -/

def base1 : Expr := .app [.var "+", .num 1, .num 2]
def base2 : Expr := .app [.lam ["x"] (.primApp (.var "+") [.var "x", .num 1]), .num 41]
def base3 : Expr :=
  .app [.var "twice", .lam ["x"] (.primApp (.var "*") [.var "x", .num 2]), .num 3]
def base4 : Expr := .app [.var "sum-to", .var "sum-to", .lam ["x"] (.var "x"), .num 4]

def baselines : List (String × Expr × String) :=
  [("(+ 1 2)", base1, "num(3)"),
   ("((λx. x+1) 41)", base2, "num(42)"),
   ("(twice (λx. 2x) 3)     — library on closures", base3, "num(12)"),
   ("(sum-to (λx. x) 4)     — library on closures", base4, "num(6)")]

-- REFUSED: currying. The gate holds no approval — and can't:
-- `no_guardSpec_closureq`.
def curryRefused : Option Val :=
  evalProgram demoFuel gate (.seq [installGate, installCurry])

/-! ## 7. Runner -/

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

def check (label expected : String) (actual : Option Val) : IO Bool := do
  let got := shortRepr actual
  let ok := got == expected
  IO.println s!"  {if ok then "OK " else "XX "} {label}: expected {expected}, got {got}"
  pure ok

def main : IO Unit := do
  IO.println "A useful admitted change: sequences become applicable (Clojure-style)."
  IO.println ""
  IO.println "BEFORE — clients with data in operator position, baseline semantics:"
  let mut beforeCount := 0
  for (label, e, _) in clients do
    let r := runBefore e
    let _ ← check label "<none>" r
    if shortRepr r != "<none>" then beforeCount := beforeCount + 1
  IO.println ""
  IO.println "ADMITTED — (set! base-apply seq-wrapper), certificate via the master theorem:"
  let installOk ← check "gated install succeeds" "bool(true)"
    (evalProgram demoFuel gate (.seq [installGate, installSeq]))
  IO.println ""
  IO.println "AFTER — the same clients:"
  let mut afterCount := 0
  for (label, e, expected) in clients do
    if (← check label expected (runAfter e)) then afterCount := afterCount + 1
  IO.println ""
  IO.println "OLD PROMISES — identical before and after (and certified, not just tested):"
  let mut baseOk := true
  for (label, e, expected) in baselines do
    let b := runBefore e
    let a := runAfter e
    let same := shortRepr b == expected && shortRepr a == expected
    IO.println s!"  {if same then "OK " else "XX "} {label}: before {shortRepr b}, after {shortRepr a} (expected {expected})"
    baseOk := baseOk && same
  IO.println ""
  IO.println "REFUSED — partial application (guard closure?): no certificate CAN exist"
  IO.println "  (no_guardSpec_closureq — it would intercept every ordinary call;"
  IO.println "   currying needs arity-aware guards: the open family generalization):"
  let _ ← check "gated (set! base-apply curry) refused" "bool(false)" curryRefused
  IO.println ""
  IO.println s!"score: clients {beforeCount}/6 before → {afterCount}/6 after; \
baseline {if baseOk then "unchanged" else "BROKEN"}; install {if installOk then "admitted" else "FAILED"}"
