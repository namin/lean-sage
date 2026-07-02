/-
  DemoForget.lean — the point: "improvement" is only meaningful
  relative to what you already have. A gate that forgets the past can
  check proposals only against day zero — so it CANNOT TELL
  IMPROVEMENT FROM REGRESSION, and below it certifies one as the
  other. A gate that can tell them apart must check proposals against
  everything admitted so far. That growing obligation IS the history;
  nothing more is meant by the word.

  The objection this file answers: why keep a history of admitted
  transitions at all? Why not just improve continually and forget —
  each step checked, current state trusted, past discarded?

  The concession first, because it is real: for unconditional
  conservative extension, forgetting WORKS for baseline clients.
  CE composes (the transitivity behind `guardedExt_stack_soundForCE`),
  so the chain compresses to one fact — "current ⊇ baseline" — and the
  intermediate states can be discarded. `(+ 1 2) ⇒ 3` needs no ledger.

  What cannot be forgotten is the OBLIGATION. "Improvement" is a
  relation to something; the whole question is: conservative over
  WHAT? The two answers are both already in this codebase, as theorem
  signatures:

    frozen      GuardSpec.misses is stated against `applyDirect` —
                the BASELINE dispatcher, forever. The first-install
                obligation, re-checked verbatim on every proposal.

    accumulating  `guardedExt_stack_soundForCE` demands CE over the
                INSTALLED wrapper (via `GuardsDisjoint`): what was
                admitted has entered the obligation.

  This file runs both gates against the same two proposals:

    #1  seq-wrapper (DemoSeq): pairs apply as indexing. Useful; six
        clients start depending on it.
    #2  "an improvement": pair?-guarded, returns 666. Family-shaped,
        carries the SAME kernel-checked `GuardSpec "pair?"` as #1 —
        by the frozen obligation it is exactly as admissible as #1
        was, because pairs were undefined AT TIME ZERO.

  Under the FORGETFUL gate, #2 is admitted, and it keeps every frozen
  promise — `(+ 1 2)` is 3 at every stage, kernel-certifiable
  baseline-CE at every step. No stated guarantee is violated. And the
  six clients go 6/6 → 0/6: four silently corrupted, two stuck.
  The frozen constitution protects only programs that never used
  anything admitted after time zero — for everyone else, yesterday's
  admission is quicksand, and "continual improvement" may oscillate
  (admit, revert, re-admit), each step certified against a world
  nobody lives in anymore.

  Under the REMEMBERING gate, #2 is refused — and not by taste: the
  claim its certificate would need is now FALSE. `(v 2)` is DEFINED
  behavior of the installed state (= 30, `seq_defines_v2`); wrapper
  #2 changes it (= 666, `forgetting_breaks_v2`). Post-admission,
  defined territory has grown; the obligation must grow with it, or
  admission means nothing to the clients it invited.

  That is the answer, one line: forgetting is sound exactly for the
  clients of the state you froze; a history is what makes ADMITTED
  behavior load-bearing rather than provisional. (The gate-level
  analog of lean-keep's "safety is not progress": the forgetful tower
  is safe forever and accumulates nothing.)

  Run:  lake exe demoForget
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.GuardedExt
import LeanBlack.GuardedExtApproval
import LeanBlack.GuardedExtStack

open LeanBlack

def demoFuel : Nat := 100000
def probeFuel : Nat := 64

/-! ## 1. Proposal #1 — the useful one (as in DemoSeq) -/

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

def nthLam : Expr :=
  .lam ["self", "lst", "i"]
    (.ifte (.primApp (.var "=") [.var "i", .num 0])
      (.primApp (.var "car") [.var "lst"])
      (.app [.var "self", .var "self",
             .primApp (.var "cdr") [.var "lst"],
             .primApp (.var "-") [.var "i", .num 1]]))

def seqIndexBehavior : Expr :=
  .letE "nth" nthLam
    (.app [.var "nth", .var "nth", .var "op",
           .primApp (.var "car") [.var "args"]])

def seqWrapper : Expr :=
  .lam ["op", "args"] (guardedExtBody "pair?" seqIndexBehavior)

/-! ## 2. Proposal #2 — "an improvement", same shape, same GuardSpec -/

def wrapper666 : Expr :=
  .lam ["op", "args"] (guardedExtBody "pair?" (.num 666))

def installWrapper (w : Expr) : Expr :=
  .em (.letE "orig" (.var "base-apply") (.set "base-apply" w))

def installSeq : Expr := installWrapper seqWrapper
def install666 : Expr := installWrapper wrapper666
def installGate : Expr := .em (.installPolicy 0)

/-! ## 3. The two gates

    FORGETFUL: the first-install obligation, re-checked verbatim
    forever — family shape, `pair?` guard, `orig` honestly bound.
    Exactly what admitted #1; history plays no part. -/

def forgetfulGate : PolicyTable := [guardedExtPolicy "pair?"]

/-- REMEMBERING: holds the one certificate that exists — proposal #1
    over the builtin, through the master theorem (as in DemoSeq). No
    certificate for #2 is held; none can be issued against the
    installed state, because the CE claim it would need is false
    (`forgetting_breaks_v2` below is the counterexample). -/

def probe : Option (Val × TowerState) :=
  let T := initTower.setPolicyAt 0 acceptAllPolicy
  match T.envAt? 0 with
  | some env => eval probeFuel [] 0
      (.em (.letE "orig" (.var "base-apply") seqWrapper)) env T
  | none     => none

def seqClosure : Val := (probe.map (·.1)).getD .nilV
def seqHeap : Heap := (probe.map (·.2.heap)).getD []

theorem seq_admits :
    guardedExtPolicy "pair?"
      { target := "base-apply", heap := seqHeap, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      .builtinBaseApply seqClosure = true := by native_decide

def seqCertificate : ApprovedModification :=
  guardedExtApproval guardSpec_pairq 1 seqHeap .nil .nil 0
    seqClosure seq_admits

def rememberingGate : PolicyTable := [approvedPolicy [seqCertificate]]

theorem remembering_soundForCE :
    BlackPolicy.SoundForCE_weak_strong 1 (approvedPolicy [seqCertificate]) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl <;> rfl

/-! ## 4. The clients that started depending on admission #1 -/

def vec : Expr := .quote (listToVal [.num 10, .num 20, .num 30])
def perm : Expr := .quote (listToVal [.num 2, .num 0, .num 1])
def price : Expr := .quote (listToVal [.num 100, .num 200, .num 300])
def matrix : Expr :=
  .quote (listToVal [listToVal [.num 1, .num 2], listToVal [.num 3, .num 4]])

def opsTable : Expr :=
  .primApp (.var "cons")
    [.lam ["x", "y"] (.primApp (.var "+") [.var "x", .var "y"]),
     .primApp (.var "cons")
       [.lam ["x", "y"] (.primApp (.var "*") [.var "x", .var "y"]),
        .quote .nilV]]

def twiceLam : Expr :=
  .lam ["f", "x"] (.app [.var "f", .app [.var "f", .var "x"]])

def sumToLam : Expr :=
  .lam ["self", "f", "n"]
    (.ifte (.primApp (.var "=") [.var "n", .num 0])
      (.num 0)
      (.primApp (.var "+")
        [.app [.var "f", .primApp (.var "-") [.var "n", .num 1]],
         .app [.var "self", .var "self", .var "f",
               .primApp (.var "-") [.var "n", .num 1]]]))

def withLib (e : Expr) : Expr :=
  .letE "twice" twiceLam (.letE "sum-to" sumToLam e)

def client1 : Expr := .app [vec, .num 2]
def client2 : Expr := .app [.var "twice", perm, .num 0]
def client3 : Expr := .app [.var "sum-to", .var "sum-to", vec, .num 3]
def client4 : Expr :=
  .letE "ops" opsTable (.app [.app [.var "ops", .num 0], .num 6, .num 7])
def client5 : Expr := .app [.app [matrix, .num 1], .num 0]
def client6 : Expr := .app [price, .num 0]

/-- label, client, value under seq (what admission #1 promised),
    value after the forgetful gate admits #2. -/
def clients : List (String × Expr × String × String) :=
  [("(v 2)",                client1, "num(30)",  "num(666)"),
   ("(twice perm 0)",       client2, "num(1)",   "num(666)"),
   ("(sum-to v 3)",         client3, "num(60)",  "num(1998)"),
   ("((ops 0) 6 7)",        client4, "num(13)",  "<none>"),
   ("((m 1) 0)",            client5, "num(3)",   "<none>"),
   ("(price 0)",            client6, "num(100)", "num(666)")]

/-! ## 5. The runs -/

def runF (prelude : List Expr) (e : Expr) : Option Val :=
  evalProgram demoFuel forgetfulGate (.seq (prelude ++ [withLib e]))

def runR (prelude : List Expr) (e : Expr) : Option Val :=
  evalProgram demoFuel rememberingGate (.seq (prelude ++ [withLib e]))

def stage1 : List Expr := [installGate, installSeq]
def stage2 : List Expr := [installGate, installSeq, install666]

/-! ## 6. The dividing line, as checked facts

    `(v 2)` is DEFINED behavior of the installed state — the meaning
    admission #1 gave it. Wrapper #2 changes it. So no CE-over-
    installed certificate can exist for #2 (the claim is false), while
    its CE-over-baseline pedigree — `guardSpec_pairq`, the very same
    spec that admitted #1 — remains impeccable. `native_decide`, as
    for all concrete-evaluation facts in the demos. -/

theorem seq_defines_v2 :
    evalProgram demoFuel forgetfulGate (.seq (stage1 ++ [client1]))
      = some (.num 30) := by native_decide

theorem forgetting_breaks_v2 :
    evalProgram demoFuel forgetfulGate (.seq (stage2 ++ [client1]))
      = some (.num 666) := by native_decide

theorem forgetting_keeps_the_frozen_promise :
    evalProgram demoFuel forgetfulGate
      (.seq (stage2 ++ [.app [.var "+", .num 1, .num 2]]))
      = some (.num 3) := by native_decide

theorem remembering_refuses :
    evalProgram demoFuel rememberingGate (.seq (stage1 ++ [install666]))
      = some (.bool false) := by native_decide

theorem remembering_keeps_v2 :
    evalProgram demoFuel rememberingGate (.seq (stage2 ++ [client1]))
      = some (.num 30) := by native_decide

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
  IO.println "Continual improvement, forgetting the past — versus a gate that remembers."
  IO.println ""
  IO.println "FORGETFUL GATE — every proposal held to the first-install obligation, forever:"
  IO.println ""
  IO.println "  after admission #1 (seq — pairs apply as indexing):"
  let mut ok1 := 0
  for (label, e, expSeq, _) in clients do
    if (← check label expSeq (runF stage1 e)) then ok1 := ok1 + 1
  IO.println ""
  let _ ← check "  admission #2 (pair?-guarded, returns 666) ADMITTED" "bool(true)"
    (evalProgram demoFuel forgetfulGate (.seq (stage1 ++ [install666])))
  IO.println "      — to this gate #1 and #2 are INDISTINGUISHABLE: same shape, same"
  IO.println "        GuardSpec pair?. At day zero, pairs were undefined; measured"
  IO.println "        there, the improvement and the regression look identical."
  IO.println ""
  IO.println "  after admission #2 — same clients:"
  let mut broken := 0
  for (label, e, expSeq, expAfter) in clients do
    let r := runF stage2 e
    let _ ← check label expAfter r
    if shortRepr r != expSeq then broken := broken + 1
  IO.println ""
  let _ ← check "  (+ 1 2) — the FROZEN promise, still kept" "num(3)"
    (evalProgram demoFuel forgetfulGate (.seq (stage2 ++ [.app [.var "+", .num 1, .num 2]])))
  IO.println ""
  IO.println "REMEMBERING GATE — the obligation accumulates (CE over what is installed):"
  IO.println ""
  let _ ← check "  admission #1 (seq) admitted" "bool(true)"
    (evalProgram demoFuel rememberingGate (.seq [installGate, installSeq]))
  let _ ← check "  proposal #2 REFUSED — its CE claim is now false" "bool(false)"
    (evalProgram demoFuel rememberingGate (.seq (stage1 ++ [install666])))
  IO.println ""
  IO.println "  clients, after the refused attempt:"
  let mut ok2 := 0
  for (label, e, expSeq, _) in clients do
    if (← check label expSeq (runR stage2 e)) then ok2 := ok2 + 1
  IO.println ""
  IO.println s!"score: forgetful gate — clients {ok1}/6 → {6 - broken}/6, baseline intact throughout;"
  IO.println s!"       remembering gate — clients {ok2}/6, the regression never got in."
  IO.println ""
  IO.println "The forgetful gate checked #2 against day zero — the only past it kept —"
  IO.println "so it could not tell improvement from regression, and certified one as"
  IO.println "the other. \"Improvement\" is relative to what you already have: a gate"
  IO.println "that can tell the difference must check proposals against everything"
  IO.println "admitted so far. That growing obligation IS the history."
