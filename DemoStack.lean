/-
  DemoStack.lean — two admitted wrappers live at once.

  `DemoGuarded` installs one wrapper. Here we *stack*: install multn
  (guard `num?`) over the builtin, then bool-selector (guard `bool?`)
  over multn, through a single gate holding two certificates. The
  second certificate is the disjoint-guard second-install theorem
  `guardedExt_stack_soundForCE` (GuardedExtStack.lean) — kernel-checked
  CE of the bool-selector over the multn wrapper.

  After both installs, all three behaviors coexist:
    (2 3 4)    ⇒ 24   (multn — guard num?)
    (#t 1 2)   ⇒ 1    (bool-selector — guard bool?)
    (+ 1 2)    ⇒ 3    (baseline — constitutionally preserved)

  Run:  lake exe demoStack
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

def demoFuel : Nat := 10000
def probeFuel : Nat := 64

/-! ## 1. The two wrappers, as SOURCE -/

def multnBehavior : Expr :=
  .primApp (.var "mul-list") [.primApp (.var "cons") [.var "op", .var "args"]]
def multnWrapper : Expr := .lam ["op", "args"] (guardedExtBody "num?" multnBehavior)

def boolSelBehavior : Expr :=
  .ifte (.var "op")
    (.primApp (.var "car") [.var "args"])
    (.primApp (.var "car") [.primApp (.var "cdr") [.var "args"]])
def boolSelWrapper : Expr := .lam ["op", "args"] (guardedExtBody "bool?" boolSelBehavior)

def installWrapper (w : Expr) : Expr :=
  .em (.letE "orig" (.var "base-apply") (.set "base-apply" w))
def installGate : Expr := .em (.installPolicy 0)

/-! ## 2. Stage 1 — the multn certificate (over the builtin) -/

def probeMultn : Option (Val × TowerState) :=
  let T := initTower.setPolicyAt 0 acceptAllPolicy
  match T.envAt? 0 with
  | some env => eval probeFuel [] 0
      (.em (.letE "orig" (.var "base-apply") multnWrapper)) env T
  | none => none

def W1 : Val := (probeMultn.map (·.1)).getD .nilV
def heap1 : Heap := (probeMultn.map (·.2.heap)).getD []

theorem multn_admits :
    guardedExtPolicy "num?"
      { target := "base-apply", heap := heap1, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      .builtinBaseApply W1 = true := by native_decide

def multnCertificate : ApprovedModification :=
  guardedExtApproval guardSpec_numq 1 heap1 .nil .nil 0 W1 multn_admits

/-! ## 3. Stage 2 — the bool-selector certificate (over multn)

    Probe the state *after* multn is installed (ungated, under
    acceptAll), so the bool-selector's `orig` binds to `W1`. -/

def afterMultn : Option TowerState :=
  let T := initTower.setPolicyAt 0 acceptAllPolicy
  match T.envAt? 0 with
  | some env =>
      (eval probeFuel [acceptAllPolicy] 0
        (.seq [.em (.installPolicy 0), installWrapper multnWrapper]) env T).map (·.2)
  | none => none

def s1 : TowerState := afterMultn.getD initTower

def probeBoolSel : Option (Val × TowerState) :=
  match s1.envAt? 0 with
  | some env => eval probeFuel [acceptAllPolicy] 0
      (.em (.letE "orig" (.var "base-apply") boolSelWrapper)) env s1
  | none => none

def W2 : Val := (probeBoolSel.map (·.1)).getD .nilV
def heap2 : Heap := (probeBoolSel.map (·.2.heap)).getD []

theorem stack_admit1 :
    guardedExtPolicy "num?"
      { target := "base-apply", heap := heap2, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      .builtinBaseApply W1 = true := by native_decide

theorem stack_admit2 :
    guardedExtPolicy "bool?"
      { target := "base-apply", heap := heap2, env := .nil,
        metaEnv := .nil, index := 0, level := 1 }
      W1 W2 = true := by native_decide

theorem stack_deep_W1 : ValDeep W1 heap2 := by native_decide

def boolSelCertificate : ApprovedModification :=
{ level  := 1
  heap   := heap2
  oldVal := W1
  newVal := W2
  proof  := guardedExt_stack_soundForCE guardSpec_numq guardSpec_boolq
              guardsDisjoint_num_bool 1 heap2 .nil .nil 0 W1 W2
              stack_admit1 stack_admit2 stack_deep_W1 }

/-! ## 4. The stacked gate — two certs, second one via the stack theorem -/

def gate : PolicyTable := [approvedPolicy [multnCertificate, boolSelCertificate]]

/-- Every `.set` this gate admits at level 1 carries a `CE_weak_strong`
    witness (multn over builtin; bool-selector over multn). -/
theorem gate_soundForCE :
    BlackPolicy.SoundForCE_weak_strong 1
      (approvedPolicy [multnCertificate, boolSelCertificate]) := by
  apply approvedPolicy_soundForCE_weak_strong
  intro am h_mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl <;> rfl

/-! ## 5. Both installs, then all three behaviors -/

def installBoth : Expr := .seq [installGate, installWrapper multnWrapper,
                                installWrapper boolSelWrapper]

def bothAdmitted : Option Val :=
  evalProgram demoFuel gate installBoth
def multnLives : Option Val :=
  evalProgram demoFuel gate (.seq [installBoth, .app [.num 2, .num 3, .num 4]])
def boolSelLives : Option Val :=
  evalProgram demoFuel gate (.seq [installBoth, .app [.bool true, .num 1, .num 2]])
def boolSelLivesF : Option Val :=
  evalProgram demoFuel gate (.seq [installBoth, .app [.bool false, .num 1, .num 2]])
def plusPreserved : Option Val :=
  evalProgram demoFuel gate (.seq [installBoth, .app [.var "+", .num 1, .num 2]])

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
  IO.println "TWO wrappers stacked through one gate — the second admitted"
  IO.println "over the first by the disjoint-guard stack theorem."
  IO.println ""
  check "both installs admitted (last set! true)" "bool(true)" bothAdmitted
  check "(2 3 4) ⇒ 24    multn still lives"        "num(24)"    multnLives
  check "(true 1 2) ⇒ 1  bool-selector lives"      "num(1)"     boolSelLives
  check "(false 1 2) ⇒ 2 bool-selector lives"      "num(2)"     boolSelLivesF
  check "(+ 1 2) ⇒ 3      baseline preserved"      "num(3)"     plusPreserved
