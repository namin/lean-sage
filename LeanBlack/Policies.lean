/-
  lean-black: Verified policy library (tower-aware).

  Adapted from `lean-green/LeanBlack/Policies.lean`. The structural
  policy definitions (`acceptAll`, `rejectAll`, `numGuardPolicy`,
  `multnExactPolicy`) port verbatim — `BlackPolicy` is unchanged
  in shape (`MutationCtx → Val → Val → Bool`), the only difference
  is `MutationCtx.level` was added.

  The wrapper `callAsBaseApply` and the conservative-extension
  predicate `CE` / `CE_weak` are *per-level* in this version: cross-
  side policy equality is checked at a specific `level`, not on a
  monolithic `s.policy`.

  ## Contents

  - `callAsBaseApply` (tower-aware)
  - `CE` / `CE_weak` (per-level)
  - `rejectAllPolicy` SoundForCE proof
  - `numGuardPolicy` / `multnExactPolicy` definitions + structural
    shape lemmas
  - `verifiedTable` and indexing constants
  - `OrigBoundIn` / `NumQBoundIn` / `InstallFacts` / `RuntimeWF`
    install-protocol structures
  - `multnExactPolicy_implies_InstallFacts` (bridge lemma)
  - `multn_closure_body_unfolds` (closure-body trace)
  - `multnExact_CE_num_case_vacuous` (numerical case, vacuous)
  - `multnExact_CE_nonnum_case` (substantive non-numerical case via
    `applyDirect_heap_extend_weak`)
  - `multnExact_soundForCE_first_install_tower` (the headline,
    proven by combining the num and non-num cases)
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame

/-! ## Calling a Val as base-apply (tower-aware) -/

/-- Call a `Val` as if it were the level-`level+1` `base-apply`.
    `.builtinBaseApply` dispatches `(op, operands)` directly; a
    closure replacement takes `(op, listOf operands)` (matching the
    `applyVia` convention). -/
def callAsBaseApply (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (baseApply : Val) (op : Val) (operands : List Val) (T : TowerState)
    : Option (Val × TowerState) :=
  match baseApply with
  | .builtinBaseApply => applyDirect fuel ptable level op operands T
  | _                 => applyDirect fuel ptable level baseApply
                                     [op, listToVal operands] T

/-- **Conservative extension** between two candidate base-apply
    values at a given `level`. `new` conservatively extends `old`
    if every successful call through `old` produces a successful
    call through `new` with a `ValVis`-related result and well-
    formed post-state.

    **`h_ref` parameter (compositional CE):** the test state's heap
    has length ≥ `h_ref.length`. This length-monotonicity premise
    is sufficient for ValValid lifting (via `ValValid.length_mono`)
    and supports composition across mutating sub-evals (where the
    intermediate heap is no longer a strict prefix-extension). -/
def CE (level : Nat) (h_ref : Heap) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    h_ref.length ≤ T.heap.length →
    HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
    ValValid old T.heap → ValValid new T.heap →
    PolicyTableRespectsBisimT ptable →
    (∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
    (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length

/-- Same as `CE` but with `ValVis_weak` in the conclusion. -/
def CE_weak (level : Nat) (h_ref : Heap) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    h_ref.length ≤ T.heap.length →
    HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
    ValValid old T.heap → ValValid new T.heap →
    PolicyTableRespectsBisimT ptable →
    (∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
    (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
    (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length

/-- Soundness for CE binds `h_ref := ctx.heap` — the policy's view of the
    heap at admission time. Test states extending `ctx.heap` see CE-soundness
    (this matches the natural use: a `.set` step admits a modification
    based on the heap at the moment of decision, and consumers of the
    resulting CE pass test states extending that heap). -/
abbrev BlackPolicy.SoundForCE (level : Nat) (p : BlackPolicy) : Prop :=
  ∀ ctx old new, p ctx old new = true → CE level ctx.heap old new

abbrev BlackPolicy.SoundForCE_weak (level : Nat) (p : BlackPolicy) : Prop :=
  ∀ ctx old new, p ctx old new = true → CE_weak level ctx.heap old new

/-! ## Trivial policies -/

theorem rejectAllPolicy_soundForCE (level : Nat) :
    rejectAllPolicy.SoundForCE level := by
  intro _ _ _ h; simp [rejectAllPolicy] at h

/-! ## Numerical helpers (ported from lean-green:Policies.lean:155-186)

    Used by the multnExact CE soundness theorem to split into the
    vacuous numerical case (`op = .num n`, where `builtinBaseApply`
    returns none) and the substantive non-numerical case. -/

/-- `op` is not a number. -/
def OpNotNum (op : Val) : Prop := ∀ n, op ≠ .num n

theorem applyDirect_num_returns_none (fuel : Nat) (ptable : PolicyTable)
    (level : Nat) (n : Int) (operands : List Val) (T : TowerState) :
    applyDirect fuel ptable level (.num n) operands T = none := by
  cases fuel with
  | zero => simp [applyDirect]
  | succ k => simp [applyDirect]

theorem callAsBaseApply_builtin_num_none
    (fuel : Nat) (ptable : PolicyTable) (level : Nat) (n : Int)
    (operands : List Val) (T : TowerState) :
    callAsBaseApply fuel ptable level .builtinBaseApply (.num n) operands T
        = none := by
  unfold callAsBaseApply
  exact applyDirect_num_returns_none fuel ptable level n operands T

theorem applyPrim_numq_nonnum (op : Val) (h_op : OpNotNum op) :
    applyPrim "num?" [op] = some (.bool false) := by
  cases op with
  | num n     => exact absurd rfl (h_op n)
  | bool _    => rfl
  | nilV      => rfl
  | cons _ _  => rfl
  | sym _     => rfl
  | closure _ _ _    => rfl
  | prim _           => rfl
  | builtinBaseApply => rfl

/-- **Numerical-operator half** of `multnExact_soundForCE_first_install_tower`
    (vacuous). When `op = .num n`, `callAsBaseApply` through
    `builtinBaseApply` returns `none` regardless of fuel — so the
    premise is unsatisfiable and the conclusion follows trivially.
    Ported from lean-green:Policies.lean:1076. -/
theorem multnExact_CE_num_case_vacuous
    (new : Val) (fuel : Nat) (ptable : PolicyTable) (level : Nat)
    (n : Int) (operands : List Val) (T : TowerState)
    (r : Val) (T' : TowerState) :
    callAsBaseApply fuel ptable level .builtinBaseApply (.num n) operands T
        = some (r, T') →
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new (.num n) operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      T'.policyAt? level = T''.policyAt? level ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length := by
  intro h
  rw [callAsBaseApply_builtin_num_none] at h
  contradiction

/-! ## `numGuardPolicy` — loose structural shape

    Admits any closure with `(λ (op args). (if (num? op) <anything>
    <anything>))` shape. The else-branch is unconstrained — a
    closure-shaped malicious modification can pass this. Used to
    illustrate the "loose vs strict" governance contrast in demos.
    Not sound for CE. -/
def numGuardPolicy : BlackPolicy := fun _ctx _old new =>
  match new with
  | .closure [_, _] body _ =>
      match body with
      | .ifte cond _ _ =>
          match cond with
          | .primApp (.var pred) [.var _] => pred == "num?"
          | _                              => false
      | _ => false
  | _ => false

def NumGuardShape (v : Val) : Prop :=
  ∃ p1 p2 t e cenv var,
    v = .closure [p1, p2]
      (.ifte (.primApp (.var "num?") [.var var]) t e) cenv

theorem numGuard_sound_for_shape :
    numGuardPolicy.Sound (fun _ new => NumGuardShape new) := by
  intro _ _ new h
  unfold numGuardPolicy at h
  split at h
  · split at h
    · split at h
      · rename_i pred _
        have hpred : pred = "num?" := by simp at h; exact h
        subst hpred
        exact ⟨_, _, _, _, _, _, rfl⟩
      · simp at h
    · simp at h
  · simp at h

/-! ## `multnExactPolicy` — strict multn shape + install-protocol

    Admits a `(λ (op args). (if (num? op) <num-branch>
    (orig op args)))` closure *with the delegating else-branch
    fixed* AND with `cenv` binding `orig` to the current
    `base-apply` (= `oldVal`) and `num?` to `.prim "num?"`. The
    extra structural and install-protocol checks make this sound
    for `CE_weak` (first install — `oldVal = .builtinBaseApply`).
    See the headline theorem `multnExact_soundForCE_first_install_tower`
    below. -/
def multnExactPolicy : BlackPolicy := fun ctx oldVal new =>
  -- Target restriction
  (ctx.target == "base-apply") &&
  (match new with
   | .closure ["op", "args"]
       (.ifte (.primApp (.var "num?") [.var "op"])
              _
              (.primApp (.var "orig") [.var "op", .var "args"]))
       cenv =>
       (match cenv.lookup "orig" with
        | some idx_o =>
            match ctx.heap[idx_o]? with
            | some v => v == oldVal
            | _ => false
        | none => false) &&
       (match cenv.lookup "num?" with
        | some idx_n =>
            match ctx.heap[idx_n]? with
            | some (.prim "num?") => true
            | _ => false
        | none => false)
   | _ => false)

def MultnExactShape (v : Val) : Prop :=
  ∃ t cenv,
    v = .closure ["op", "args"]
      (.ifte (.primApp (.var "num?") [.var "op"])
             t
             (.primApp (.var "orig") [.var "op", .var "args"]))
      cenv

theorem multnExact_sound_for_shape :
    multnExactPolicy.Sound (fun _ new => MultnExactShape new) := by
  intro _ _ new h
  unfold multnExactPolicy at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h_shape⟩ := h
  split at h_shape
  · exact ⟨_, _, rfl⟩
  · simp at h_shape

/-! ## Verified policy table -/

/-- The verified policy table. Each entry will (eventually) come with
    a `PolicyRespectsBisimT` proof. CE soundness is per-policy and
    stated by the relevant theorem (`multnExact_soundForCE_first_install_tower`
    for `multnExactPolicy`). -/
def verifiedTable : PolicyTable := [rejectAllPolicy, numGuardPolicy, multnExactPolicy]

namespace Policy
def idx_rejectAll   : Nat := 0
def idx_numGuard    : Nat := 1
def idx_multnExact  : Nat := 2
end Policy

/-! ## Install-protocol facts and runtime well-formedness

    Ported from lean-green:Policies.lean:828-937. Tower-aware:
    `RuntimeWF` references `T.heap` and per-level envs via `T.envAt?`. -/

/-- The closure's captured env binds `"orig"` to a heap cell whose
    value is `old`. -/
def OrigBoundIn (heap : Heap) (old : Val) (new : Val) : Prop :=
  ∃ ps body cenv idx,
    new = .closure ps body cenv ∧
    cenv.lookup "orig" = some idx ∧
    heap[idx]? = some old

/-- The closure's captured env binds `"num?"` to the `.prim "num?"` value. -/
def NumQBoundIn (heap : Heap) (new : Val) : Prop :=
  ∃ ps body cenv idx,
    new = .closure ps body cenv ∧
    cenv.lookup "num?" = some idx ∧
    heap[idx]? = some (.prim "num?")

/-- Install-time facts the runner must establish when admitting a
    `multnExactPolicy`-shaped modification. -/
structure InstallFacts (oldVal new : Val) (heap : Heap) : Prop where
  orig : OrigBoundIn heap oldVal new
  numq : NumQBoundIn heap new

/-- Bridge lemma: the runtime gate's admission implies the structural
    install-protocol facts. -/
theorem multnExactPolicy_implies_InstallFacts
    {ctx : MutationCtx} {oldVal new : Val}
    (h : multnExactPolicy ctx oldVal new = true) :
    ctx.target = "base-apply" ∧ InstallFacts oldVal new ctx.heap := by
  have shape : MultnExactShape new :=
    multnExact_sound_for_shape ctx oldVal new h
  obtain ⟨t, cenv, h_new_eq⟩ := shape
  subst h_new_eq
  unfold multnExactPolicy at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h_tgt, h_orig, h_numq⟩ := h
  have orig_facts :
      ∃ idx_o, cenv.lookup "orig" = some idx_o ∧
               ctx.heap[idx_o]? = some oldVal := by
    cases h_lookup : cenv.lookup "orig" with
    | none => simp [h_lookup] at h_orig
    | some idx_o =>
        simp only [h_lookup] at h_orig
        cases h_heap : ctx.heap[idx_o]? with
        | none => simp [h_heap] at h_orig
        | some v =>
            simp only [h_heap] at h_orig
            have h_eq : v = oldVal := val_beq_eq v oldVal h_orig
            subst h_eq
            exact ⟨idx_o, rfl, h_heap⟩
  have numq_facts :
      ∃ idx_n, cenv.lookup "num?" = some idx_n ∧
               ctx.heap[idx_n]? = some (.prim "num?") := by
    cases h_lookup : cenv.lookup "num?" with
    | none => simp [h_lookup] at h_numq
    | some idx_n =>
        simp only [h_lookup] at h_numq
        cases h_heap : ctx.heap[idx_n]? with
        | none => simp [h_heap] at h_numq
        | some v =>
            simp only [h_heap] at h_numq
            cases v with
            | prim name =>
                by_cases h_eq : name = "num?"
                · subst h_eq; exact ⟨idx_n, rfl, h_heap⟩
                · exfalso; simp [h_eq] at h_numq
            | num _ => simp at h_numq
            | bool _ => simp at h_numq
            | nilV => simp at h_numq
            | sym _ => simp at h_numq
            | cons _ _ => simp at h_numq
            | builtinBaseApply => simp at h_numq
            | closure _ _ _ => simp at h_numq
  obtain ⟨idx_o, h_lookup_o, h_heap_o⟩ := orig_facts
  obtain ⟨idx_n, h_lookup_n, h_heap_n⟩ := numq_facts
  refine ⟨h_tgt, ?_, ?_⟩
  · exact ⟨_, _, _, idx_o, rfl, h_lookup_o, h_heap_o⟩
  · exact ⟨_, _, _, idx_n, rfl, h_lookup_n, h_heap_n⟩

/-- Runtime well-formedness invariants the tower runner inductively
    maintains. Tower-aware: heap and per-level envs are validity-closed,
    captured cenv of `new` (when a closure) is valid in heap, and the
    `(op, operands)` triple to dispatch is valid. -/
structure RuntimeWF
    (new op : Val) (operands : List Val) (T : TowerState) : Prop where
  hv_heap     : HeapValid T.heap
  ev_levels   : ∀ n env, T.envAt? n = some env → EnvValid env T.heap
  ev_cenv     : ∀ ps body cenv', new = .closure ps body cenv' → EnvValid cenv' T.heap
  vv_op       : ValValid op T.heap
  lvv_operands : ListValValid operands T.heap

/-! ## The multn closure-body trace lemma (tower-aware)

    Ported from lean-green:Policies.lean:953-1069. With `fuel ≥ 2`,
    `callAsBaseApply` on the multn closure unfolds in `fuel + 4`
    steps to `applyDirect fuel op operands` at the alloc'd state.

    The proof steps through `applyDirect`'s closure case (length
    check + foldl alloc + eval body), then `eval` of the `.ifte`
    cond and else branches. -/
theorem multn_closure_body_unfolds
    (fuel : Nat) (h_fuel : fuel ≥ 2)
    (ptable : PolicyTable) (level : Nat)
    (op : Val) (h_op : OpNotNum op)
    (operands : List Val)
    (t : Expr) (cenv : Env) (idx_o idx_n : Nat)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_lookup_n : cenv.lookup "num?" = some idx_n)
    (T : TowerState)
    (h_heap_o : (T.heap ++ [op, listToVal operands])[idx_o]? =
                some .builtinBaseApply)
    (h_heap_n : (T.heap ++ [op, listToVal operands])[idx_n]? =
                some (.prim "num?")) :
    callAsBaseApply (fuel + 4) ptable level
      (.closure ["op", "args"]
        (.ifte (.primApp (.var "num?") [.var "op"]) t
               (.primApp (.var "orig") [.var "op", .var "args"]))
        cenv) op operands T
    = applyDirect fuel ptable level op operands
        { T with heap := T.heap ++ [op, listToVal operands] } := by
  obtain ⟨k, hk⟩ : ∃ k, fuel = k + 2 := ⟨fuel - 2, by omega⟩
  subst hk
  have h_lookup_op_alloc :
      (T.heap ++ [op, listToVal operands])[T.heap.length]? = some op := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have h_lookup_args_alloc :
      (T.heap ++ [op, listToVal operands])[T.heap.length + 1]?
        = some (listToVal operands) := by
    rw [List.getElem?_append_right (by omega)]; simp
  show callAsBaseApply (k + 6) ptable _ _ op operands T = _
  unfold callAsBaseApply
  -- applyDirect on closure: length check + foldl alloc + eval body.
  simp only [applyDirect, allocStep, Heap.alloc, List.zip, List.zipWith,
             List.foldl, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
             ↓reduceIte, List.length_append, List.length_singleton,
             List.append_assoc, List.cons_append, List.nil_append]
  let env_alloc : Env := Env.cons "args" (T.heap.length + 1)
                          (Env.cons "op" T.heap.length cenv)
  let T_alloc : TowerState :=
    { T with heap := T.heap ++ [op, listToVal operands] }
  show eval (k + 5) ptable level
       (.ifte (.primApp (.var "num?") [.var "op"]) t
              (.primApp (.var "orig") [.var "op", .var "args"]))
       env_alloc T_alloc
       = applyDirect (k + 2) ptable level op operands T_alloc
  have hl_numq : env_alloc.lookup "num?" = some idx_n := by
    show (Env.cons "args" (T.heap.length + 1)
          (Env.cons "op" T.heap.length cenv)).lookup "num?" = _
    rw [env_alloc_lookup_other (s_heap := T.heap) (cenv := cenv) "num?"
          (by decide) (by decide)]
    exact h_lookup_n
  have hl_op : env_alloc.lookup "op" = some T.heap.length := env_alloc_lookup_op T.heap cenv
  have hl_args : env_alloc.lookup "args" = some (T.heap.length + 1) :=
    env_alloc_lookup_args T.heap cenv
  have hl_orig : env_alloc.lookup "orig" = some idx_o := by
    show (Env.cons "args" (T.heap.length + 1)
          (Env.cons "op" T.heap.length cenv)).lookup "orig" = _
    rw [env_alloc_lookup_other (s_heap := T.heap) (cenv := cenv) "orig"
          (by decide) (by decide)]
    exact h_lookup_o
  have hp_numq : T_alloc.heap[idx_n]? = some (.prim "num?") := h_heap_n
  have hp_op : T_alloc.heap[T.heap.length]? = some op := h_lookup_op_alloc
  have hp_args : T_alloc.heap[T.heap.length + 1]? = some (listToVal operands) :=
    h_lookup_args_alloc
  have hp_orig : T_alloc.heap[idx_o]? = some .builtinBaseApply := h_heap_o
  -- The cond `(num? op)` evaluates to `.bool false` (op is non-num).
  have h_cond : eval (k + 4) ptable level (.primApp (.var "num?") [.var "op"])
        env_alloc T_alloc
        = some (.bool false, T_alloc) := by
    simp only [eval, evalList, applyDirect, hl_numq, hp_numq, hl_op, hp_op,
               applyPrim_numq_nonnum op h_op]
  -- Eval the else-branch → applyDirect builtinBaseApply [op, listToVal operands]
  --                     → applyDirect op operands.
  have h_else : eval (k + 4) ptable level
        (.primApp (.var "orig") [.var "op", .var "args"])
        env_alloc T_alloc
        = applyDirect (k + 2) ptable level op operands T_alloc := by
    simp only [eval, evalList, applyDirect, hl_orig, hp_orig, hl_op, hp_op,
               hl_args, hp_args, valToList_listToVal]
  -- Combine: .ifte under .bool false picks the else.
  unfold eval
  -- Reduce the match-on-Expr to the .ifte arm.
  simp only []
  rw [h_cond]
  exact h_else

/-! ## The non-numerical case (substantive trace + framing)

    Ported from lean-green:Policies.lean:1110-1196. Tower-aware:
    threads `level` through callAsBaseApply / applyDirect. Uses
    `applyDirect_heap_extend_weak` (Frame.lean) for the prefix-
    extension lemma, which is itself derived from `shift_respect`. -/
theorem multnExact_CE_nonnum_case
    {new : Val} {ctx : MutationCtx}
    (h_admit : multnExactPolicy ctx .builtinBaseApply new = true)
    {fuel : Nat} (h_fuel : fuel ≥ 2)
    {ptable : PolicyTable} {level : Nat} {op : Val} (h_op : OpNotNum op)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    {operands : List Val} {T : TowerState}
    {r : Val} {T' : TowerState}
    (h_old : callAsBaseApply fuel ptable level .builtinBaseApply op operands T
        = some (r, T'))
    (install : InstallFacts .builtinBaseApply new T.heap)
    (wf : RuntimeWF new op operands T)
    (h_heap_deep : HeapDeep T.heap) (h_op_deep : ValDeep op T.heap)
    (h_operands_deep : ListValDeep operands T.heap)
    (h_levels_deep : ∀ n env, T.envAt? n = some env → EnvDeep env T.heap)
    (h_levels_resp : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_pt_shift :
      PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable)
    (h_pol_shift :
      ∀ n p, T.policyAt? n = some p →
        PolicyRespectsShift T.heap.length [op, listToVal operands] p) :
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      (∀ n, T'.policyAt? n = T''.policyAt? n) ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length := by
  -- Destructure.
  obtain ⟨h_orig, h_numq⟩ := install
  obtain ⟨h_heap, h_levels_valid, _hv_cenv, hv_op, hv_operands⟩ := wf
  -- new is multn-shaped.
  have shape : MultnExactShape new :=
    multnExact_sound_for_shape ctx .builtinBaseApply new h_admit
  obtain ⟨t, cenv, h_eq⟩ := shape
  subst h_eq
  -- Extract orig's index.
  obtain ⟨ps_o, body_o, cenv_o, idx_o, h_eq_o, h_lookup_o, h_heap_o⟩ := h_orig
  injection h_eq_o with hps_eq hbody_eq hcenv_eq
  subst hps_eq; subst hbody_eq; subst hcenv_eq
  -- Extract num?'s index.
  obtain ⟨_, _, _, idx_n, hnew_eq, h_lookup_n, h_heap_n⟩ := h_numq
  injection hnew_eq with _ _ hcenv_eq2
  subst hcenv_eq2
  -- callAsBaseApply on .builtinBaseApply reduces to applyDirect.
  have h_app : applyDirect fuel ptable level op operands T = some (r, T') := by
    unfold callAsBaseApply at h_old; exact h_old
  -- Heap-index validity.
  have h_idx_o_lt : idx_o < T.heap.length := by
    have := List.getElem?_eq_some_iff.mp h_heap_o
    obtain ⟨h, _⟩ := this; exact h
  have h_idx_n_lt : idx_n < T.heap.length := by
    have := List.getElem?_eq_some_iff.mp h_heap_n
    obtain ⟨h, _⟩ := this; exact h
  -- Heap lookups in the alloc'd state (left half of append).
  have h_lookup_orig_alloc :
      (T.heap ++ [op, listToVal operands])[idx_o]? = some .builtinBaseApply := by
    rw [List.getElem?_append_left h_idx_o_lt]; exact h_heap_o
  have h_lookup_numq_alloc :
      (T.heap ++ [op, listToVal operands])[idx_n]? = some (.prim "num?") := by
    rw [List.getElem?_append_left h_idx_n_lt]; exact h_heap_n
  -- Trace: callAsBaseApply (fuel+4) on the multn closure → applyDirect fuel.
  have h_trace := multn_closure_body_unfolds fuel h_fuel ptable level op h_op operands
    t cenv idx_o idx_n h_lookup_o h_lookup_n T
    h_lookup_orig_alloc h_lookup_numq_alloc
  -- Validity of the appended cells in T.heap.
  have h_extras_valid : ListValValid [op, listToVal operands] T.heap :=
    ⟨hv_op, ValValid_listToVal hv_operands, trivial⟩
  -- Apply the prefix-extension lemma.
  obtain ⟨r_b, T_b', h_app_b, h_vv_r, h_heap_valid, h_state_eq, h_heap_mono⟩ :=
    applyDirect_heap_extend_weak hresp_pt h_heap hv_op hv_operands
      h_levels_valid h_levels_resp h_app
      [op, listToVal operands] h_extras_valid
      h_heap_deep h_op_deep h_operands_deep h_levels_deep
      h_pt_shift h_pol_shift
  refine ⟨fuel + 4, T_b', r_b, ?_, h_vv_r, h_state_eq, h_heap_valid, ?_⟩
  · rw [h_trace]; exact h_app_b
  · have h_alloc_len : T.heap.length ≤ T.heap.length + [op, listToVal operands].length :=
      Nat.le_add_right _ _
    exact Nat.le_trans h_alloc_len h_heap_mono

/-! ## The headline theorem (tower-aware)

    Adapted from lean-green's `multnExact_soundForCE_first_install`.
    Combines the numerical case (`multnExact_CE_num_case_vacuous`) and
    non-numerical case (`multnExact_CE_nonnum_case`) by case analysis
    on `op`. The proof is conditional on the runtime invariants the
    runner maintains (Deep validity, PolicyRespectsBisim/Shift). -/
theorem multnExact_soundForCE_first_install_tower
    {new : Val} {ctx : MutationCtx}
    (h_admit : multnExactPolicy ctx .builtinBaseApply new = true)
    {fuel : Nat} (h_fuel : fuel ≥ 2)
    {ptable : PolicyTable} {level : Nat} {op : Val}
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    {operands : List Val} {T : TowerState}
    {r : Val} {T' : TowerState}
    (h_old : callAsBaseApply fuel ptable level .builtinBaseApply op operands T
        = some (r, T'))
    (install : InstallFacts .builtinBaseApply new T.heap)
    (wf : RuntimeWF new op operands T)
    (h_heap_deep : HeapDeep T.heap) (h_op_deep : ValDeep op T.heap)
    (h_operands_deep : ListValDeep operands T.heap)
    (h_levels_deep : ∀ n env, T.envAt? n = some env → EnvDeep env T.heap)
    (h_levels_resp : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (h_pt_shift :
      PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable)
    (h_pol_shift :
      ∀ n p, T.policyAt? n = some p →
        PolicyRespectsShift T.heap.length [op, listToVal operands] p) :
    ∃ fuel' T'' r',
      callAsBaseApply fuel' ptable level new op operands T = some (r', T'') ∧
      ValVis_weak r r' T'.heap T''.heap ∧
      (∀ n, T'.policyAt? n = T''.policyAt? n) ∧
      HeapValid T''.heap ∧
      T.heap.length ≤ T''.heap.length := by
  by_cases hn : ∃ n, op = .num n
  · obtain ⟨n, hop⟩ := hn
    subst hop
    obtain ⟨fuel', T'', r', h_call, h_vv, h_pol, h_heap, h_mono⟩ :=
      multnExact_CE_num_case_vacuous new fuel ptable level n operands T r T' h_old
    refine ⟨fuel', T'', r', h_call, h_vv, ?_, h_heap, h_mono⟩
    -- The num-case-vacuous result has T'.policyAt? level = T''.policyAt? level
    -- (only at the chosen level), but we need it for all n. The premise is
    -- vacuous (callAsBaseApply on .builtinBaseApply for .num returns none),
    -- so this case is unreachable.
    exfalso
    rw [callAsBaseApply_builtin_num_none] at h_old
    cases h_old
  · have h_op : OpNotNum op := fun n hop_num => hn ⟨n, hop_num⟩
    exact multnExact_CE_nonnum_case h_admit h_fuel h_op hresp_pt h_old install wf
      h_heap_deep h_op_deep h_operands_deep h_levels_deep h_levels_resp
      h_pt_shift h_pol_shift
