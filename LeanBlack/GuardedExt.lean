/-
  lean-sage: Guarded-extension wrappers — the master CE theorem.

  Generalizes the multn certificate machinery (`Policies.lean`) from
  the single `num?`-guarded wrapper to the *family* of guarded
  extension wrappers:

      (λ (op args). (if (<g> op) <behavior> (orig op args)))

  where `g` is any recognizer primitive. The class-level theorem
  `guardedExt_soundForCE_first_install_tower` proves CE_weak once for
  the whole family; a proposal is admitted with only a per-guard
  `GuardSpec g` — two small lemmas:

    * `total`  — the guard is total and Bool-valued on any operator;
    * `misses` — whenever the guard accepts an operator, the baseline
                 `applyDirect` is undefined on it.

  `misses` is the load-bearing obligation: it confines the new
  behavior to territory the baseline never claimed, which makes the
  guard-true case of CE vacuous (CE only constrains calls the OLD
  semantics answered). The guard-false case delegates to `orig` and
  is discharged by the trace lemma + `applyDirect_heap_extend_weak`,
  exactly as in the multn proof.

  The family has a provable interior boundary: recognizers that
  accept baseline-defined operators can never carry a `GuardSpec`.
  `no_guardSpec_primq` (and `no_guardSpec_closureq`) are the
  machine-checked impossibility results — the `malicious_not_CE`
  analog at family level. A `prim?`-guarded wrapper would redefine
  what `(+ 1 2)` means; the kernel refuses it not because a proof
  was not found but because no proof exists.

  Subsumption: `multnExactPolicy` is the `g := "num?"` instance;
  `multn_admits_guardedExt` + `guardSpec_numq` re-derive the multn
  headline from the master theorem.

  Scope (same honesty as multn): first-install only
  (`oldVal = .builtinBaseApply`); chained installs compose via
  `CE_weak_strong_trans` as before. The family covers *extensions on
  baseline-undefined territory* only — behavior-preserving rewrites
  of defined territory are outside it (that corner needs the open
  logical relation; see `CtxEquiv.lean`).
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Policies

/-! ## The wrapper family -/

/-- Body of a guarded-extension wrapper: test the operator with
    recognizer `g`; on hit run `t` (arbitrary new behavior); on miss
    delegate to `orig`. `multnBody` is `guardedExtBody "num?" ⟨…⟩`. -/
def guardedExtBody (g : String) (t : Expr) : Expr :=
  .ifte (.primApp (.var g) [.var "op"])
        t
        (.primApp (.var "orig") [.var "op", .var "args"])

/-- The closure shape of the family. -/
def GuardedExtShape (g : String) (v : Val) : Prop :=
  ∃ t cenv, v = .closure ["op", "args"] (guardedExtBody g t) cenv

/-! ## Per-guard obligations -/

/-- What a proposer must supply about a recognizer `g` for the master
    theorem to apply. `total` + `misses` are the semantic content;
    the two disequalities are bookkeeping (the wrapper's own binders
    must not shadow the guard). -/
structure GuardSpec (g : String) : Prop where
  ne_op   : g ≠ "op"
  ne_args : g ≠ "args"
  total   : ∀ op : Val, ∃ b, applyPrim g [op] = some (.bool b)
  misses  : ∀ op : Val, applyPrim g [op] = some (.bool true) →
            ∀ fuel ptable level operands T,
              applyDirect fuel ptable level op operands T = none

/-! ## The gate -/

/-- The captured-env checks: `orig` bound to the current base-apply
    (= `oldVal`) and `g` bound to the recognizer primitive. Split out
    of `guardedExtPolicy` so the admission arm stays a flat `&&`. -/
def guardedExtCenvChecks (g : String) (heap : Heap) (oldVal : Val)
    (cenv : Env) : Bool :=
  (match cenv.lookup "orig" with
   | some idx_o =>
       match heap[idx_o]? with
       | some v => v == oldVal
       | _ => false
   | none => false) &&
  (match cenv.lookup g with
   | some idx_g =>
       match heap[idx_g]? with
       | some (.prim p) => p == g
       | _ => false
   | none => false)

/-- The proof-bearing policy for the family at guard `g`: admits a
    closure of the exact guarded-extension shape whose captured env
    passes `guardedExtCenvChecks`. Mirrors `multnExactPolicy`. -/
def guardedExtPolicy (g : String) : BlackPolicy := fun ctx oldVal new =>
  (ctx.target == "base-apply") &&
  (match new with
   | .closure ["op", "args"]
       (.ifte (.primApp (.var pred) [.var "op"])
              _
              (.primApp (.var "orig") [.var "op", .var "args"]))
       cenv =>
       cond (pred == g) (guardedExtCenvChecks g ctx.heap oldVal cenv) false
   | _ => false)

theorem guardedExt_sound_for_shape (g : String) :
    (guardedExtPolicy g).Sound (fun _ new => GuardedExtShape g new) := by
  intro _ _ new h
  unfold guardedExtPolicy at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h_shape⟩ := h
  split at h_shape
  · rename_i pred t cenv
    cases hpred : pred == g with
    | false => rw [hpred] at h_shape; cases h_shape
    | true =>
        have h_pred : pred = g := eq_of_beq hpred
        subst h_pred
        exact ⟨t, cenv, rfl⟩
  · simp at h_shape

/-! ## Install-protocol facts -/

/-- The closure's captured env binds `g` to the recognizer primitive
    `.prim g`. Generalizes `NumQBoundIn`. -/
def PrimBoundIn (g : String) (heap : Heap) (new : Val) : Prop :=
  ∃ ps body cenv idx,
    new = .closure ps body cenv ∧
    cenv.lookup g = some idx ∧
    heap[idx]? = some (.prim g)

/-- Install-time facts for a guarded-extension admission. -/
structure GuardedInstallFacts (g : String) (oldVal new : Val) (heap : Heap) : Prop where
  orig  : OrigBoundIn heap oldVal new
  guard : PrimBoundIn g heap new

/-- Bridge: the gate's admission implies the install facts. -/
theorem guardedExtPolicy_implies_InstallFacts
    {g : String} {ctx : MutationCtx} {oldVal new : Val}
    (h : guardedExtPolicy g ctx oldVal new = true) :
    ctx.target = "base-apply" ∧ GuardedInstallFacts g oldVal new ctx.heap := by
  have shape : GuardedExtShape g new :=
    guardedExt_sound_for_shape g ctx oldVal new h
  obtain ⟨t, cenv, h_new_eq⟩ := shape
  subst h_new_eq
  unfold guardedExtPolicy at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h_tgt', h_rest⟩ := h
  have h_tgt : ctx.target = "base-apply" := by simpa using h_tgt'
  -- The concrete closure iota-reduces the admission match (defeq), and
  -- `cond (g == g) X false` rewrites to `X` via `beq_self_eq_true`.
  have h_rest' : cond (g == g)
      (guardedExtCenvChecks g ctx.heap oldVal cenv) false = true := h_rest
  rw [beq_self_eq_true] at h_rest'
  have h_checks : guardedExtCenvChecks g ctx.heap oldVal cenv = true := h_rest'
  unfold guardedExtCenvChecks at h_checks
  simp only [Bool.and_eq_true] at h_checks
  obtain ⟨h_orig, h_guard⟩ := h_checks
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
  have guard_facts :
      ∃ idx_g, cenv.lookup g = some idx_g ∧
               ctx.heap[idx_g]? = some (.prim g) := by
    cases h_lookup : cenv.lookup g with
    | none => simp [h_lookup] at h_guard
    | some idx_g =>
        simp only [h_lookup] at h_guard
        cases h_heap : ctx.heap[idx_g]? with
        | none => simp [h_heap] at h_guard
        | some v =>
            simp only [h_heap] at h_guard
            cases v with
            | prim name =>
                have : name = g := by simpa using h_guard
                subst this
                exact ⟨idx_g, rfl, h_heap⟩
            | num _ => simp at h_guard
            | bool _ => simp at h_guard
            | nilV => simp at h_guard
            | sym _ => simp at h_guard
            | cons _ _ => simp at h_guard
            | builtinBaseApply => simp at h_guard
            | closure _ _ _ => simp at h_guard
  obtain ⟨idx_o, h_lookup_o, h_heap_o⟩ := orig_facts
  obtain ⟨idx_g, h_lookup_g, h_heap_g⟩ := guard_facts
  refine ⟨h_tgt, ?_, ?_⟩
  · exact ⟨_, _, _, idx_o, rfl, h_lookup_o, h_heap_o⟩
  · exact ⟨_, _, _, idx_g, rfl, h_lookup_g, h_heap_g⟩

/-! ## The closure-body trace lemma (guard-false case)

    Mirror of `multn_closure_body_unfolds` with the recognizer
    abstracted: the guard's verdict on `op` arrives as the hypothesis
    `h_gfalse` instead of the `num?`-specific lemma. -/
theorem guardedExt_closure_body_unfolds
    (g : String) (h_ne_op : g ≠ "op") (h_ne_args : g ≠ "args")
    (fuel : Nat) (h_fuel : fuel ≥ 2)
    (ptable : PolicyTable) (level : Nat)
    (op : Val) (h_gfalse : applyPrim g [op] = some (.bool false))
    (operands : List Val)
    (t : Expr) (cenv : Env) (idx_o idx_g : Nat)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_lookup_g : cenv.lookup g = some idx_g)
    (T : TowerState)
    (h_heap_o : (T.heap ++ [op, listToVal operands])[idx_o]? =
                some .builtinBaseApply)
    (h_heap_g : (T.heap ++ [op, listToVal operands])[idx_g]? =
                some (.prim g)) :
    callAsBaseApply (fuel + 4) ptable level
      (.closure ["op", "args"] (guardedExtBody g t) cenv) op operands T
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
  unfold callAsBaseApply guardedExtBody
  simp only [applyDirect, allocStep, Heap.alloc, List.zip, List.zipWith,
             List.foldl, List.length_append, List.length_singleton,
             List.append_assoc, List.cons_append, List.nil_append]
  let env_alloc : Env := Env.cons "args" (T.heap.length + 1)
                          (Env.cons "op" T.heap.length cenv)
  let T_alloc : TowerState :=
    { T with heap := T.heap ++ [op, listToVal operands] }
  show eval (k + 5) ptable level
       (.ifte (.primApp (.var g) [.var "op"]) t
              (.primApp (.var "orig") [.var "op", .var "args"]))
       env_alloc T_alloc
       = applyDirect (k + 2) ptable level op operands T_alloc
  have hl_g : env_alloc.lookup g = some idx_g := by
    show (Env.cons "args" (T.heap.length + 1)
          (Env.cons "op" T.heap.length cenv)).lookup g = _
    rw [env_alloc_lookup_other (s_heap := T.heap) (cenv := cenv) g
          h_ne_args h_ne_op]
    exact h_lookup_g
  have hl_op : env_alloc.lookup "op" = some T.heap.length :=
    env_alloc_lookup_op T.heap cenv
  have hl_args : env_alloc.lookup "args" = some (T.heap.length + 1) :=
    env_alloc_lookup_args T.heap cenv
  have hl_orig : env_alloc.lookup "orig" = some idx_o := by
    show (Env.cons "args" (T.heap.length + 1)
          (Env.cons "op" T.heap.length cenv)).lookup "orig" = _
    rw [env_alloc_lookup_other (s_heap := T.heap) (cenv := cenv) "orig"
          (by decide) (by decide)]
    exact h_lookup_o
  have hp_g : T_alloc.heap[idx_g]? = some (.prim g) := h_heap_g
  have hp_op : T_alloc.heap[T.heap.length]? = some op := h_lookup_op_alloc
  have hp_args : T_alloc.heap[T.heap.length + 1]? = some (listToVal operands) :=
    h_lookup_args_alloc
  have hp_orig : T_alloc.heap[idx_o]? = some .builtinBaseApply := h_heap_o
  -- The cond `(g op)` evaluates to `.bool false` (guard misses op).
  have h_cond : eval (k + 4) ptable level (.primApp (.var g) [.var "op"])
        env_alloc T_alloc
        = some (.bool false, T_alloc) := by
    simp only [eval, evalList, applyDirect, hl_g, hp_g, hl_op, hp_op, h_gfalse]
  -- Else branch → applyDirect builtinBaseApply [op, listToVal operands]
  --             → applyDirect op operands.
  have h_else : eval (k + 4) ptable level
        (.primApp (.var "orig") [.var "op", .var "args"])
        env_alloc T_alloc
        = applyDirect (k + 2) ptable level op operands T_alloc := by
    simp only [eval, evalList, applyDirect, hl_orig, hp_orig, hl_op, hp_op,
               hl_args, hp_args, valToList_listToVal]
  unfold eval
  simp only []
  rw [h_cond]
  exact h_else

/-! ## The guard-false case (substantive trace + framing) -/

theorem guardedExt_CE_guardfalse_case
    {g : String} (h_ne_op : g ≠ "op") (h_ne_args : g ≠ "args")
    {new : Val} {ctx : MutationCtx}
    (h_admit : guardedExtPolicy g ctx .builtinBaseApply new = true)
    {fuel : Nat} (h_fuel : fuel ≥ 2)
    {ptable : PolicyTable} {level : Nat} {op : Val}
    (h_gfalse : applyPrim g [op] = some (.bool false))
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    {operands : List Val} {T : TowerState}
    {r : Val} {T' : TowerState}
    (h_old : callAsBaseApply fuel ptable level .builtinBaseApply op operands T
        = some (r, T'))
    (install : GuardedInstallFacts g .builtinBaseApply new T.heap)
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
  obtain ⟨h_orig, h_guard⟩ := install
  obtain ⟨h_heap, h_levels_valid, _hv_cenv, hv_op, hv_operands⟩ := wf
  -- new is guarded-extension-shaped.
  have shape : GuardedExtShape g new :=
    guardedExt_sound_for_shape g ctx .builtinBaseApply new h_admit
  obtain ⟨t, cenv, h_eq⟩ := shape
  subst h_eq
  -- Extract orig's index.
  obtain ⟨ps_o, body_o, cenv_o, idx_o, h_eq_o, h_lookup_o, h_heap_o⟩ := h_orig
  injection h_eq_o with hps_eq hbody_eq hcenv_eq
  subst hps_eq; subst hbody_eq; subst hcenv_eq
  -- Extract the guard's index.
  obtain ⟨_, _, _, idx_g, hnew_eq, h_lookup_g, h_heap_g⟩ := h_guard
  injection hnew_eq with _ _ hcenv_eq2
  subst hcenv_eq2
  -- callAsBaseApply on .builtinBaseApply reduces to applyDirect.
  have h_app : applyDirect fuel ptable level op operands T = some (r, T') := by
    unfold callAsBaseApply at h_old; exact h_old
  -- Heap-index validity.
  have h_idx_o_lt : idx_o < T.heap.length := by
    have := List.getElem?_eq_some_iff.mp h_heap_o
    obtain ⟨h, _⟩ := this; exact h
  have h_idx_g_lt : idx_g < T.heap.length := by
    have := List.getElem?_eq_some_iff.mp h_heap_g
    obtain ⟨h, _⟩ := this; exact h
  -- Heap lookups in the alloc'd state (left half of append).
  have h_lookup_orig_alloc :
      (T.heap ++ [op, listToVal operands])[idx_o]? = some .builtinBaseApply := by
    rw [List.getElem?_append_left h_idx_o_lt]; exact h_heap_o
  have h_lookup_guard_alloc :
      (T.heap ++ [op, listToVal operands])[idx_g]? = some (.prim g) := by
    rw [List.getElem?_append_left h_idx_g_lt]; exact h_heap_g
  -- Trace: callAsBaseApply (fuel+4) on the wrapper → applyDirect fuel.
  have h_trace := guardedExt_closure_body_unfolds g h_ne_op h_ne_args
    fuel h_fuel ptable level op h_gfalse operands
    t cenv idx_o idx_g h_lookup_o h_lookup_g T
    h_lookup_orig_alloc h_lookup_guard_alloc
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

/-! ## The master theorem -/

/-- **The master theorem.** Any admitted guarded-extension wrapper
    whose guard carries a `GuardSpec` conservatively extends the
    builtin base-apply (first install). Guard-true calls are outside
    CE's jurisdiction because `spec.misses` makes the old semantics
    undefined there; guard-false calls delegate to `orig` and
    reproduce the old result. `multnExact_soundForCE_first_install_tower`
    is the `g := "num?"` instance. -/
theorem guardedExt_soundForCE_first_install_tower
    {g : String} (spec : GuardSpec g)
    {new : Val} {ctx : MutationCtx}
    (h_admit : guardedExtPolicy g ctx .builtinBaseApply new = true)
    {fuel : Nat} (h_fuel : fuel ≥ 2)
    {ptable : PolicyTable} {level : Nat} {op : Val}
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    {operands : List Val} {T : TowerState}
    {r : Val} {T' : TowerState}
    (h_old : callAsBaseApply fuel ptable level .builtinBaseApply op operands T
        = some (r, T'))
    (install : GuardedInstallFacts g .builtinBaseApply new T.heap)
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
  obtain ⟨b, h_g⟩ := spec.total op
  cases b with
  | true =>
      -- Guard hits ⇒ baseline undefined ⇒ the premise is impossible.
      exfalso
      have h_none := spec.misses op h_g fuel ptable level operands T
      unfold callAsBaseApply at h_old
      rw [h_none] at h_old
      cases h_old
  | false =>
      exact guardedExt_CE_guardfalse_case spec.ne_op spec.ne_args
        h_admit h_fuel h_g hresp_pt h_old install wf
        h_heap_deep h_op_deep h_operands_deep h_levels_deep h_levels_resp
        h_pt_shift h_pol_shift

/-! ## Guard instances: what a proposal costs -/

theorem applyDirect_bool_returns_none (fuel : Nat) (ptable : PolicyTable)
    (level : Nat) (b : Bool) (operands : List Val) (T : TowerState) :
    applyDirect fuel ptable level (.bool b) operands T = none := by
  cases fuel with
  | zero => simp [applyDirect]
  | succ k => simp [applyDirect]

theorem applyDirect_nil_returns_none (fuel : Nat) (ptable : PolicyTable)
    (level : Nat) (operands : List Val) (T : TowerState) :
    applyDirect fuel ptable level .nilV operands T = none := by
  cases fuel with
  | zero => simp [applyDirect]
  | succ k => simp [applyDirect]

/-- The multn guard, re-derived: `num?` misses everything the baseline
    defines. This is the entire per-proposal cost for `num?`. -/
theorem guardSpec_numq : GuardSpec "num?" where
  ne_op := by decide
  ne_args := by decide
  total := by
    intro op
    show ∃ b, applyPrim_numQ [op] = some (.bool b)
    cases op <;> exact ⟨_, rfl⟩
  misses := by
    intro op h_true fuel ptable level operands T
    have : ∃ n, op = .num n := by
      cases op with
      | num n => exact ⟨n, rfl⟩
      | bool _ => simp [applyPrim, applyPrim_numQ] at h_true
      | nilV => simp [applyPrim, applyPrim_numQ] at h_true
      | cons _ _ => simp [applyPrim, applyPrim_numQ] at h_true
      | sym _ => simp [applyPrim, applyPrim_numQ] at h_true
      | closure _ _ _ => simp [applyPrim, applyPrim_numQ] at h_true
      | prim _ => simp [applyPrim, applyPrim_numQ] at h_true
      | builtinBaseApply => simp [applyPrim, applyPrim_numQ] at h_true
    obtain ⟨n, rfl⟩ := this
    exact applyDirect_num_returns_none fuel ptable level n operands T

/-- A genuinely new guard: `bool?`. Same two-lemma cost. -/
theorem guardSpec_boolq : GuardSpec "bool?" where
  ne_op := by decide
  ne_args := by decide
  total := by
    intro op
    show ∃ b, applyPrim_boolQ [op] = some (.bool b)
    cases op <;> exact ⟨_, rfl⟩
  misses := by
    intro op h_true fuel ptable level operands T
    have : ∃ b, op = .bool b := by
      cases op with
      | bool b => exact ⟨b, rfl⟩
      | num _ => simp [applyPrim, applyPrim_boolQ] at h_true
      | nilV => simp [applyPrim, applyPrim_boolQ] at h_true
      | cons _ _ => simp [applyPrim, applyPrim_boolQ] at h_true
      | sym _ => simp [applyPrim, applyPrim_boolQ] at h_true
      | closure _ _ _ => simp [applyPrim, applyPrim_boolQ] at h_true
      | prim _ => simp [applyPrim, applyPrim_boolQ] at h_true
      | builtinBaseApply => simp [applyPrim, applyPrim_boolQ] at h_true
    obtain ⟨b, rfl⟩ := this
    exact applyDirect_bool_returns_none fuel ptable level b operands T

/-- `null?` too, for good measure. -/
theorem guardSpec_nullq : GuardSpec "null?" where
  ne_op := by decide
  ne_args := by decide
  total := by
    intro op
    show ∃ b, applyPrim_nullQ [op] = some (.bool b)
    cases op <;> exact ⟨_, rfl⟩
  misses := by
    intro op h_true fuel ptable level operands T
    have : op = .nilV := by
      cases op with
      | nilV => rfl
      | num _ => simp [applyPrim, applyPrim_nullQ] at h_true
      | bool _ => simp [applyPrim, applyPrim_nullQ] at h_true
      | cons _ _ => simp [applyPrim, applyPrim_nullQ] at h_true
      | sym _ => simp [applyPrim, applyPrim_nullQ] at h_true
      | closure _ _ _ => simp [applyPrim, applyPrim_nullQ] at h_true
      | prim _ => simp [applyPrim, applyPrim_nullQ] at h_true
      | builtinBaseApply => simp [applyPrim, applyPrim_nullQ] at h_true
    subst this
    exact applyDirect_nil_returns_none fuel ptable level operands T

/-! ## The boundary: guards that can never carry a spec

    A `prim?`-guarded wrapper would intercept every primitive
    application — `(+ 1 2)` would flow into the new behavior. No
    `GuardSpec "prim?"` exists, because the baseline is *defined* on
    primitive operators. The refusal is an impossibility, not a
    missing proof. -/
theorem no_guardSpec_primq : ¬ GuardSpec "prim?" := by
  intro spec
  have h_true : applyPrim "prim?" [Val.prim "+"] = some (.bool true) := by
    simp [applyPrim, applyPrim_primQ]
  have h_none := spec.misses (.prim "+") h_true 1 [] 0 [.num 1, .num 2] initTower
  have h_some : applyDirect 1 [] 0 (.prim "+") [.num 1, .num 2] initTower
      = some (.num 3, initTower) := by
    simp [applyDirect, applyPrim, applyPrim_plus]
  rw [h_some] at h_none
  cases h_none

/-- Same impossibility for `closure?`: it would hijack ordinary
    function application. -/
theorem no_guardSpec_closureq : ¬ GuardSpec "closure?" := by
  intro spec
  -- The identity closure applied to one argument succeeds under the
  -- baseline (fuel 2: one step for applyDirect, one for the body var).
  have h_true : applyPrim "closure?" [Val.closure ["x"] (.var "x") .nil]
      = some (.bool true) := by
    simp [applyPrim, applyPrim_closureQ]
  have h_none := spec.misses (.closure ["x"] (.var "x") .nil) h_true
    2 [] 0 [.nilV] ⟨[], []⟩
  have h_some : applyDirect 2 [] 0 (.closure ["x"] (.var "x") .nil)
      [.nilV] (⟨[], []⟩ : TowerState)
      = some (.nilV, ⟨[.nilV], []⟩) := by
    simp [applyDirect, allocStep, Heap.alloc, eval, Env.lookup]
  rw [h_some] at h_none
  cases h_none

/-! ## Subsumption: multn is the `num?` instance -/

/-- The multn gate implies the family gate at `g := "num?"`: every
    modification `multnExactPolicy` admits, `guardedExtPolicy "num?"`
    admits. With `guardSpec_numq`, the master theorem therefore
    re-derives `multnExact_soundForCE_first_install_tower`. -/
theorem multn_admits_guardedExt
    (ctx : MutationCtx) (oldVal new : Val)
    (h : multnExactPolicy ctx oldVal new = true) :
    guardedExtPolicy "num?" ctx oldVal new = true := by
  unfold multnExactPolicy at h
  unfold guardedExtPolicy
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨h_tgt, h_shape⟩ := h
  refine ⟨h_tgt, ?_⟩
  split at h_shape
  · rename_i cenv
    simp only [Bool.and_eq_true] at h_shape
    obtain ⟨h_orig, h_numq⟩ := h_shape
    show guardedExtCenvChecks "num?" ctx.heap oldVal cenv = true
    unfold guardedExtCenvChecks
    simp only [Bool.and_eq_true]
    refine ⟨h_orig, ?_⟩
    -- Convert multn's literal `.prim "num?"` match into the family's
    -- `p == "num?"` check.
    cases h_lookup : cenv.lookup "num?" with
    | none => simp [h_lookup] at h_numq
    | some idx =>
        rw [h_lookup] at h_numq
        show (match ctx.heap[idx]? with
              | some (.prim p) => p == "num?"
              | _ => false) = true
        have h_numq' : (match ctx.heap[idx]? with
              | some (.prim "num?") => true
              | _ => false) = true := h_numq
        cases h_heap : ctx.heap[idx]? with
        | none => simp [h_heap] at h_numq'
        | some v =>
            rw [h_heap] at h_numq'
            cases v with
            | prim name =>
                by_cases hname : name = "num?"
                · subst hname; simp
                · simp [hname] at h_numq'
            | num _ => simp at h_numq'
            | bool _ => simp at h_numq'
            | nilV => simp at h_numq'
            | sym _ => simp at h_numq'
            | cons _ _ => simp at h_numq'
            | closure _ _ _ => simp at h_numq'
            | builtinBaseApply => simp at h_numq'
  · simp at h_shape
