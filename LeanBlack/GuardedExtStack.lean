/-
  lean-sage: Stacking guarded-extension wrappers.

  The master theorem (`GuardedExt.lean`) is first-install: it certifies
  a wrapper as a conservative extension of the *builtin* base-apply.
  This file lifts that to a *second* install: a wrapper `W2` (guard
  `g2`) admitted over an already-installed wrapper `W1` (guard `g1`),
  when the two guards are disjoint.

  The key facts, all reused from the first-install machinery:

    * guard-true (g2 fires): `W1` is undefined there. Because g2 fires,
      `g2.misses` makes the baseline undefined on `op`; disjointness
      makes `g1` miss `op`, so `W1` delegates to the baseline — also
      undefined. Proved by running the *existing* builtin trace lemma
      (`guardedExt_closure_body_unfolds`) on `W1` and hitting the
      `g2.misses` contradiction. So the guard-true case is vacuous.

    * guard-false (g2 misses): `W2` delegates to `orig = W1`, and the
      framing lemma (`applyDirect_heap_extend_weak`, polymorphic in the
      operator) reproduces `W1`'s result over the alloc'd heap.

  Composed with `CE_weak_strong_trans`, `W2`-over-`W1` and
  `W1`-over-builtin give `W2`-over-builtin: the whole stack is a
  conservative extension of the baseline, and both admitted behaviors
  live at once (see `DemoStack.lean`).

  Scope: two disjoint single-guard installs. n-way stacking is the same
  argument iterated (each new guard disjoint from all installed ones);
  not mechanized here.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.Bisim
import LeanBlack.Frame
import LeanBlack.Policies
import LeanBlack.EvalFuelMono
import LeanBlack.GuardedExt
import LeanBlack.HeapAgree
import LeanBlack.IdentityDelegate

set_option linter.unusedSimpArgs false

namespace LeanBlack

/-! ## Decidability of `EnvDeep` / `ValDeep`

    Structural, so a concrete wrapper's deepness (`ValDeep W1 heap`) is
    `native_decide`-able — needed to discharge the stack theorem's one
    non-derivable hypothesis in `DemoStack`. -/

instance decEnvDeep : (env : Env) → (h : Heap) → Decidable (EnvDeep env h)
  | .nil,             _ => isTrue trivial
  | .cons _ idx rest, h =>
      if hlt : idx < h.length then
        match decEnvDeep rest h with
        | isTrue ht => isTrue ⟨hlt, ht⟩
        | isFalse hf => isFalse (fun h' => hf h'.2)
      else isFalse (fun h' => hlt h'.1)

instance decValDeep : (v : Val) → (h : Heap) → Decidable (ValDeep v h)
  | .num _,            _ => isTrue trivial
  | .bool _,           _ => isTrue trivial
  | .nilV,             _ => isTrue trivial
  | .sym _,            _ => isTrue trivial
  | .prim _,           _ => isTrue trivial
  | .builtinBaseApply, _ => isTrue trivial
  | .cons x y,         h =>
      match decValDeep x h, decValDeep y h with
      | isTrue hx, isTrue hy => isTrue ⟨hx, hy⟩
      | isFalse hx, _        => isFalse (fun h' => hx h'.1)
      | _,         isFalse hy => isFalse (fun h' => hy h'.2)
  | .closure _ _ cenv, h => decEnvDeep cenv h

/-! ## Disjoint guards -/

/-- Two recognizer guards never accept the same operator. -/
def GuardsDisjoint (g1 g2 : String) : Prop :=
  ∀ op : Val, applyPrim g1 [op] = some (.bool true) →
              applyPrim g2 [op] = some (.bool true) → False

/-- From disjointness plus `g1`'s totality: if `g2` fires on `op`,
    `g1` misses it. -/
theorem guard_miss_of_disjoint {g1 g2 : String}
    (spec1 : GuardSpec g1) (disj : GuardsDisjoint g1 g2)
    {op : Val} (h_g2 : applyPrim g2 [op] = some (.bool true)) :
    applyPrim g1 [op] = some (.bool false) := by
  obtain ⟨b, hb⟩ := spec1.total op
  cases b with
  | false => exact hb
  | true => exact absurd h_g2 (fun h => (disj op hb h).elim)

/-- `num?` and `bool?` are disjoint: no value is both a number and a
    boolean. The concrete disjointness the multn ⊕ bool-selector stack
    needs. -/
theorem guardsDisjoint_num_bool : GuardsDisjoint "num?" "bool?" := by
  intro op h1 h2
  cases op <;>
    simp_all [applyPrim, applyPrim_numQ, applyPrim_boolQ]

/-! ## The closure-`orig` trace lemma (guard-false case, second install)

    Mirror of `guardedExt_closure_body_unfolds`, but the wrapper's
    `orig` is bound to a *closure* `W1` rather than `.builtinBaseApply`.
    The else-branch `(orig op args)` therefore delegates to `W1`
    applied to `[op, listToVal operands]` — i.e. to
    `callAsBaseApply … W1 op operands` — instead of unwrapping to
    `applyDirect … op operands`. One less unwrap step, so the fuel
    lands at `fuel + 1` rather than `fuel`. -/
theorem guardedExt_closure_body_unfolds_over_closure
    (g : String) (h_ne_op : g ≠ "op") (h_ne_args : g ≠ "args")
    (fuel : Nat) (h_fuel : fuel ≥ 2)
    (ptable : PolicyTable) (level : Nat)
    (op : Val) (h_gfalse : applyPrim g [op] = some (.bool false))
    (operands : List Val)
    (t : Expr) (cenv : Env) (idx_o idx_g : Nat)
    (orig : Val)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_lookup_g : cenv.lookup g = some idx_g)
    (T : TowerState)
    (h_heap_o : (T.heap ++ [op, listToVal operands])[idx_o]? = some orig)
    (h_heap_g : (T.heap ++ [op, listToVal operands])[idx_g]? = some (.prim g)) :
    callAsBaseApply (fuel + 4) ptable level
      (.closure ["op", "args"] (guardedExtBody g t) cenv) op operands T
    = applyDirect (fuel + 1) ptable level orig [op, listToVal operands]
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
       = applyDirect (k + 3) ptable level orig [op, listToVal operands] T_alloc
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
  have hp_orig : T_alloc.heap[idx_o]? = some orig := h_heap_o
  have h_cond : eval (k + 4) ptable level (.primApp (.var g) [.var "op"])
        env_alloc T_alloc
        = some (.bool false, T_alloc) := by
    simp only [eval, evalList, applyDirect, hl_g, hp_g, hl_op, hp_op, h_gfalse]
  have h_else : eval (k + 4) ptable level
        (.primApp (.var "orig") [.var "op", .var "args"])
        env_alloc T_alloc
        = applyDirect (k + 3) ptable level orig [op, listToVal operands] T_alloc := by
    simp only [eval, evalList, applyDirect, hl_orig, hp_orig, hl_op, hp_op,
               hl_args, hp_args]
  unfold eval
  simp only []
  rw [h_cond]
  exact h_else

/-! ## Guard-true vacuity: where `g2` fires, `W1` cannot succeed

    If `g2` fires on `op`, a successful call through the *first* wrapper
    `W1` (guard `g1`, delegating to the builtin) is impossible. Because
    `g2` firing makes the baseline undefined on `op` (`spec2.misses`),
    and disjointness makes `g1` miss `op`, so `W1` takes its delegate
    branch straight to that undefined baseline. Proved by running the
    builtin trace lemma on `W1` (after bumping fuel past the unfold
    threshold) and colliding with `spec2.misses`. -/
theorem stack_vacuous_of_guard2_fires
    {g1 g2 : String} (spec1 : GuardSpec g1) (spec2 : GuardSpec g2)
    (disj : GuardsDisjoint g1 g2)
    {op : Val} (h_g2 : applyPrim g2 [op] = some (.bool true))
    (t1 : Expr) (cenv1 : Env) (idx_o1 idx_g1 : Nat)
    {fuel : Nat} {ptable : PolicyTable} {level : Nat} {operands : List Val}
    {T : TowerState} {r : Val} {T' : TowerState}
    (h_heap_o1 : (T.heap ++ [op, listToVal operands])[idx_o1]?
                    = some .builtinBaseApply)
    (h_heap_g1 : (T.heap ++ [op, listToVal operands])[idx_g1]? = some (.prim g1))
    (h_lookup_o1 : cenv1.lookup "orig" = some idx_o1)
    (h_lookup_g1 : cenv1.lookup g1 = some idx_g1)
    (h_call : callAsBaseApply fuel ptable level
                (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1)
                op operands T = some (r, T')) :
    False := by
  have h_g1_miss : applyPrim g1 [op] = some (.bool false) :=
    guard_miss_of_disjoint spec1 disj h_g2
  -- Success through W1 = applyDirect on the closure.
  have h_ad : applyDirect fuel ptable level
      (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1)
      [op, listToVal operands] T = some (r, T') := by
    simpa only [callAsBaseApply] using h_call
  -- Bump fuel past the unfold threshold (need ≥ 6 so F-4 ≥ 2).
  obtain ⟨F, h_fuel_le, h_F6⟩ : ∃ F, fuel ≤ F ∧ 6 ≤ F :=
    ⟨fuel + 6, by omega, by omega⟩
  have h_adF : applyDirect F ptable level
      (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1)
      [op, listToVal operands] T = some (r, T') :=
    applyDirect_fuel_mono h_fuel_le h_ad
  have h_callF : callAsBaseApply F ptable level
      (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1) op operands T
      = some (r, T') := by simpa only [callAsBaseApply] using h_adF
  -- Run the builtin trace lemma on W1 at fuel (F-4).
  obtain ⟨m, hm⟩ : ∃ m, F = m + 4 := ⟨F - 4, by omega⟩
  have h_m2 : m ≥ 2 := by omega
  rw [hm] at h_callF
  have h_trace := guardedExt_closure_body_unfolds g1 spec1.ne_op spec1.ne_args
    m h_m2 ptable level op h_g1_miss operands t1 cenv1 idx_o1 idx_g1
    h_lookup_o1 h_lookup_g1 T h_heap_o1 h_heap_g1
  rw [h_trace] at h_callF
  -- But the baseline is undefined on op (g2 fires).
  have h_none := spec2.misses op h_g2 m ptable level operands
    { T with heap := T.heap ++ [op, listToVal operands] }
  rw [h_none] at h_callF
  cases h_callF

/-! ## The second-install certificate

    `W2` (guard `g2`) conservatively extends `W1` (guard `g1`) when the
    guards are disjoint. Selective form (`CE_weak_strong_at`) pinning
    the four cells the proof reads: `W2`'s captured `orig`/`g2` and
    `W1`'s captured `orig`/`g1`. -/
theorem guardedExt_stack_soundForCE_weak_strong_at
    {g1 g2 : String} (spec1 : GuardSpec g1) (spec2 : GuardSpec g2)
    (disj : GuardsDisjoint g1 g2)
    (level : Nat) (h_ref : Heap)
    (t1 t2 : Expr) (cenv1 cenv2 : Env) (idx_o1 idx_g1 idx_o2 idx_g2 : Nat)
    (W1 W2 : Val)
    (hW1 : W1 = .closure ["op", "args"] (guardedExtBody g1 t1) cenv1)
    (hW2 : W2 = .closure ["op", "args"] (guardedExtBody g2 t2) cenv2)
    (h_lk_o2 : cenv2.lookup "orig" = some idx_o2)
    (h_lk_g2 : cenv2.lookup g2 = some idx_g2)
    (h_cell_o2 : h_ref[idx_o2]? = some W1)
    (h_cell_g2 : h_ref[idx_g2]? = some (.prim g2))
    (h_lk_o1 : cenv1.lookup "orig" = some idx_o1)
    (h_lk_g1 : cenv1.lookup g1 = some idx_g1)
    (h_cell_o1 : h_ref[idx_o1]? = some .builtinBaseApply)
    (h_cell_g1 : h_ref[idx_g1]? = some (.prim g1))
    (hd_W1 : ValDeep W1 h_ref) :
    CE_weak_strong_at level [idx_o2, idx_g2, idx_o1, idx_g1] h_ref W1 W2 := by
  intro fuel ptable op operands T r T'
    h_len h_agree
    h_heap h_op h_operands h_valid_old _h_valid_new
    h_ptable _h_lvl_pol h_env h_pol _h_env_bisim
    h_heap_deep h_op_deep h_operands_deep h_env_deep
    h_pt_shift h_pol_shift h_call
  subst hW1; subst hW2
  -- Transport the four install cells from h_ref to T.heap.
  have a_o2 : T.heap[idx_o2]? = some (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1) := by
    rw [← h_agree idx_o2 (by simp)]; exact h_cell_o2
  have a_g2 : T.heap[idx_g2]? = some (.prim g2) := by
    rw [← h_agree idx_g2 (by simp)]; exact h_cell_g2
  have a_o1 : T.heap[idx_o1]? = some .builtinBaseApply := by
    rw [← h_agree idx_o1 (by simp)]; exact h_cell_o1
  have a_g1 : T.heap[idx_g1]? = some (.prim g1) := by
    rw [← h_agree idx_g1 (by simp)]; exact h_cell_g1
  -- Append-left to the alloc'd heap.
  have lt_o2 := getElem?_some_lt_length a_o2
  have lt_g2 := getElem?_some_lt_length a_g2
  have lt_o1 := getElem?_some_lt_length a_o1
  have lt_g1 := getElem?_some_lt_length a_g1
  have alloc_o2 : (T.heap ++ [op, listToVal operands])[idx_o2]?
      = some (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1) := by
    rw [List.getElem?_append_left lt_o2]; exact a_o2
  have alloc_g2 : (T.heap ++ [op, listToVal operands])[idx_g2]? = some (.prim g2) := by
    rw [List.getElem?_append_left lt_g2]; exact a_g2
  have alloc_o1 : (T.heap ++ [op, listToVal operands])[idx_o1]? = some .builtinBaseApply := by
    rw [List.getElem?_append_left lt_o1]; exact a_o1
  have alloc_g1 : (T.heap ++ [op, listToVal operands])[idx_g1]? = some (.prim g1) := by
    rw [List.getElem?_append_left lt_g1]; exact a_g1
  -- g2's verdict on op decides which case we are in.
  obtain ⟨b2, hb2⟩ := spec2.total op
  cases b2 with
  | true =>
      exact (stack_vacuous_of_guard2_fires spec1 spec2 disj hb2
        t1 cenv1 idx_o1 idx_g1 alloc_o1 alloc_g1 h_lk_o1 h_lk_g1 h_call).elim
  | false =>
      -- fuel ≥ 2: a closure old-call cannot succeed with less.
      obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 2 := by
        match fuel with
        | 0 => simp [callAsBaseApply, applyDirect] at h_call
        | 1 =>
            exact absurd h_call (by
              simp [callAsBaseApply, applyDirect, allocStep, Heap.alloc,
                    List.zip, List.zipWith, List.foldl, eval, ite_self])
        | k + 2 => exact ⟨k, rfl⟩
      -- Old call through W1 = applyDirect on the closure.
      have h_ad_old : applyDirect (k + 2) ptable level
          (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1)
          [op, listToVal operands] T = some (r, T') := by
        simpa only [callAsBaseApply] using h_call
      -- Frame that call over the alloc'd cells.
      have hlist : ListValValid [op, listToVal operands] T.heap :=
        ⟨h_op, ValValid_listToVal h_operands, trivial⟩
      have hlist_deep : ListValDeep [op, listToVal operands] T.heap :=
        ⟨h_op_deep, ValDeep_listToVal h_operands_deep, trivial⟩
      have hd_W1_T : ValDeep (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1) T.heap :=
        ValDeep.length_mono hd_W1 h_len
      obtain ⟨r_b, T_b', h_appb, h_vvr, h_heapv, h_stateeq, h_mono⟩ :=
        applyDirect_heap_extend_weak h_ptable h_heap h_valid_old hlist
          h_env h_pol h_ad_old [op, listToVal operands] hlist
          h_heap_deep hd_W1_T hlist_deep h_env_deep h_pt_shift h_pol_shift
      -- Bump to fuel (k+3) to match the new trace lemma.
      have h_appb' : applyDirect (k + 3) ptable level
          (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1)
          [op, listToVal operands]
          { T with heap := T.heap ++ [op, listToVal operands] } = some (r_b, T_b') :=
        applyDirect_fuel_mono (by omega) h_appb
      -- The new (closure-orig) trace: W2 delegates to W1.
      have h_trace := guardedExt_closure_body_unfolds_over_closure g2
        spec2.ne_op spec2.ne_args (k + 2) (by omega) ptable level op hb2 operands
        t2 cenv2 idx_o2 idx_g2
        (.closure ["op", "args"] (guardedExtBody g1 t1) cenv1)
        h_lk_o2 h_lk_g2 T alloc_o2 alloc_g2
      have h_new_call : callAsBaseApply ((k + 2) + 4) ptable level
          (.closure ["op", "args"] (guardedExtBody g2 t2) cenv2) op operands T
          = some (r_b, T_b') := by
        rw [h_trace]; exact h_appb'
      refine ⟨(k + 2) + 4, T_b', r_b, h_new_call, h_vvr, ?_, h_heapv, ?_⟩
      · exact h_stateeq level
      · have : T.heap.length + [op, listToVal operands].length ≤ T_b'.heap.length := h_mono
        omega

/-! ## Demo-facing front end

    The full-prefix `CE_weak_strong` for a second install, derived from
    two ordinary `guardedExtPolicy` admissions (both `native_decide`-
    able on concrete probe values) plus `ValDeep` of the installed
    wrapper. The install facts and closure shapes are recovered from
    the admissions exactly as in `guardedExtApproval`. -/
theorem guardedExt_stack_soundForCE
    {g1 g2 : String} (spec1 : GuardSpec g1) (spec2 : GuardSpec g2)
    (disj : GuardsDisjoint g1 g2)
    (level : Nat) (h_ref : Heap) (env metaEnv : Env) (index : Nat)
    (W1 W2 : Val)
    (h_admit1 : guardedExtPolicy g1
                  { target := "base-apply", heap := h_ref, env := env,
                    metaEnv := metaEnv, index := index, level := level }
                  .builtinBaseApply W1 = true)
    (h_admit2 : guardedExtPolicy g2
                  { target := "base-apply", heap := h_ref, env := env,
                    metaEnv := metaEnv, index := index, level := level }
                  W1 W2 = true)
    (hd_W1 : ValDeep W1 h_ref) :
    CE_weak_strong level h_ref W1 W2 := by
  -- Shapes.
  obtain ⟨t1, cenv1, hW1⟩ := guardedExt_sound_for_shape g1 _ _ _ h_admit1
  obtain ⟨t2, cenv2, hW2⟩ := guardedExt_sound_for_shape g2 _ _ _ h_admit2
  -- Install facts.
  obtain ⟨_, if1⟩ := guardedExtPolicy_implies_InstallFacts h_admit1
  obtain ⟨_, if2⟩ := guardedExtPolicy_implies_InstallFacts h_admit2
  -- W1's orig/guard cells (reconciling the generic closure with the shape).
  obtain ⟨ps_o1, b_o1, c_o1, idx_o1, heq_o1, lk_o1, cell_o1⟩ := if1.orig
  obtain ⟨ps_g1, b_g1, c_g1, idx_g1, heq_g1, lk_g1, cell_g1⟩ := if1.guard
  obtain ⟨ps_o2, b_o2, c_o2, idx_o2, heq_o2, lk_o2, cell_o2⟩ := if2.orig
  obtain ⟨ps_g2, b_g2, c_g2, idx_g2, heq_g2, lk_g2, cell_g2⟩ := if2.guard
  -- Reconcile cenv from each install fact with the shape's cenv.
  rw [hW1] at heq_o1 heq_g1
  rw [hW2] at heq_o2 heq_g2
  injection heq_o1 with _ _ hc_o1; subst hc_o1
  injection heq_g1 with _ _ hc_g1; subst hc_g1
  injection heq_o2 with _ _ hc_o2; subst hc_o2
  injection heq_g2 with _ _ hc_g2; subst hc_g2
  -- Bridge selective → full-prefix.
  refine CE_weak_strong_of_at ?_
    (guardedExt_stack_soundForCE_weak_strong_at spec1 spec2 disj level h_ref
      t1 t2 cenv1 cenv2 idx_o1 idx_g1 idx_o2 idx_g2 W1 W2 hW1 hW2
      lk_o2 lk_g2 cell_o2 cell_g2 lk_o1 lk_g1 cell_o1 cell_g1 hd_W1)
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl
  · exact getElem?_some_lt_length cell_o2
  · exact getElem?_some_lt_length cell_g2
  · exact getElem?_some_lt_length cell_o1
  · exact getElem?_some_lt_length cell_g1

end LeanBlack
