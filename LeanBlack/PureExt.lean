/-
  lean-sage: Pure evaluation only *extends* the tower state.

  `StateExtends T T'` captures the structural evolution of a
  `TowerState` under evaluation of a `Pure` expression (no `.set`,
  no `.installPolicy`): the heap grows by appending (no cell is
  ever overwritten), every materialized level's env is preserved
  verbatim, and the number of materialized levels is monotone.

  Why we need it: the contextual-β machinery (`Ctx.lean`,
  `ContextualBeta.lean`) threads state predicates like
  `BuiltinReady` ("level+1 is materialized and its `base-apply`
  cell is the builtin") through the evaluation of a context's
  sibling sub-expressions. `StateExtends` is exactly the
  preservation fact those predicates need: cells survive appends,
  envs survive materialization, level counts only grow.

  ## Joint structure

  The four evaluation functions are mutually recursive, so the
  claim is joint, proved by induction on fuel. Mirrors
  `EvalFuelBump` (`EvalFuelMono.lean`) structurally; purity
  bookkeeping for intermediate states is *consumed* from the
  already-proved `allPureIndep` (`ProofBased.lean`) rather than
  re-proved here.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.ProofBased

namespace LeanBlack

/-! ## The extension relation -/

/-- `T'` structurally extends `T`: the heap is a prefix-extension,
    all materialized envs are preserved, and the level count is
    monotone. This is what evaluation of a `Pure` expression does
    to the state. -/
structure StateExtends (T T' : TowerState) : Prop where
  heap_ext  : ∃ extras, T'.heap = T.heap ++ extras
  envs      : ∀ m e, T.envAt? m = some e → T'.envAt? m = some e
  levels_le : T.levels.length ≤ T'.levels.length

namespace StateExtends

theorem refl (T : TowerState) : StateExtends T T :=
  ⟨⟨[], by simp⟩, fun _ _ h => h, Nat.le_refl _⟩

theorem trans {T₁ T₂ T₃ : TowerState}
    (h₁ : StateExtends T₁ T₂) (h₂ : StateExtends T₂ T₃) :
    StateExtends T₁ T₃ := by
  obtain ⟨⟨ex₁, he₁⟩, hv₁, hl₁⟩ := h₁
  obtain ⟨⟨ex₂, he₂⟩, hv₂, hl₂⟩ := h₂
  exact ⟨⟨ex₁ ++ ex₂, by rw [he₂, he₁, List.append_assoc]⟩,
         fun m e h => hv₂ m e (hv₁ m e h),
         Nat.le_trans hl₁ hl₂⟩

/-- Heap cells are preserved under extension. -/
theorem cell {T T' : TowerState} (h : StateExtends T T')
    {i : Nat} {v : Val} (h_cell : T.heap[i]? = some v) :
    T'.heap[i]? = some v := by
  obtain ⟨extras, h_eq⟩ := h.heap_ext
  have h_lt : i < T.heap.length := (List.getElem?_eq_some_iff.mp h_cell).1
  rw [h_eq, List.getElem?_append_left h_lt]
  exact h_cell

/-- Heap length is monotone under extension. -/
theorem heap_len_le {T T' : TowerState} (h : StateExtends T T') :
    T.heap.length ≤ T'.heap.length := by
  obtain ⟨extras, h_eq⟩ := h.heap_ext
  rw [h_eq, List.length_append]
  exact Nat.le_add_right _ _

/-- Appending to the heap is an extension. -/
theorem of_heap_append (T : TowerState) (extras : Heap) :
    StateExtends T { T with heap := T.heap ++ extras } :=
  ⟨⟨extras, rfl⟩, fun _ _ h => h, Nat.le_refl _⟩

end StateExtends

/-! ## Building blocks: materialize, alloc-folds -/

theorem materializeStep_levels_length (T : TowerState) :
    (materializeStep T).levels.length = T.levels.length + 1 := by
  unfold materializeStep
  simp

private theorem materializeStep_iter_levels_le (T : TowerState) (k : Nat) :
    T.levels.length ≤ (Nat.fold k (fun _ _ T' => materializeStep T') T).levels.length := by
  induction k with
  | zero => simp [Nat.fold]
  | succ k ih =>
      simp only [Nat.fold]
      rw [materializeStep_levels_length]
      omega

theorem TowerState.materialize_levels_le
    {T T' : TowerState} {n : Nat}
    (h_mat : T.materialize n = some T') :
    T.levels.length ≤ T'.levels.length := by
  unfold TowerState.materialize at h_mat
  split at h_mat
  · cases h_mat
  · split at h_mat
    · injection h_mat with h_eq; subst h_eq; exact Nat.le_refl _
    · injection h_mat with h_eq; subst h_eq
      exact materializeStep_iter_levels_le T _

/-- `materialize` is a state extension. -/
theorem StateExtends.of_materialize {T T' : TowerState} {n : Nat}
    (h_mat : T.materialize n = some T') : StateExtends T T' :=
  ⟨TowerState.materialize_heap_extends T T' n h_mat,
   fun m e h => TowerState.materialize_envAt?_preserves T T' n m e h_mat h,
   TowerState.materialize_levels_le h_mat⟩

/-- The closure-call `foldl allocStep` only appends to the heap. -/
theorem foldl_allocStep_heap_extends
    (pairs : List (Val × String)) (h : Heap) (env : Env) :
    ∃ extras, (pairs.foldl allocStep (h, env)).1 = h ++ extras := by
  induction pairs generalizing h env with
  | nil => exact ⟨[], by simp [List.foldl]⟩
  | cons p rest ih =>
      simp only [List.foldl]
      obtain ⟨extras, h_eq⟩ := ih (allocStep (h, env) p).1 (allocStep (h, env) p).2
      refine ⟨[p.1] ++ extras, ?_⟩
      have : (allocStep (h, env) p).1 = h ++ [p.1] := by
        simp [allocStep, Heap.alloc]
      rw [← List.append_assoc, ← this]
      rw [← h_eq]

/-! ## The joint claim -/

/-- Joint claim across the four mutually-recursive evaluation
    functions: on `Pure` inputs over a `PureHeap`, success implies
    the final state extends the initial state. -/
def PureEvalExt (n : Nat) : Prop :=
  (∀ (ptable : PolicyTable) (level : Nat) (e : Expr) (env : Env) (T : TowerState)
       (v : Val) (T' : TowerState),
       Pure e = true → PureHeap T.heap →
       eval n ptable level e env T = some (v, T') → StateExtends T T') ∧
  (∀ (ptable : PolicyTable) (level : Nat) (es : List Expr) (env : Env) (T : TowerState)
       (vs : List Val) (T' : TowerState),
       PureList es = true → PureHeap T.heap →
       evalList n ptable level es env T = some (vs, T') → StateExtends T T') ∧
  (∀ (ptable : PolicyTable) (level : Nat) (op : Val) (args : List Val) (T : TowerState)
       (v : Val) (T' : TowerState),
       PureVal op = true → PureValList args = true → PureHeap T.heap →
       applyVia n ptable level op args T = some (v, T') → StateExtends T T') ∧
  (∀ (ptable : PolicyTable) (level : Nat) (op : Val) (args : List Val) (T : TowerState)
       (v : Val) (T' : TowerState),
       PureVal op = true → PureValList args = true → PureHeap T.heap →
       applyDirect n ptable level op args T = some (v, T') → StateExtends T T')

theorem pureEvalExt_zero : PureEvalExt 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _ _ _ _ _ _ _ h; simp [eval] at h
  · intro _ _ _ _ _ _ _ _ _ h; simp [evalList] at h
  · intro _ _ _ _ _ _ _ _ _ _ h; simp [applyVia] at h
  · intro _ _ _ _ _ _ _ _ _ _ h; simp [applyDirect] at h

theorem pureEvalExt_succ (n : Nat) (IH : PureEvalExt n) :
    PureEvalExt (n + 1) := by
  obtain ⟨IH_eval, IH_evalList, IH_applyVia, IH_applyDirect⟩ := IH
  -- Purity preservation for intermediate states, from allPureIndep.
  have PP := allPureIndep n
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- eval clause
    intro ptable level e env T v T' h_pure h_heap h_some
    cases e with
    | num i =>
        simp only [eval] at h_some
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h_some)
        exact StateExtends.refl T
    | bool b =>
        simp only [eval] at h_some
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h_some)
        exact StateExtends.refl T
    | quote vq =>
        simp only [eval] at h_some
        split at h_some
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h_some)
          exact StateExtends.refl T
        · cases h_some
    | var x =>
        simp only [eval] at h_some
        cases h_lk : env.lookup x with
        | none => simp [h_lk] at h_some
        | some idx =>
            simp only [h_lk] at h_some
            cases h_cell : T.heap[idx]? with
            | none => simp [h_cell] at h_some
            | some v' =>
                simp only [h_cell] at h_some
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h_some)
                exact StateExtends.refl T
    | lam ps body =>
        simp only [eval] at h_some
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h_some)
        exact StateExtends.refl T
    | ifte c t e =>
        simp only [Pure, Bool.and_eq_true] at h_pure
        obtain ⟨⟨h_pc, h_pt⟩, h_pe⟩ := h_pure
        simp only [eval] at h_some
        generalize h_ec : eval n ptable level c env T = ec at h_some
        cases ec with
        | none => simp at h_some
        | some pair =>
            obtain ⟨vc, Tc⟩ := pair
            have h_ext_c := IH_eval ptable level c env T vc Tc h_pc h_heap h_ec
            have h_heap_c : PureHeap Tc.heap :=
              ((PP.1 level c env T h_pc h_heap).2 ptable vc Tc h_ec).2
            cases vc with
            | bool b' =>
                cases b' with
                | true =>
                    simp at h_some
                    exact h_ext_c.trans
                      (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
                | false =>
                    simp at h_some
                    exact h_ext_c.trans
                      (IH_eval ptable level e env Tc v T' h_pe h_heap_c h_some)
            | num _ =>
                simp at h_some
                exact h_ext_c.trans
                  (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
            | nilV =>
                simp at h_some
                exact h_ext_c.trans
                  (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
            | sym _ =>
                simp at h_some
                exact h_ext_c.trans
                  (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
            | cons _ _ =>
                simp at h_some
                exact h_ext_c.trans
                  (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
            | closure _ _ _ =>
                simp at h_some
                exact h_ext_c.trans
                  (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
            | prim _ =>
                simp at h_some
                exact h_ext_c.trans
                  (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
            | builtinBaseApply =>
                simp at h_some
                exact h_ext_c.trans
                  (IH_eval ptable level t env Tc v T' h_pt h_heap_c h_some)
    | app exps =>
        cases exps with
        | nil => simp [eval] at h_some
        | cons f args =>
            simp only [Pure, PureList, Bool.and_eq_true] at h_pure
            obtain ⟨h_pf, h_pargs⟩ := h_pure
            simp only [eval] at h_some
            generalize h_ef : eval n ptable level f env T = ef at h_some
            cases ef with
            | none => simp at h_some
            | some pair =>
                obtain ⟨fv, T₁⟩ := pair
                have h_ext_f := IH_eval ptable level f env T fv T₁ h_pf h_heap h_ef
                obtain ⟨h_pv_f, h_heap₁⟩ :=
                  (PP.1 level f env T h_pf h_heap).2 ptable fv T₁ h_ef
                simp at h_some
                generalize h_el : evalList n ptable level args env T₁ = el at h_some
                cases el with
                | none => simp at h_some
                | some pair' =>
                    obtain ⟨avs, T₂⟩ := pair'
                    have h_ext_l :=
                      IH_evalList ptable level args env T₁ avs T₂ h_pargs h_heap₁ h_el
                    obtain ⟨h_pvs, h_heap₂⟩ :=
                      (PP.2.1 level args env T₁ h_pargs h_heap₁).2 ptable avs T₂ h_el
                    simp at h_some
                    exact (h_ext_f.trans h_ext_l).trans
                      (IH_applyVia ptable level fv avs T₂ v T' h_pv_f h_pvs h_heap₂ h_some)
    | set x e =>
        simp [Pure] at h_pure
    | em b =>
        simp only [Pure] at h_pure
        simp only [eval] at h_some
        cases h_mat : T.materialize (level + 1) with
        | none => simp [h_mat] at h_some
        | some T₁ =>
            simp [h_mat] at h_some
            cases h_env : T₁.envAt? (level + 1) with
            | none => simp [h_env] at h_some
            | some upEnv =>
                simp [h_env] at h_some
                have h_heap₁ : PureHeap T₁.heap :=
                  materialize_preserves_PureHeap h_mat h_heap
                exact (StateExtends.of_materialize h_mat).trans
                  (IH_eval ptable (level+1) b upEnv T₁ v T' h_pure h_heap₁ h_some)
    | primApp f args =>
        simp only [Pure, Bool.and_eq_true] at h_pure
        obtain ⟨h_pf, h_pargs⟩ := h_pure
        simp only [eval] at h_some
        generalize h_ef : eval n ptable level f env T = ef at h_some
        cases ef with
        | none => simp at h_some
        | some pair =>
            obtain ⟨fv, T₁⟩ := pair
            have h_ext_f := IH_eval ptable level f env T fv T₁ h_pf h_heap h_ef
            obtain ⟨h_pv_f, h_heap₁⟩ :=
              (PP.1 level f env T h_pf h_heap).2 ptable fv T₁ h_ef
            simp at h_some
            generalize h_el : evalList n ptable level args env T₁ = el at h_some
            cases el with
            | none => simp at h_some
            | some pair' =>
                obtain ⟨avs, T₂⟩ := pair'
                have h_ext_l :=
                  IH_evalList ptable level args env T₁ avs T₂ h_pargs h_heap₁ h_el
                obtain ⟨h_pvs, h_heap₂⟩ :=
                  (PP.2.1 level args env T₁ h_pargs h_heap₁).2 ptable avs T₂ h_el
                simp at h_some
                exact (h_ext_f.trans h_ext_l).trans
                  (IH_applyDirect ptable level fv avs T₂ v T' h_pv_f h_pvs h_heap₂ h_some)
    | letE x e body =>
        simp only [Pure, Bool.and_eq_true] at h_pure
        obtain ⟨h_pe, h_pbody⟩ := h_pure
        simp only [eval] at h_some
        generalize h_ee : eval n ptable level e env T = ee at h_some
        cases ee with
        | none => simp at h_some
        | some pair =>
            obtain ⟨v_e, T₁⟩ := pair
            have h_ext_e := IH_eval ptable level e env T v_e T₁ h_pe h_heap h_ee
            obtain ⟨h_pv_e, h_heap₁⟩ :=
              (PP.1 level e env T h_pe h_heap).2 ptable v_e T₁ h_ee
            simp only [TowerState.alloc, Heap.alloc] at h_some
            have h_heap₂ : PureHeap (T₁.heap ++ [v_e]) := by
              apply PureHeap_append _ _ h_heap₁
              intro w hw
              simp at hw; subst hw; exact h_pv_e
            have h_ext_alloc := StateExtends.of_heap_append T₁ [v_e]
            exact (h_ext_e.trans h_ext_alloc).trans
              (IH_eval ptable level body (.cons x T₁.heap.length env)
                { T₁ with heap := T₁.heap ++ [v_e] } v T' h_pbody h_heap₂ h_some)
    | seq exps =>
        cases exps with
        | nil =>
            simp only [eval] at h_some
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h_some)
            exact StateExtends.refl T
        | cons e rest =>
            cases rest with
            | nil =>
                simp only [Pure, PureList, Bool.and_eq_true] at h_pure
                simp only [eval] at h_some
                exact IH_eval ptable level e env T v T' h_pure.1 h_heap h_some
            | cons e2 rest2 =>
                simp only [Pure, PureList, Bool.and_eq_true] at h_pure
                obtain ⟨h_pe, h_prest⟩ := h_pure
                simp only [eval] at h_some
                generalize h_ee : eval n ptable level e env T = ee at h_some
                cases ee with
                | none => simp at h_some
                | some pair =>
                    obtain ⟨v_e, T₁⟩ := pair
                    have h_ext_e := IH_eval ptable level e env T v_e T₁ h_pe h_heap h_ee
                    have h_heap₁ : PureHeap T₁.heap :=
                      ((PP.1 level e env T h_pe h_heap).2 ptable v_e T₁ h_ee).2
                    simp at h_some
                    have h_prest' : Pure (.seq (e2 :: rest2)) = true := by
                      simp only [Pure, PureList, Bool.and_eq_true]
                      exact h_prest
                    exact h_ext_e.trans
                      (IH_eval ptable level (.seq (e2 :: rest2)) env T₁ v T'
                        h_prest' h_heap₁ h_some)
    | installPolicy idx =>
        simp [Pure] at h_pure
  · -- evalList clause
    intro ptable level es env T vs T' h_pure h_heap h_some
    cases es with
    | nil =>
        simp only [evalList] at h_some
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h_some)
        exact StateExtends.refl T
    | cons hd tl =>
        simp only [PureList, Bool.and_eq_true] at h_pure
        obtain ⟨h_phd, h_ptl⟩ := h_pure
        simp only [evalList] at h_some
        generalize h_e : eval n ptable level hd env T = e_res at h_some
        cases e_res with
        | none => simp at h_some
        | some pair =>
            obtain ⟨vh, T₁⟩ := pair
            have h_ext_hd := IH_eval ptable level hd env T vh T₁ h_phd h_heap h_e
            have h_heap₁ : PureHeap T₁.heap :=
              ((PP.1 level hd env T h_phd h_heap).2 ptable vh T₁ h_e).2
            simp at h_some
            generalize h_el : evalList n ptable level tl env T₁ = el at h_some
            cases el with
            | none => simp at h_some
            | some pair' =>
                obtain ⟨vts, T₂⟩ := pair'
                have h_ext_tl :=
                  IH_evalList ptable level tl env T₁ vts T₂ h_ptl h_heap₁ h_el
                simp at h_some
                obtain ⟨_, rfl⟩ := h_some
                exact h_ext_hd.trans h_ext_tl
  · -- applyVia clause
    intro ptable level op args T v T' h_pop h_pargs h_heap h_some
    simp only [applyVia] at h_some
    cases h_mat : T.materialize (level + 1) with
    | none => simp [h_mat] at h_some
    | some T₁ =>
        simp [h_mat] at h_some
        have h_ext_mat := StateExtends.of_materialize h_mat
        have h_heap₁ : PureHeap T₁.heap :=
          materialize_preserves_PureHeap h_mat h_heap
        cases h_env : T₁.envAt? (level + 1) with
        | none =>
            simp [h_env] at h_some
            exact h_ext_mat.trans
              (IH_applyDirect ptable level op args T₁ v T' h_pop h_pargs h_heap₁ h_some)
        | some upEnv =>
            simp [h_env] at h_some
            cases h_la : upEnv.lookup "base-apply" with
            | none =>
                simp [h_la] at h_some
                exact h_ext_mat.trans
                  (IH_applyDirect ptable level op args T₁ v T' h_pop h_pargs h_heap₁ h_some)
            | some idx =>
                simp [h_la] at h_some
                cases h_cell : T₁.heap[idx]? with
                | none => simp [h_cell] at h_some
                | some baseApply =>
                    simp [h_cell] at h_some
                    have h_pba : PureVal baseApply = true :=
                      h_heap₁ idx baseApply h_cell
                    have h_pargs' : PureValList [op, listToVal args] = true := by
                      simp only [PureValList, Bool.and_eq_true]
                      exact ⟨h_pop, PureVal_listToVal h_pargs, trivial⟩
                    cases baseApply with
                    | builtinBaseApply =>
                        simp at h_some
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level op args T₁ v T'
                            h_pop h_pargs h_heap₁ h_some)
                    | num _ =>
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level _ [op, listToVal args] T₁ v T'
                            h_pba h_pargs' h_heap₁ h_some)
                    | bool _ =>
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level _ [op, listToVal args] T₁ v T'
                            h_pba h_pargs' h_heap₁ h_some)
                    | nilV =>
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level _ [op, listToVal args] T₁ v T'
                            h_pba h_pargs' h_heap₁ h_some)
                    | sym _ =>
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level _ [op, listToVal args] T₁ v T'
                            h_pba h_pargs' h_heap₁ h_some)
                    | cons _ _ =>
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level _ [op, listToVal args] T₁ v T'
                            h_pba h_pargs' h_heap₁ h_some)
                    | closure _ _ _ =>
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level _ [op, listToVal args] T₁ v T'
                            h_pba h_pargs' h_heap₁ h_some)
                    | prim _ =>
                        exact h_ext_mat.trans
                          (IH_applyDirect ptable level _ [op, listToVal args] T₁ v T'
                            h_pba h_pargs' h_heap₁ h_some)
  · -- applyDirect clause
    intro ptable level op args T v T' h_pop h_pargs h_heap h_some
    cases op with
    | num _ => simp [applyDirect] at h_some
    | bool _ => simp [applyDirect] at h_some
    | nilV => simp [applyDirect] at h_some
    | sym _ => simp [applyDirect] at h_some
    | cons _ _ => simp [applyDirect] at h_some
    | prim name =>
        simp only [applyDirect] at h_some
        cases h_pa : applyPrim name args with
        | none => simp [h_pa] at h_some
        | some v' =>
            simp [h_pa] at h_some
            obtain ⟨_, rfl⟩ := h_some
            exact StateExtends.refl T
    | builtinBaseApply =>
        cases args with
        | nil => simp [applyDirect] at h_some
        | cons actualOp tl =>
            cases tl with
            | nil => simp [applyDirect] at h_some
            | cons opList tl2 =>
                cases tl2 with
                | nil =>
                    simp only [applyDirect] at h_some
                    cases h_vtl : valToList opList with
                    | none => simp [h_vtl] at h_some
                    | some operands =>
                        simp [h_vtl] at h_some
                        simp only [PureValList, Bool.and_eq_true] at h_pargs
                        obtain ⟨h_pao, h_pol, _⟩ := h_pargs
                        have h_pops : PureValList operands = true :=
                          valToList_PureValList h_pol h_vtl
                        exact IH_applyDirect ptable level actualOp operands T v T'
                          h_pao h_pops h_heap h_some
                | cons _ _ => simp [applyDirect] at h_some
    | closure ps body cenv =>
        simp only [applyDirect] at h_some
        by_cases h_len : ps.length = args.length
        · simp [h_len] at h_some
          have h_pbody : Pure body = true := by
            simpa only [PureVal] using h_pop
          obtain ⟨extras, h_foldl⟩ :=
            foldl_allocStep_heap_extends (args.zip ps) T.heap cenv
          have h_heap' : PureHeap (args.zip ps |>.foldl allocStep (T.heap, cenv)).1 :=
            foldl_allocStep_preserves_PureHeap (args.zip ps) T.heap cenv h_heap
              (PureValList_zip_left h_pargs)
          have h_ext_alloc :
              StateExtends T
                { T with heap := (args.zip ps |>.foldl allocStep (T.heap, cenv)).1 } := by
            rw [h_foldl]
            exact StateExtends.of_heap_append T extras
          exact h_ext_alloc.trans
            (IH_eval ptable level body
              (args.zip ps |>.foldl allocStep (T.heap, cenv)).2
              { T with heap := (args.zip ps |>.foldl allocStep (T.heap, cenv)).1 }
              v T' h_pbody h_heap' h_some)
        · simp [h_len] at h_some

theorem pureEvalExt : ∀ n, PureEvalExt n
  | 0     => pureEvalExt_zero
  | n + 1 => pureEvalExt_succ n (pureEvalExt n)

/-! ## User-facing corollaries -/

/-- Evaluating a `Pure` expression over a `PureHeap` only extends
    the state. -/
theorem eval_pure_extends {k : Nat} {ptable : PolicyTable} {level : Nat}
    {e : Expr} {env : Env} {T : TowerState} {v : Val} {T' : TowerState}
    (h_pure : Pure e = true) (h_heap : PureHeap T.heap)
    (h_some : eval k ptable level e env T = some (v, T')) :
    StateExtends T T' :=
  (pureEvalExt k).1 ptable level e env T v T' h_pure h_heap h_some

/-- `evalList` version of `eval_pure_extends`. -/
theorem evalList_pure_extends {k : Nat} {ptable : PolicyTable} {level : Nat}
    {es : List Expr} {env : Env} {T : TowerState} {vs : List Val} {T' : TowerState}
    (h_pure : PureList es = true) (h_heap : PureHeap T.heap)
    (h_some : evalList k ptable level es env T = some (vs, T')) :
    StateExtends T T' :=
  (pureEvalExt k).2.1 ptable level es env T vs T' h_pure h_heap h_some

end LeanBlack
