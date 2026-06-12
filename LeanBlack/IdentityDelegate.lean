import LeanBlack.Compose
import LeanBlack.Frame
import LeanBlack.EvalFuelMono
import LeanBlack.HeapAgree

/-!
# IdentityDelegate — the simplest non-trivial second-install wrapper

`identityDelegateBody` is `(orig op args)` — a wrapper that does
nothing except forward to its captured `orig`. Installed on top of any
apply value, it's a conservative extension of that value: every call
goes through `orig` and returns the same result, modulo the heap
allocation of `[op, listToVal operands]` that wrapper-invocation
triggers.

This is the *concrete second link* in a CE chain: the framework
already supports `CE_weak_strong` transitivity (`Compose.lean`); this
file builds one concrete instance, demonstrating
`bbApply → multn → identity-delegate-on-multn` end-to-end through
the proof-based gate.
-/

namespace LeanBlack

/-! ## Body and template -/

/-- The wrapper body: `(orig op args)` — pure delegation. -/
def identityDelegateBody : Expr :=
  .primApp (.var "orig") [.var "op", .var "args"]

/-- The wrapper lambda. -/
def identityDelegateLam : Expr := .lam ["op", "args"] identityDelegateBody

/-! ## Trace lemma

Calling the identity-delegate closure with `(op, operands)` traces
(after the closure case's alloc step) to `applyDirect` on the captured
`origVal` with `[op, listToVal operands]` in the alloc'd state. Fuel
decreases by 2 (one for the `.closure` case, one for the `.primApp`
inside the body). -/

theorem identityDelegate_body_unfolds
    {fuel : Nat} (h_fuel : fuel ≥ 3)
    (ptable : PolicyTable) (level : Nat)
    (op : Val) (operands : List Val)
    (cenv : Env) (idx_o : Nat) (origVal : Val)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (T : TowerState)
    (h_heap_o : T.heap[idx_o]? = some origVal) :
    applyDirect (fuel + 2) ptable level
        (.closure ["op", "args"] identityDelegateBody cenv)
        [op, listToVal operands] T
      = applyDirect fuel ptable level origVal [op, listToVal operands]
          { T with heap := T.heap ++ [op, listToVal operands] } := by
  -- Pre-compute the alloc'd heap lookups.
  have h_lookup_op_alloc :
      (T.heap ++ [op, listToVal operands])[T.heap.length]? = some op := by
    rw [List.getElem?_append_right (Nat.le_refl _)]; simp
  have h_lookup_args_alloc :
      (T.heap ++ [op, listToVal operands])[T.heap.length + 1]?
        = some (listToVal operands) := by
    rw [List.getElem?_append_right (by omega)]; simp
  -- idx_o is within T.heap (since h_heap_o gave us a value at idx_o).
  have h_idx_o_lt : idx_o < T.heap.length := by
    have := List.getElem?_eq_some_iff.mp h_heap_o
    obtain ⟨h, _⟩ := this; exact h
  have h_lookup_orig_alloc :
      (T.heap ++ [op, listToVal operands])[idx_o]? = some origVal := by
    rw [List.getElem?_append_left h_idx_o_lt]; exact h_heap_o
  -- Set up alloc'd env.
  let env_alloc : Env := Env.cons "args" (T.heap.length + 1)
                          (Env.cons "op" T.heap.length cenv)
  let T_alloc : TowerState :=
    { T with heap := T.heap ++ [op, listToVal operands] }
  -- Lookups in env_alloc.
  have hl_op : env_alloc.lookup "op" = some T.heap.length := by
    show (Env.cons "args" (T.heap.length + 1)
          (Env.cons "op" T.heap.length cenv)).lookup "op" = _
    simp [Env.lookup]
  have hl_args : env_alloc.lookup "args" = some (T.heap.length + 1) := by
    show (Env.cons "args" (T.heap.length + 1)
          (Env.cons "op" T.heap.length cenv)).lookup "args" = _
    simp [Env.lookup]
  have hl_orig : env_alloc.lookup "orig" = some idx_o := by
    show (Env.cons "args" (T.heap.length + 1)
          (Env.cons "op" T.heap.length cenv)).lookup "orig" = _
    simp [Env.lookup]
    exact h_lookup_o
  -- Unpack fuel: fuel ≥ 3 means fuel = k + 3 for some k.
  obtain ⟨k, hk⟩ : ∃ k, fuel = k + 3 := ⟨fuel - 3, by omega⟩
  subst hk
  -- applyDirect on closure: length check + foldl alloc + eval body.
  show applyDirect (k + 5) ptable level
        (.closure ["op", "args"] identityDelegateBody cenv)
        [op, listToVal operands] T = _
  simp only [applyDirect, allocStep, Heap.alloc, List.zip, List.zipWith,
             List.foldl, beq_self_eq_true, Bool.not_true, Bool.false_eq_true,
             ↓reduceIte, List.length_append, List.length_singleton,
             List.append_assoc, List.cons_append, List.nil_append]
  -- After closure case unfolds: eval (k+4) of identityDelegateBody.
  show eval (k + 4) ptable level identityDelegateBody env_alloc T_alloc
      = applyDirect (k + 3) ptable level origVal [op, listToVal operands] T_alloc
  -- T_alloc heap lookups (T_alloc.heap = T.heap ++ [op, listToVal operands]).
  have hp_op : T_alloc.heap[T.heap.length]? = some op := h_lookup_op_alloc
  have hp_args : T_alloc.heap[T.heap.length + 1]? = some (listToVal operands) :=
    h_lookup_args_alloc
  have hp_orig : T_alloc.heap[idx_o]? = some origVal := h_lookup_orig_alloc
  -- identityDelegateBody = .primApp (.var "orig") [.var "op", .var "args"].
  -- Unfold eval, evalList, .var lookups.
  simp only [identityDelegateBody, eval, evalList, hl_orig, hl_op, hl_args,
             hp_orig, hp_op, hp_args]

/-! ## Auxiliary: ValDeep of `listToVal` lifts from `ListValDeep`. -/

theorem ValDeep_listToVal : ∀ {xs : List Val} {h : Heap},
    ListValDeep xs h → ValDeep (listToVal xs) h
  | [],      _, _ => trivial
  | _ :: _,  _, ⟨hv, htail⟩ => ⟨hv, ValDeep_listToVal htail⟩

/-! ## The selective certificate (the primitive)

The proof bridges:
1. The trace lemma `identityDelegate_body_unfolds`: invoking
   identityDelegate's body traces to `applyDirect origVal [op,
   listToVal operands]` at the alloc'd state.
2. `applyDirect_heap_extend_weak`: lifts the hypothesis-side
   `applyDirect origVal [op, listToVal operands] T` to the same call
   at `T_alloc`, with `ValVis_weak`-related result.

The certificate only reads one heap cell — the captured `orig` at
`idx_o` — so it is stated selectively (`CE_weak_strong_at` over
`[idx_o]`): it survives any later mutation of other cells,
including the `base-apply` cell itself, which is what lets it serve
as a *second link* in an admission chain. The full-prefix form is
derived below.

Restriction: `origVal ≠ .builtinBaseApply`. The bbApply case requires
a different unfolding (bbApply-unpack first); not needed for our
chain demo where the orig captured by identityDelegate is the
previously-installed multn closure. -/

theorem identityDelegate_CE_at
    (level : Nat) (h_ref : Heap) (origVal : Val) (cenv : Env) (idx_o : Nat)
    (h_not_bbApply : origVal ≠ .builtinBaseApply)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_heap_o : h_ref[idx_o]? = some origVal) :
    CE_weak_strong_at level [idx_o] h_ref origVal
      (.closure ["op", "args"] identityDelegateBody cenv) := by
  intro fuel ptable op operands T r T'
  intro _h_len h_agree
  intro h_heap h_op h_operands h_va h_vb h_pt h_pol h_envs h_pols h_envvis
  intro h_heap_deep h_op_deep h_operands_deep h_levels_deep h_pt_shift h_pol_shift h_call
  -- Transport the orig cell from h_ref to T.heap via the selective agreement.
  have h_heap_o_T : T.heap[idx_o]? = some origVal := by
    rw [← h_agree idx_o (by simp)]; exact h_heap_o
  -- ValDeep origVal at T.heap, via HeapDeep.
  have h_origVal_deep : ValDeep origVal T.heap :=
    h_heap_deep idx_o origVal h_heap_o_T
  -- Unfold callAsBaseApply (origVal is a closure, not bbApply).
  have h_app_origVal : applyDirect fuel ptable level origVal
        [op, listToVal operands] T = some (r, T') := by
    unfold callAsBaseApply at h_call
    cases origVal with
    | builtinBaseApply => exact absurd rfl h_not_bbApply
    | _ => exact h_call
  -- Validity of the extras (= [op, listToVal operands]).
  have h_extras_valid : ListValValid [op, listToVal operands] T.heap :=
    ⟨h_op, ValValid_listToVal h_operands, trivial⟩
  -- Deep validity for the extras list.
  have h_args_deep : ListValDeep [op, listToVal operands] T.heap :=
    ⟨h_op_deep, ValDeep_listToVal h_operands_deep, trivial⟩
  -- Apply heap-extend-weak. Note: h_va = ValValid origVal T.heap (from
  -- the certificate's premises; the predicate calls this "ValValid old T.heap").
  obtain ⟨r_alloc, T_alloc_post, h_app_alloc, h_vis, h_heap_valid, h_state_eq, h_heap_mono⟩ :=
    applyDirect_heap_extend_weak h_pt h_heap h_va h_extras_valid h_envs h_pols
      h_app_origVal [op, listToVal operands] h_extras_valid h_heap_deep h_origVal_deep
      h_args_deep h_levels_deep h_pt_shift h_pol_shift
  -- Trace identityDelegate's invocation: callAsBaseApply (fuel+2) on closure
  -- unfolds to applyDirect fuel on origVal at the alloc'd state. Use
  -- fuel + 5 so the trace's `≥ 3` bound holds unconditionally.
  refine ⟨fuel + 5, T_alloc_post, r_alloc, ?_, h_vis, ?_, h_heap_valid, ?_⟩
  · show callAsBaseApply (fuel + 5) ptable level
          (.closure ["op", "args"] identityDelegateBody cenv) op operands T = _
    unfold callAsBaseApply
    show applyDirect (fuel + 5) ptable level
          (.closure ["op", "args"] identityDelegateBody cenv)
          [op, listToVal operands] T = _
    have h_fuel3 : fuel + 3 ≥ 3 := by omega
    rw [show fuel + 5 = (fuel + 3) + 2 from by omega]
    rw [identityDelegate_body_unfolds h_fuel3 ptable level op operands cenv idx_o origVal
          h_lookup_o T h_heap_o_T]
    exact applyDirect_fuel_mono (by omega : fuel ≤ fuel + 3) h_app_alloc
  · exact h_state_eq level
  · have : T.heap.length ≤ T.heap.length + [op, listToVal operands].length :=
      Nat.le_add_right _ _
    exact Nat.le_trans this h_heap_mono

/-- Full-prefix corollary of `identityDelegate_CE_at` (the form
    `ApprovedModification.proof` consumes), via
    `CE_weak_strong_of_at`. -/
theorem identityDelegate_CE_of_closure
    (level : Nat) (h_ref : Heap) (origVal : Val) (cenv : Env) (idx_o : Nat)
    (h_not_bbApply : origVal ≠ .builtinBaseApply)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_heap_o : h_ref[idx_o]? = some origVal) :
    CE_weak_strong level h_ref origVal
      (.closure ["op", "args"] identityDelegateBody cenv) := by
  refine CE_weak_strong_of_at ?_
    (identityDelegate_CE_at level h_ref origVal cenv idx_o
      h_not_bbApply h_lookup_o h_heap_o)
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  subst hi
  exact getElem?_some_lt_length h_heap_o

/-! ## Approval constructor

Bundles `identityDelegate_CE_of_closure` into an `ApprovedModification`
record. Use when the previously-installed apply rule (`origVal`) is a
closure (not `.builtinBaseApply`) — typical for the *second* link in
a CE chain. -/

def identityDelegateApproval
    (level : Nat) (heap : Heap) (cenv : Env) (idx_o : Nat) (origVal : Val)
    (h_not_bbApply : origVal ≠ .builtinBaseApply)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_heap_o : heap[idx_o]? = some origVal) :
    ApprovedModification :=
  { level   := level
    heap    := heap
    oldVal  := origVal
    newVal  := .closure ["op", "args"] identityDelegateBody cenv
    proof   := identityDelegate_CE_of_closure level heap origVal cenv idx_o
                 h_not_bbApply h_lookup_o h_heap_o }

end LeanBlack
