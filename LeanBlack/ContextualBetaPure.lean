/-
  lean-sage: Contextual β over pure-sided contexts — the assembled
  theorem.

  This file combines:

  - `ContextualBeta.lean`'s base-case witness
    (`beta_letE_conv_equiv`: β-redex ≡ `.letE` under the L1
    conditions),
  - `PureExt.lean`'s structural-evolution engine (`StateExtends`
    under pure evaluation), and
  - `CtxPure.lean`'s master congruence (`Ctx.plug_cong_master`
    with sibling class `Pure`, over every `Expr` position except
    under `.lam`)

  into the contextually-quantified β-equivalence:

    For any pure-sided context `C` (em-nesting allowed), any binder
    `x`, any body, and any *pure* operand `v_expr`:
      `C[(λx. body) v_expr]  ≡  C[.letE x v_expr body]`
    at every state with enough depth margin, enough materialized
    levels, builtin `base-apply` cells in the relevant window, and
    a pure heap (`BuiltinReadyP (emDepth C)`).

  The lazy-materialization gap — `initTower` materializes only
  level 0, so the hole's level+1 condition fails at the bare
  program start state — is closed by anchoring the program-level
  corollaries at `buildTower (d+2)`: the canonical tower
  pre-materialized to the context's reflective depth, whose fresh
  levels carry builtin `base-apply` cells by construction
  (`buildTower_builtin`).
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.Eval
import LeanBlack.ProofBased
import LeanBlack.EvalFuelMono
import LeanBlack.Ctx
import LeanBlack.PureExt
import LeanBlack.CtxPure
import LeanBlack.ContextualBeta

open LeanBlack

/-! ## `builtinBaseApplyAt` under state extension -/

/-- `builtinBaseApplyAt` survives any structural extension: envs are
    preserved verbatim and heap cells survive appends. -/
theorem builtinBaseApplyAt_extends {level : Nat} {T T' : TowerState}
    (h : StateExtends T T') (h_b : builtinBaseApplyAt level T) :
    builtinBaseApplyAt level T' := by
  obtain ⟨upEnv, idx, h_env, h_lk, h_cell⟩ := h_b
  exact ⟨upEnv, idx, h.envs _ _ h_env, h_lk, h.cell h_cell⟩

/-! ## The depth-indexed readiness family

`BuiltinReady` (`ContextualBeta.lean`) is the `d = 0` member of a
family indexed by *remaining `em`-depth margin*: descending into an
`em` consumes one unit (the hole runs one level higher, so it needs
its depth bound, its materialized-levels bound, and its builtin
window shifted up by one). -/

/-- Depth-indexed readiness: enough depth margin below `maxDepth`,
    enough materialized levels, and builtin `base-apply` at every
    level in the window `[level, level + d]`. `BuiltinReadyN 0` is
    `BuiltinReady`. -/
def BuiltinReadyN (d : Nat) : StatePred :=
  fun _ level _ T =>
    level + d + 1 < Tower.maxDepth ∧
    T.levels.length > level + d + 1 ∧
    ∀ m, level ≤ m → m ≤ level + d → builtinBaseApplyAt m T

/-- `BuiltinReadyN` bundled with heap purity — the predicate that is
    closed under evaluation of pure sub-expressions. -/
def BuiltinReadyP (d : Nat) : StatePred :=
  fun ptable level env T =>
    BuiltinReadyN d ptable level env T ∧ PureHeap T.heap

theorem BuiltinReadyN_zero_iff (ptable : PolicyTable) (level : Nat)
    (env : Env) (T : TowerState) :
    BuiltinReadyN 0 ptable level env T ↔ BuiltinReady ptable level env T := by
  constructor
  · rintro ⟨h_depth, h_len, h_intv⟩
    exact ⟨h_depth, h_len, h_intv level (Nat.le_refl _) (Nat.le_refl _)⟩
  · rintro ⟨h_depth, h_len, h_b⟩
    refine ⟨h_depth, h_len, ?_⟩
    intro m h1 h2
    have : m = level := by omega
    subst this; exact h_b

/-- `BuiltinReadyN` is env-independent and preserved by structural
    extension. -/
theorem BuiltinReadyN_extends {d : Nat} {ptable : PolicyTable} {level : Nat}
    {env env' : Env} {T T' : TowerState}
    (h : StateExtends T T') (hP : BuiltinReadyN d ptable level env T) :
    BuiltinReadyN d ptable level env' T' := by
  obtain ⟨h_depth, h_len, h_intv⟩ := hP
  refine ⟨h_depth, ?_, ?_⟩
  · have := h.levels_le; omega
  · intro m h1 h2
    exact builtinBaseApplyAt_extends h (h_intv m h1 h2)

/-! ## Family hypotheses for the master congruence -/

/-- A materialization request below the materialized frontier is a
    no-op. -/
theorem materialize_noop {T : TowerState} {n : Nat}
    (h_len : T.levels.length > n) (h_depth : n < Tower.maxDepth) :
    T.materialize n = some T := by
  unfold TowerState.materialize
  rw [if_neg (Nat.not_le.mpr h_depth), if_pos h_len]

/-- `BuiltinReadyP d` is closed under evaluation of pure
    expressions: the state only extends (`PureExt.lean`) and the
    heap stays pure (`allPureIndep`). -/
theorem BuiltinReadyP_closed (d : Nat) : ClosedUnderPureEval (BuiltinReadyP d) := by
  intro ptable level e env T h_pe hP k v T' h_ev
  obtain ⟨hBRN, h_heap⟩ := hP
  have h_ext := eval_pure_extends h_pe h_heap h_ev
  exact ⟨BuiltinReadyN_extends h_ext hBRN,
         (((allPureIndep k).1 level e env T h_pe h_heap).2 ptable v T' h_ev).2⟩

/-- Descending into `em` trades one unit of depth margin for one
    level. The materialization is a no-op (the window is already
    materialized), so the heap is untouched. -/
theorem BuiltinReadyP_em (d : Nat) (ptable : PolicyTable) (level : Nat)
    (env : Env) (T : TowerState)
    (hP : BuiltinReadyP (d + 1) ptable level env T)
    (T_mat : TowerState) (h_mat : T.materialize (level + 1) = some T_mat)
    (upEnv : Env) (_h_env : T_mat.envAt? (level + 1) = some upEnv) :
    BuiltinReadyP d ptable (level + 1) upEnv T_mat := by
  obtain ⟨⟨h_depth, h_len, h_intv⟩, h_heap⟩ := hP
  have h_noop : T.materialize (level + 1) = some T :=
    materialize_noop (by omega) (by omega)
  have h_eq : T_mat = T := by
    rw [h_noop] at h_mat; exact (Option.some.inj h_mat).symm
  subst h_eq
  refine ⟨⟨by omega, by omega, ?_⟩, h_heap⟩
  intro m h1 h2
  exact h_intv m (by omega) (by omega)

/-- `BuiltinReadyP d` survives the `.letE` binding step: evaluate a
    pure binder (extension), allocate the pure result (append),
    extend the env (env-independence). -/
theorem BuiltinReadyP_alloc (d : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (ev : Expr) (env : Env) (T : TowerState)
    (h_pev : Pure ev = true) (hP : BuiltinReadyP d ptable level env T)
    (k : Nat) (v : Val) (T' : TowerState)
    (h_ev : eval k ptable level ev env T = some (v, T')) :
    BuiltinReadyP d ptable level (Env.cons x T'.heap.length env)
      { T' with heap := T'.heap ++ [v] } := by
  obtain ⟨hBRN, h_heap⟩ := hP
  have h_ext := eval_pure_extends h_pev h_heap h_ev
  obtain ⟨h_pval, h_heap'⟩ :=
    ((allPureIndep k).1 level ev env T h_pev h_heap).2 ptable v T' h_ev
  refine ⟨BuiltinReadyN_extends (h_ext.trans (StateExtends.of_heap_append T' [v])) hBRN, ?_⟩
  apply PureHeap_append _ _ h_heap'
  intro w hw
  simp at hw; subst hw; exact h_pval

/-! ## The β base case for arbitrary pure operands

`beta_letE_conv_equiv` (`ContextualBeta.lean`) requires the operand
evaluation to succeed. For a *pure* operand, the success case
satisfies its hypotheses via `StateExtends` (the L1 conditions
transport from `T` to the post-operand state `T'`), and in the
failure case both sides have no outcomes at all. So the equivalence
holds under the state-only predicate `BuiltinReadyP 0` — no
quantification over the operand's evaluation. -/

private theorem redex_arg_must_succeed
    {k : Nat} {ptable : PolicyTable} {level : Nat} {x : String}
    {body v_expr : Expr} {env : Env} {T : TowerState}
    {v : Val} {T_final : TowerState}
    (h_k : eval k ptable level (.app [.lam [x] body, v_expr]) env T
            = some (v, T_final)) :
    ∃ n v_val T', eval n ptable level v_expr env T = some (v_val, T') := by
  cases k with
  | zero => simp [eval] at h_k
  | succ n =>
      cases n with
      | zero => simp [eval] at h_k
      | succ m =>
          rw [eval_app_lam_v_step (m + 1) ptable level x body v_expr env T] at h_k
          rw [eval_lam m ptable level [x] body env T] at h_k
          simp only at h_k
          cases m with
          | zero => simp [evalList, eval] at h_k
          | succ mm =>
              rw [evalList_single mm ptable level v_expr env T] at h_k
              cases h_ev : eval (mm + 1) ptable level v_expr env T with
              | none => rw [h_ev] at h_k; simp at h_k
              | some pr => exact ⟨mm + 1, pr.1, pr.2, by rw [h_ev]⟩

private theorem letE_arg_must_succeed
    {k : Nat} {ptable : PolicyTable} {level : Nat} {x : String}
    {body v_expr : Expr} {env : Env} {T : TowerState}
    {v : Val} {T_final : TowerState}
    (h_k : eval k ptable level (.letE x v_expr body) env T = some (v, T_final)) :
    ∃ n v_val T', eval n ptable level v_expr env T = some (v_val, T') := by
  cases k with
  | zero => simp [eval] at h_k
  | succ n =>
      simp only [eval] at h_k
      cases h_ev : eval n ptable level v_expr env T with
      | none => rw [h_ev] at h_k; simp at h_k
      | some pr => exact ⟨n, pr.1, pr.2, by rw [h_ev]⟩

/-- **β base case, pure operand, state-only precondition.** For any
    binder, body, and pure operand, the β-redex and its `.letE`
    contractum are observationally equivalent at every
    `BuiltinReadyP 0` state. -/
theorem beta_letE_pure_EvalEquivAt (x : String) (body v_expr : Expr)
    (h_pv : Pure v_expr = true) :
    EvalEquivAt (BuiltinReadyP 0)
        (.app [.lam [x] body, v_expr])
        (.letE x v_expr body) := by
  intro ptable level env T hP v T_final
  obtain ⟨⟨h_depth, h_len, h_intv⟩, h_heap⟩ := hP
  by_cases h_succ : ∃ n v_val T', eval n ptable level v_expr env T = some (v_val, T')
  · obtain ⟨n, v_val, T', h_ev⟩ := h_succ
    have h_ev' : eval (n + 1) ptable level v_expr env T = some (v_val, T') :=
      eval_fuel_mono (Nat.le_succ n) h_ev
    have h_ext : StateExtends T T' := eval_pure_extends h_pv h_heap h_ev
    have h_mat' : T'.levels.length > level + 1 := by
      have := h_ext.levels_le; omega
    have h_builtin' : builtinBaseApplyAt level T' :=
      builtinBaseApplyAt_extends h_ext (h_intv level (Nat.le_refl _) (by omega))
    exact beta_letE_conv_equiv n ptable level x body v_expr env T (by omega)
      v_val T' h_ev' h_mat' h_builtin' v T_final
  · constructor
    · rintro ⟨k, h_k⟩
      exact absurd (redex_arg_must_succeed h_k) h_succ
    · rintro ⟨k, h_k⟩
      exact absurd (letE_arg_must_succeed h_k) h_succ

/-! ## The contextual β theorem -/

/-- **Contextual β over pure-sided contexts.** For any lam-free
    context `C` (every `Expr` position except under `.lam`,
    `em`-nesting included) with pure pre-hole siblings, and any pure
    operand: the β-redex plug and the `.letE` plug are
    observationally equivalent at every `BuiltinReadyP (emDepth C)`
    state. Instance of the master congruence
    (`Ctx.plug_cong_master` with sibling class `Pure`). -/
theorem contextual_beta_pure
    (C : Ctx) (h_lam : C.lamFree = true)
    (h_sides : C.sidesOK (fun e => Pure e = true))
    (x : String) (body v_expr : Expr) (h_pv : Pure v_expr = true) :
    EvalEquivAt (BuiltinReadyP C.emDepth)
        (C.plug (.app [.lam [x] body, v_expr]))
        (C.plug (.letE x v_expr body)) :=
  Ctx.plug_cong_master (fun e => Pure e = true) BuiltinReadyP
    BuiltinReadyP_closed BuiltinReadyP_alloc C
    (fun _ => BuiltinReadyP_em)
    h_lam h_sides
    (beta_letE_pure_EvalEquivAt x body v_expr h_pv)

/-! ## Closing the lazy-materialization gap: the canonical start tower

`initTower` materializes only level 0, so the hole's `level + 1`
condition fails at the program's bare start state.
`buildTower (d + 2)` is the canonical start tower pre-materialized
to reflective depth `d + 1`; its fresh levels carry builtin
`base-apply` cells *by construction*, proved here. -/

theorem buildTower_succ (n : Nat) :
    buildTower (n + 1) = materializeStep (buildTower n) := by
  unfold buildTower materializeStep
  simp [Nat.fold]

theorem buildTower_levels_length (n : Nat) :
    (buildTower n).levels.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [buildTower_succ, materializeStep_levels_length, ih]

/-- One materialization step is a structural extension. -/
theorem materializeStep_extends (T : TowerState) :
    StateExtends T (materializeStep T) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold materializeStep
    exact freshLevelEnv_heap_extends T.heap
  · intro m e h_env
    unfold materializeStep
    unfold TowerState.envAt? TowerState.levelAt? at h_env ⊢
    cases h_lv : T.levels[m]? with
    | none => rw [h_lv] at h_env; cases h_env
    | some ls =>
        rw [h_lv] at h_env
        have h_lt : m < T.levels.length := (List.getElem?_eq_some_iff.mp h_lv).1
        rw [List.getElem?_append_left h_lt, h_lv]
        exact h_env
  · rw [materializeStep_levels_length]
    exact Nat.le_succ _

/-- The fresh level allocated by `freshLevelEnv` binds `base-apply`
    to a cell holding the builtin. -/
theorem freshLevelEnv_base_apply (h : Heap) :
    ∃ idx, (freshLevelEnv h).2.lookup "base-apply" = some idx ∧
           (freshLevelEnv h).1[idx]? = some Val.builtinBaseApply := by
  unfold freshLevelEnv
  simp only [Heap.alloc]
  refine ⟨?idx, ?_, ?_⟩
  case idx => exact (primPairs.foldl
      (fun (acc : Heap × Env) (kv : String × Val) =>
        (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2)) (h, Env.nil)).1.length
  · simp [Env.lookup]
  · rw [List.getElem?_append_right (Nat.le_refl _)]
    simp

/-- Every interior level of `buildTower N` has the builtin
    `base-apply`. -/
theorem buildTower_builtin (N : Nat) :
    ∀ m, m + 1 < N → builtinBaseApplyAt m (buildTower N) := by
  induction N with
  | zero => intro m h; omega
  | succ N ih =>
      intro m h_lt
      rw [buildTower_succ]
      by_cases h_old : m + 1 < N
      · exact builtinBaseApplyAt_extends (materializeStep_extends _) (ih m h_old)
      · -- m + 1 = N: the appended level is exactly m + 1.
        have h_eq : m + 1 = N := by omega
        obtain ⟨idx, h_lk, h_cell⟩ := freshLevelEnv_base_apply (buildTower N).heap
        refine ⟨(freshLevelEnv (buildTower N).heap).2, idx, ?_, h_lk, ?_⟩
        · unfold materializeStep TowerState.envAt? TowerState.levelAt?
          rw [List.getElem?_append_right (by rw [buildTower_levels_length]; omega)]
          rw [buildTower_levels_length, h_eq]
          simp
        · show (materializeStep (buildTower N)).heap[idx]? = _
          unfold materializeStep
          exact h_cell

theorem buildTower_pureHeap (N : Nat) : PureHeap (buildTower N).heap := by
  induction N with
  | zero =>
      intro i v h
      rw [show (buildTower 0).heap = [] from rfl] at h
      cases h
  | succ N ih =>
      rw [buildTower_succ]
      exact materializeStep_preserves_PureHeap ih

/-- The canonical start state for a depth-`d` context — the
    pre-materialized tower with any level-0 policy installed — is
    `BuiltinReadyP d` at level 0, for any policy table and env. -/
theorem startTower_BuiltinReadyP (d : Nat) (h_depth : d + 1 < Tower.maxDepth)
    (p : BlackPolicy) (ptable : PolicyTable) (env : Env) :
    BuiltinReadyP d ptable 0 env ((buildTower (d + 2)).setPolicyAt 0 p) := by
  constructor
  · refine ⟨by omega, ?_, ?_⟩
    · rw [TowerState.setPolicyAt_levels_length, buildTower_levels_length]
      omega
    · intro m h0 hd
      have h_b := buildTower_builtin (d + 2) m (by omega)
      obtain ⟨upEnv, idx, h_env, h_lk, h_cell⟩ := h_b
      refine ⟨upEnv, idx, ?_, h_lk, ?_⟩
      · rw [TowerState.setPolicyAt_envAt?]; exact h_env
      · rw [show ((buildTower (d + 2)).setPolicyAt 0 p).heap
              = (buildTower (d + 2)).heap from TowerState.setPolicyAt_heap _ _ _]
        exact h_cell
  · rw [show ((buildTower (d + 2)).setPolicyAt 0 p).heap
          = (buildTower (d + 2)).heap from TowerState.setPolicyAt_heap _ _ _]
    exact buildTower_pureHeap _

/-! ## Program-level corollaries -/

/-- **Contextual β from the canonical start state.** For any
    lam-free pure-sided context `C` with depth margin, any
    binder/body, and any pure operand: the two plugs agree on all
    outcomes when run at level 0 from the pre-materialized tower,
    under any level-0 policy, any policy table, and any env. -/
theorem contextual_beta_at_start
    (C : Ctx) (h_lam : C.lamFree = true)
    (h_sides : C.sidesOK (fun e => Pure e = true))
    (h_depth : C.emDepth + 1 < Tower.maxDepth)
    (x : String) (body v_expr : Expr) (h_pv : Pure v_expr = true)
    (ptable : PolicyTable) (p : BlackPolicy) (env : Env)
    (v : Val) (T_final : TowerState) :
    (∃ k, eval k ptable 0 (C.plug (.app [.lam [x] body, v_expr])) env
            ((buildTower (C.emDepth + 2)).setPolicyAt 0 p) = some (v, T_final)) ↔
    (∃ k, eval k ptable 0 (C.plug (.letE x v_expr body)) env
            ((buildTower (C.emDepth + 2)).setPolicyAt 0 p) = some (v, T_final)) :=
  contextual_beta_pure C h_lam h_sides x body v_expr h_pv ptable 0 env _
    (startTower_BuiltinReadyP C.emDepth h_depth p ptable env) v T_final

/-- **The Wand pair, contextually quantified, from the start
    state.** The specific β-redex/contractum pair of
    `wand_defeated_existential_gated_beta`, lifted to any lam-free
    pure-sided context (every `Expr` position except under `.lam`),
    including `em`-nesting to any depth within the tower bound. -/
theorem wand_beta_ctx_pure_at_start
    (C : Ctx) (h_lam : C.lamFree = true)
    (h_sides : C.sidesOK (fun e => Pure e = true))
    (h_depth : C.emDepth + 1 < Tower.maxDepth)
    (ptable : PolicyTable) (p : BlackPolicy) (env : Env)
    (v : Val) (T_final : TowerState) :
    (∃ k, eval k ptable 0 (C.plug (.app [.lam ["x"] (.var "x"), .num 0])) env
            ((buildTower (C.emDepth + 2)).setPolicyAt 0 p) = some (v, T_final)) ↔
    (∃ k, eval k ptable 0 (C.plug (.letE "x" (.num 0) (.var "x"))) env
            ((buildTower (C.emDepth + 2)).setPolicyAt 0 p) = some (v, T_final)) :=
  contextual_beta_at_start C h_lam h_sides h_depth "x" (.var "x") (.num 0) rfl
    ptable p env v T_final
