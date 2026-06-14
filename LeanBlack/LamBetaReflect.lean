/-
  lean-sage: β-infrastructure for the *reflective* cases of the `.lam`
  fundamental lemma — the open core of `DUMP_LAM.md` (step 1 + step 3c).

  The gate-free fragment is closed in `LamBeta.lean` (every eval structural
  case, `evalList`, and the entire `applyDirect` clause). What remains is the
  reflective core: the `WFCtxTβ` statement wrapper, the `applyVia` gate
  dispatch, and `.em`/`.set`. All of these read the tower's *level structure*,
  and the linchpin is that `materialize` behaves consistently cross-side under
  β — where the existing `materialize_cross_side_*` lemmas (`Tower.lean`) all
  rest on `heap_len_eq` (`T_a.heap.length = T_b.heap.length`) and
  `level_envs_eq` (`∀ m, T_a.envAt? m = T_b.envAt? m`), *both of which β breaks*.

  `freshLevelEnv` allocates its 14 standard cells (13 prims + `base-apply`) at
  indices starting from `h.length`; under β the two heaps differ in length, so
  those fresh indices **diverge cross-side**. The existing
  `freshLevelEnv_env_eq` proves the two new level-envs *equal* (needing equal
  heap length); this file proves the β replacement: they are **`EnvVisβ`-
  related**, with no heap-length hypothesis — because every fresh cell holds a
  *ground* value (a `.prim` or `.builtinBaseApply`), and `ValVisβ` on ground
  values is heap-independent.

  This is the genuine new relational content the reflective cases need. It is
  isolated here so `LamBeta.lean` (the committed gate-free result) stays clean.

  Status: linchpin `freshLevelEnv_envVisβ` proved; `WFCtxTβ` defined; and the
  full **`materialize` cross-side β preservation** (`materialize_MatInvβ`, via
  `MatInvβ` + `materializeStep_MatInvβ`) proved — `materialize` carries the
  cross-side level relation, establishing it for each fresh level by the
  linchpin and lifting old levels by `EnvVisβ_extends`. Building on these, the
  **first reflective eval case `.em` is proved** (`frameβ_em_eval`, §7f) on the
  `WFCtxTβ`-based eval statement `FrameβEvalStmtW` — the metacircular level
  shift, threading `materialize_MatInvβ` + `materialize_policiesEqβ` to build
  `WFCtxTβ` at `level + 1` for the IH and rebuild it at `level` for the output.
  The **entire gate-free eval clause is now done over `FrameβEvalStmtW`**: the
  non-recursive cases (`.num`/`.bool`/`.var`/`.lam`, §7g) and the recursive
  structural cases (`.ifte`/`.seq`/`.letE`, §7h — `.letE` via `level_fields_alloc`
  + `EnvVisβ_alloc_cons`). The **`applyDirect` clause is re-threaded onto the
  level-tracking tower invariant `TowerInvβ`** (`frameβ_applyDirect_evalW`, §7i),
  and the **gated `.app` (`applyVia`'s gate dispatch) is proved** (`frameβ_applyVia_eval`,
  §7j — both sides materialize, the `base-apply` cells are `ValVisβ`-related forcing
  the same dispatch branch, then the `applyDirect` IH; route (b)'s gate threading).
  the **`evalList` clause is re-threaded onto `WFCtxTβ`** (`frameβ_evalList_evalW`,
  §7k), and the **minor eval cases `.quote` / `.installPolicy` are done** (§7l, via
  the `setPolicyAt` lemmas). eval's `.app` splits (`BetaRel.app_inv`) into a
  structural and a root-contraction branch, **both now proved over `WFCtxTβ`** (§7m):
  the **structural branch** (`frameβ_app_structural_evalW`) unconditionally — both
  sides run an `.app`, so the gated `applyVia` clause §7j handles the gate (composes
  the eval IH + §7k + §7j); and the **root-contraction branch** under the **recognized
  conditional premise** (`frameβ_app_root_evalW`). The route avoids any diagonal:
  `app_to_redex_inv` + `letE_inv` expose the *reduced* redex `(λx.body') v'`, the
  structural branch maps the a-side onto the b-side redex, and the gate bridge finishes.
  That bridge — first isolated as the abstract hypothesis `h_gate_b`
  (`frameβ_app_root_evalW_cond`) — is now **discharged**: `redex_to_letE_fixed` (the
  fixed-fuel companion to `beta_letE_conv_equiv`) + `gate_redex_to_letE` (operand
  convergence extracted from the redex, the standard gate carried through the operand by
  purity) give `gate_redex_to_letE_anyfuel`, so the premise is exactly `DUMP_LAM` §0's
  standard-gate `BuiltinReady` + heap/operand purity — the same side conditions
  `contextual_beta_pure` carries. The **payoff bridge** is also built (§7n,
  `obsConv_refine_of_FL` + `obsConv_refine_of_FL_rev`): the cross-side fundamental lemma
  ⟹ ground `ObsConv` agreement (`↔`) in every context (`BetaRel.congr` lifts the relation
  into `C`, `WFCtxTβ.refl` diagonalizes the cross-side FL onto the single-sided observation,
  `ValVisβ_isGround_eq` / `_right` collapse ground results to equality) — **both directions**,
  i.e. the full conditional ground `CtxEquiv` that `CtxEquiv.under_lam` lifts through `.lam`
  for free. **What remains** is to discharge the two FL hypotheses: the mechanical FL assembly
  (re-cut the mutual statement to carry the `Pure` + `BuiltinReadyN` premise — `.set` /
  `.installPolicy` vacuous under `Pure`; `.app` root done) for the forward `hFL`, and the
  reverse simulation for `hFL_rev` (its operational core is `gate_redex_to_letE`'s `↔`).
  (DUMP_LAM §4 has the plans.)
-/
import LeanBlack.LamBeta
import LeanBlack.Frame

namespace LeanBlack

/-! ## 7a. Ground values self-bisimulate, and validity helpers

A `closedValB` value contains no closures, the only place `ValVisβ` looks at
the heap — so it relates to itself at *any* pair of heaps, and is `ValValid`
in any heap. These carry the "fresh cells are ground" reasoning. -/

/-- A closure-free value `ValVisβ`-relates to itself over any heaps. -/
theorem ValVisβ_refl_closed : ∀ (v : Val), closedValB v = true →
    ∀ (h_a h_b : Heap), ValVisβ v v h_a h_b
  | .num _,  _, _, _ => fun d => by cases d <;> simp [ValVisβ_aux]
  | .bool _, _, _, _ => fun d => by cases d <;> simp [ValVisβ_aux]
  | .nilV,   _, _, _ => fun d => by cases d <;> simp [ValVisβ_aux]
  | .sym _,  _, _, _ => fun d => by cases d <;> simp [ValVisβ_aux]
  | .prim _, _, _, _ => fun d => by cases d <;> simp [ValVisβ_aux]
  | .builtinBaseApply, _, _, _ => fun d => by cases d <;> simp [ValVisβ_aux]
  | .cons x y, hc, h_a, h_b => by
      simp only [closedValB, Bool.and_eq_true] at hc
      intro d
      cases d with
      | zero => trivial
      | succ d' =>
          exact ⟨ValVisβ_refl_closed x hc.1 h_a h_b d', ValVisβ_refl_closed y hc.2 h_a h_b d'⟩
  | .closure _ _ _, hc, _, _ => by simp [closedValB] at hc

/-- A closure-free value is `ValValid` in any heap. -/
theorem closedVal_ValValid : ∀ (v : Val), closedValB v = true → ∀ (h : Heap), ValValid v h
  | .num _,  _, _ => trivial
  | .bool _, _, _ => trivial
  | .nilV,   _, _ => trivial
  | .sym _,  _, _ => trivial
  | .prim _, _, _ => trivial
  | .builtinBaseApply, _, _ => trivial
  | .cons x y, hc, h => by
      simp only [closedValB, Bool.and_eq_true] at hc
      exact ⟨closedVal_ValValid x hc.1 h, closedVal_ValValid y hc.2 h⟩
  | .closure _ _ _, hc, _ => by simp [closedValB] at hc

/-- Snoc-ing a closure-free cell preserves `HeapValid`. -/
theorem heapValid_snoc_closed (h : Heap) (v : Val)
    (hh : HeapValid h) (hc : closedValB v = true) : HeapValid (h ++ [v]) := by
  intro i w hp
  by_cases hlt : i < h.length
  · have hp_old : h[i]? = some w := by rw [← getElem?_prefix h [v] i hlt]; exact hp
    exact ValValid.heap_extends w (hh i w hp_old) ⟨[v], rfl⟩
  · have h_eq : i = h.length := by
      have h_le : i < (h ++ [v]).length := by
        rw [List.getElem?_eq_some_iff] at hp; obtain ⟨hh', _⟩ := hp; exact hh'
      simp [List.length_append] at h_le; omega
    subst h_eq
    rw [List.getElem?_append_right (Nat.le_refl _)] at hp
    simp at hp; subst hp
    exact closedVal_ValValid v hc (h ++ [v])

/-- The freshly-snoc'd cell is at index `L.length`. -/
theorem getElem?_snoc (L : Heap) (v : Val) : (L ++ [v])[L.length]? = some v := by
  rw [List.getElem?_append_right (Nat.le_refl _)]; simp

/-- Consing a fresh binding `x ↦ h.length` over a valid env stays valid in
    the one-cell-extended heap. -/
theorem envValid_cons_fresh (x : String) (v : Val) (env : Env) (h : Heap)
    (hev : EnvValid env h) : EnvValid (.cons x h.length env) (h ++ [v]) := by
  intro name i hl
  simp only [List.length_append, List.length_singleton]
  simp only [Env.lookup] at hl
  by_cases hx : x = name
  · subst hx; simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hl; omega
  · have hne : (x == name) = false := by rw [beq_eq_false_iff_ne]; exact hx
    simp only [hne, Bool.false_eq_true, ↓reduceIte] at hl
    have := hev name i hl; omega

/-! ## 7b. The cross-side `freshLevelEnv` bisimulation (the linchpin)

The `buildBindings` foldl, run on two unrelated heaps with the *same* atomic
`pairs`, produces `EnvVisβ`-related envs over the (divergent) result heaps —
each fresh binding points to a cell holding the same ground value on both
sides, and old bindings ride through `EnvVisβ_extends`. No heap-length
hypothesis, unlike `freshLevelEnv_env_eq`. -/

theorem buildBindings_foldl_envVisβ (pairs : List (String × Val)) :
    ∀ (h_a h_b : Heap) (env_a env_b : Env),
    (∀ v ∈ pairs.map (·.2), closedValB v = true) →
    HeapValid h_a → HeapValid h_b → EnvValid env_a h_a → EnvValid env_b h_b →
    EnvVisβ env_a env_b h_a h_b →
    let fa := pairs.foldl (fun (acc : Heap × Env) kv =>
      (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2)) (h_a, env_a)
    let fb := pairs.foldl (fun (acc : Heap × Env) kv =>
      (acc.1 ++ [kv.2], Env.cons kv.1 acc.1.length acc.2)) (h_b, env_b)
    HeapValid fa.1 ∧ HeapValid fb.1 ∧ EnvValid fa.2 fa.1 ∧ EnvValid fb.2 fb.1 ∧
    EnvVisβ fa.2 fb.2 fa.1 fb.1 := by
  induction pairs with
  | nil =>
      intro h_a h_b env_a env_b _ hh_a hh_b hev_a hev_b h_vis
      exact ⟨hh_a, hh_b, hev_a, hev_b, h_vis⟩
  | cons p rest ih =>
      intro h_a h_b env_a env_b h_atoms hh_a hh_b hev_a hev_b h_vis
      simp only [List.foldl]
      have hp_closed : closedValB p.2 = true := h_atoms p.2 (by simp)
      have h_atoms_rest : ∀ v ∈ rest.map (·.2), closedValB v = true :=
        fun v hv => h_atoms v (by simp only [List.map_cons, List.mem_cons]; exact Or.inr hv)
      have hh_a' : HeapValid (h_a ++ [p.2]) := heapValid_snoc_closed h_a p.2 hh_a hp_closed
      have hh_b' : HeapValid (h_b ++ [p.2]) := heapValid_snoc_closed h_b p.2 hh_b hp_closed
      have hev_a' : EnvValid (.cons p.1 h_a.length env_a) (h_a ++ [p.2]) :=
        envValid_cons_fresh p.1 p.2 env_a h_a hev_a
      have hev_b' : EnvValid (.cons p.1 h_b.length env_b) (h_b ++ [p.2]) :=
        envValid_cons_fresh p.1 p.2 env_b h_b hev_b
      have hl_a : (h_a ++ [p.2])[h_a.length]? = some p.2 := by
        rw [List.getElem?_append_right (Nat.le_refl _)]; simp
      have hl_b : (h_b ++ [p.2])[h_b.length]? = some p.2 := by
        rw [List.getElem?_append_right (Nat.le_refl _)]; simp
      have h_vv : ValVisβ p.2 p.2 (h_a ++ [p.2]) (h_b ++ [p.2]) :=
        ValVisβ_refl_closed p.2 hp_closed _ _
      have h_vis_ext : EnvVisβ env_a env_b (h_a ++ [p.2]) (h_b ++ [p.2]) :=
        EnvVisβ_extends env_a env_b h_a h_b [p.2] [p.2] hh_a hh_b hev_a hev_b h_vis
      have h_vis' : EnvVisβ (.cons p.1 h_a.length env_a) (.cons p.1 h_b.length env_b)
          (h_a ++ [p.2]) (h_b ++ [p.2]) :=
        EnvVisβ_cons p.1 h_a.length h_b.length env_a env_b (h_a ++ [p.2]) (h_b ++ [p.2])
          p.2 p.2 hl_a hl_b h_vv h_vis_ext
      exact ih (h_a ++ [p.2]) (h_b ++ [p.2]) (.cons p.1 h_a.length env_a)
        (.cons p.1 h_b.length env_b) h_atoms_rest hh_a' hh_b' hev_a' hev_b' h_vis'

/-- **The cross-side `freshLevelEnv` bisimulation (the linchpin).** The two
    freshly-materialized level-envs are `EnvVisβ`-related over the (length-
    divergent) extended heaps — the β replacement for `freshLevelEnv_env_eq`'s
    *equality* (which needs `h_a.length = h_b.length`). Every fresh cell holds
    a ground value, so the indices may diverge while the bindings stay related.
    The fact every reflective case needs to thread the level structure under β. -/
theorem freshLevelEnv_envVisβ (h_a h_b : Heap)
    (hh_a : HeapValid h_a) (hh_b : HeapValid h_b) :
    EnvVisβ (freshLevelEnv h_a).2 (freshLevelEnv h_b).2
            (freshLevelEnv h_a).1 (freshLevelEnv h_b).1 := by
  -- the env/heap *before* the `base-apply` cell, from the linchpin foldl lemma
  obtain ⟨hh_fa, hh_fb, hev_fa, hev_fb, h_vis_prims⟩ :=
    buildBindings_foldl_envVisβ primPairs h_a h_b .nil .nil
      primPairs_atoms_closed hh_a hh_b
      (by intro _ _ h; simp [Env.lookup] at h) (by intro _ _ h; simp [Env.lookup] at h)
      (by intro name; simp [EnvVisβ_aux, Env.lookup])
  -- extend the prim-env relation across the freshly-allocated `base-apply` cell
  have h_vis_ext := EnvVisβ_extends _ _ _ _ [Val.builtinBaseApply] [Val.builtinBaseApply]
    hh_fa hh_fb hev_fa hev_fb h_vis_prims
  -- cons `base-apply ↦ fresh`; the result is defeq to `freshLevelEnv` (Prod-eta + `Heap.alloc`)
  exact EnvVisβ_cons "base-apply" _ _ _ _ _ _
    Val.builtinBaseApply Val.builtinBaseApply (getElem?_snoc _ _) (getElem?_snoc _ _)
    (ValVisβ_refl_closed Val.builtinBaseApply rfl _ _) h_vis_ext

/-! ## 7c. The `WFCtxTβ` statement wrapper

The β-analog of `Frame.WFCtxT`, the well-formedness context the reflective
cases consume. Relative to `WFCtxT`, the cross-side fields are relaxed exactly
where β diverges from a same-program bisimulation:

* `env_eq : env_a = env_b` ↦ `EnvVisβ env_a env_b` (the ambient envs run
  different code);
* `heap_len_eq` is **dropped** (β allocates different cell counts);
* the level fields `level_envs_eq` (envs equal cross-side) +
  `heap_content_bisim_at_levels` (each level's env self-bisimulates) ↦ a single
  `level_envs_visβ`: at every level, the two envs (if materialized) are
  `EnvVisβ`-related — preserved by `materialize` precisely by
  `freshLevelEnv_envVisβ` (§7b), the β replacement for the equal-env argument.

The single-side and policy fields carry over verbatim (`HeapValid` /
`EnvValid` are body-agnostic; policies are unaffected by β). `materialize`
adds new levels deterministically, so the level structures stay in lockstep
(same count) — `level_envs_visβ` is stated over `T_a.envAt? n` / `T_b.envAt? n`
both being `some`, with the "both none / both some" agreement following from
equal level counts (a single-side invariant `materialize` preserves). -/
structure WFCtxTβ (env_a env_b : Env) (T_a T_b : TowerState) (level : Nat)
    : Prop where
  /-- Cross-side: policy at the active level matches. -/
  policy_eq_at : T_a.policyAt? level = T_b.policyAt? level
  hv_a         : HeapValid T_a.heap
  hv_b         : HeapValid T_b.heap
  ev_a         : EnvValid env_a T_a.heap
  ev_b         : EnvValid env_b T_b.heap
  /-- The active policy respects bisim. -/
  policy_resp  : ∀ p, T_a.policyAt? level = some p → PolicyRespectsBisimT p
  /-- β replaces `env_eq` (`WFCtxT`): the ambient envs are `EnvVisβ`-related. -/
  env_visβ     : EnvVisβ env_a env_b T_a.heap T_b.heap
  -- `heap_len_eq` of `WFCtxT` is intentionally absent: β breaks it.
  /-- All materialized levels' envs are valid in both heaps (single-side). -/
  level_envs_valid_a : ∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap
  level_envs_valid_b : ∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap
  /-- The two towers have the same number of materialized levels (β does not
      change the level *structure*, only heap contents). Gives the "both
      `some` / both `none`" agreement of `envAt?` cross-side. -/
  level_count_eq : T_a.levels.length = T_b.levels.length
  /-- Cross-side: at every level, policies match. -/
  policies_eq : ∀ n, T_a.policyAt? n = T_b.policyAt? n
  /-- Every policy at every level respects bisim. -/
  policies_resp_all : ∀ n p, T_a.policyAt? n = some p → PolicyRespectsBisimT p
  /-- β replaces `level_envs_eq` + `heap_content_bisim_at_levels`: at every
      level, the materialized envs are `EnvVisβ`-related cross-side. This is the
      data `.em` needs to build `EnvVisβ upEnv_a upEnv_b` for the IH at
      `level + 1`, and that `materialize` preserves via `freshLevelEnv_envVisβ`. -/
  level_envs_visβ : ∀ n env_a' env_b',
    T_a.envAt? n = some env_a' → T_b.envAt? n = some env_b' →
    EnvVisβ env_a' env_b' T_a.heap T_b.heap

/-! ## 7d. `materialize` preserves the cross-side β level invariant

The reflective cases (`.em`, `applyVia`) materialize `level + 1` on both sides
and then read the up-env. The invariant they carry/need is the cross-side
β level relation `MatInvβ` (the `WFCtxTβ` level fields). This section proves
`materialize` preserves it — establishing it for each newly-materialized level
by the linchpin `freshLevelEnv_envVisβ` (§7b) and lifting the pre-existing
levels by `EnvVisβ_extends`. The β replacement for `materialize_cross_side_*`
(`Tower.lean`, which thread *equality*). -/

/-- Appending a list of closure-free cells preserves `HeapValid`. -/
theorem heapValid_append_closed (h ext : Heap)
    (hh : HeapValid h) (hc : ∀ v ∈ ext, closedValB v = true) : HeapValid (h ++ ext) := by
  intro i w hp
  by_cases hlt : i < h.length
  · have hp_old : h[i]? = some w := by rw [← getElem?_prefix h ext i hlt]; exact hp
    exact ValValid.heap_extends w (hh i w hp_old) ⟨ext, rfl⟩
  · rw [List.getElem?_append_right (Nat.le_of_not_lt hlt)] at hp
    exact closedVal_ValValid w (hc w (List.mem_of_getElem? hp)) (h ++ ext)

/-- `freshLevelEnv` preserves `HeapValid` (my own; `Frame`'s is `private`). -/
theorem freshLevelEnv_heapValidβ (h : Heap) (hh : HeapValid h) :
    HeapValid (freshLevelEnv h).1 := by
  rw [freshLevelEnv_heap_eq, List.append_assoc]
  refine heapValid_append_closed h _ hh ?_
  intro v hv
  rcases List.mem_append.mp hv with h_in | h_in
  · exact primPairs_atoms_closed v h_in
  · simp at h_in; rw [h_in]; rfl

/-- `freshLevelEnv`'s env is valid in its heap (my own; via §7b at `h_a = h_b`). -/
theorem freshLevelEnv_envValidβ (h : Heap) (hh : HeapValid h) :
    EnvValid (freshLevelEnv h).2 (freshLevelEnv h).1 := by
  obtain ⟨_, _, hev_fa, _, _⟩ :=
    buildBindings_foldl_envVisβ primPairs h h .nil .nil primPairs_atoms_closed hh hh
      (by intro _ _ hl; simp [Env.lookup] at hl) (by intro _ _ hl; simp [Env.lookup] at hl)
      (by intro name; simp [EnvVisβ_aux, Env.lookup])
  exact envValid_cons_fresh "base-apply" _ _ _ hev_fa

/-- `materializeStep` reads back pre-existing levels unchanged. -/
theorem materializeStep_envAt?_lt (T : TowerState) (n : Nat) (h : n < T.levels.length) :
    (materializeStep T).envAt? n = T.envAt? n := by
  unfold materializeStep TowerState.envAt? TowerState.levelAt?
  rw [List.getElem?_append_left h]

/-- `materializeStep`'s new level (at the old level-count index) holds the
    fresh env. -/
theorem materializeStep_envAt?_eq (T : TowerState) :
    (materializeStep T).envAt? T.levels.length = some (freshLevelEnv T.heap).2 := by
  unfold materializeStep TowerState.envAt? TowerState.levelAt?
  rw [List.getElem?_append_right (Nat.le_refl _)]; simp

/-- `materializeStep` reads back `none` past its (one larger) level count. -/
theorem materializeStep_envAt?_gt (T : TowerState) (n : Nat) (h : T.levels.length < n) :
    (materializeStep T).envAt? n = none := by
  unfold materializeStep TowerState.envAt? TowerState.levelAt?
  rw [List.getElem?_eq_none (by simp [List.length_append]; omega)]; rfl

/-- The bundled cross-side β level invariant — the level fields of `WFCtxTβ`,
    as a standalone predicate `materialize` preserves. -/
def MatInvβ (T_a T_b : TowerState) : Prop :=
  HeapValid T_a.heap ∧ HeapValid T_b.heap ∧
  T_a.levels.length = T_b.levels.length ∧
  (∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap) ∧
  (∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap) ∧
  (∀ n ea eb, T_a.envAt? n = some ea → T_b.envAt? n = some eb →
    EnvVisβ ea eb T_a.heap T_b.heap)

/-- **One `materializeStep` preserves `MatInvβ`.** The newly-materialized level
    is related by the linchpin `freshLevelEnv_envVisβ`; pre-existing levels are
    lifted across the heap extension by `EnvVisβ_extends`. -/
theorem materializeStep_MatInvβ {T_a T_b : TowerState} (h : MatInvβ T_a T_b) :
    MatInvβ (materializeStep T_a) (materializeStep T_b) := by
  obtain ⟨hh_a, hh_b, h_count, hv_a, hv_b, h_visβ⟩ := h
  -- new heaps extend the old by closure-free cells
  obtain ⟨ext_a, hex_a⟩ := freshLevelEnv_heap_extends T_a.heap
  obtain ⟨ext_b, hex_b⟩ := freshLevelEnv_heap_extends T_b.heap
  have hstep_a : (materializeStep T_a).heap = (freshLevelEnv T_a.heap).1 := rfl
  have hstep_b : (materializeStep T_b).heap = (freshLevelEnv T_b.heap).1 := rfl
  have hh_a' : HeapValid (materializeStep T_a).heap := by
    rw [hstep_a]; exact freshLevelEnv_heapValidβ T_a.heap hh_a
  have hh_b' : HeapValid (materializeStep T_b).heap := by
    rw [hstep_b]; exact freshLevelEnv_heapValidβ T_b.heap hh_b
  have h_count' : (materializeStep T_a).levels.length = (materializeStep T_b).levels.length := by
    rw [materializeStep_levels_length, materializeStep_levels_length, h_count]
  -- pre-existing levels stay valid (heap_extends); the new level is fresh-valid
  have hv_a' : ∀ n env, (materializeStep T_a).envAt? n = some env →
      EnvValid env (materializeStep T_a).heap := by
    intro n env hen
    rw [hstep_a, hex_a]
    by_cases hlt : n < T_a.levels.length
    · rw [materializeStep_envAt?_lt T_a n hlt] at hen
      exact EnvValid.heap_extends (hv_a n env hen) ⟨ext_a, rfl⟩
    · by_cases heq : n = T_a.levels.length
      · subst heq; rw [materializeStep_envAt?_eq] at hen
        injection hen with hen; subst hen
        rw [← hex_a]; exact freshLevelEnv_envValidβ T_a.heap hh_a
      · rw [materializeStep_envAt?_gt T_a n (by omega)] at hen; simp at hen
  have hv_b' : ∀ n env, (materializeStep T_b).envAt? n = some env →
      EnvValid env (materializeStep T_b).heap := by
    intro n env hen
    rw [hstep_b, hex_b]
    by_cases hlt : n < T_b.levels.length
    · rw [materializeStep_envAt?_lt T_b n hlt] at hen
      exact EnvValid.heap_extends (hv_b n env hen) ⟨ext_b, rfl⟩
    · by_cases heq : n = T_b.levels.length
      · subst heq; rw [materializeStep_envAt?_eq] at hen
        injection hen with hen; subst hen
        rw [← hex_b]; exact freshLevelEnv_envValidβ T_b.heap hh_b
      · rw [materializeStep_envAt?_gt T_b n (by omega)] at hen; simp at hen
  -- the cross-side β relation at every level of the stepped states
  have h_visβ' : ∀ n ea eb, (materializeStep T_a).envAt? n = some ea →
      (materializeStep T_b).envAt? n = some eb →
      EnvVisβ ea eb (materializeStep T_a).heap (materializeStep T_b).heap := by
    intro n ea eb hea heb
    rw [hstep_a, hstep_b, hex_a, hex_b]
    by_cases hlt : n < T_a.levels.length
    · -- pre-existing level: lift the input relation across the extension
      rw [materializeStep_envAt?_lt T_a n hlt] at hea
      rw [materializeStep_envAt?_lt T_b n (h_count ▸ hlt)] at heb
      exact EnvVisβ_extends ea eb T_a.heap T_b.heap ext_a ext_b hh_a hh_b
        (hv_a n ea hea) (hv_b n eb heb) (h_visβ n ea eb hea heb)
    · by_cases heq : n = T_a.levels.length
      · -- the newly-materialized level: the linchpin
        subst heq
        rw [materializeStep_envAt?_eq] at hea
        rw [h_count, materializeStep_envAt?_eq] at heb
        injection hea with hea; injection heb with heb; subst hea; subst heb
        rw [← hex_a, ← hex_b]
        exact freshLevelEnv_envVisβ T_a.heap T_b.heap hh_a hh_b
      · rw [materializeStep_envAt?_gt T_a n (by omega)] at hea; simp at hea
  exact ⟨hh_a', hh_b', h_count', hv_a', hv_b', h_visβ'⟩

/-- Iterating `materializeStep` preserves `MatInvβ`. -/
theorem materializeStep_iter_MatInvβ (T_a T_b : TowerState) (k : Nat)
    (h : MatInvβ T_a T_b) :
    MatInvβ (Nat.fold k (fun _ _ T' => materializeStep T') T_a)
            (Nat.fold k (fun _ _ T' => materializeStep T') T_b) := by
  induction k with
  | zero => simpa [Nat.fold] using h
  | succ k ih => simp only [Nat.fold]; exact materializeStep_MatInvβ ih

/-- **`materialize` preserves the cross-side β level invariant.** Whether it is
    a no-op (level already materialized) or materializes new levels (the fold),
    `MatInvβ` carries through — the β replacement for
    `materialize_cross_side_envs_eq` (`Tower.lean`), built on the linchpin. This
    is the fact `.em` / `applyVia` consume after materializing `level + 1` on
    both sides: the up-envs are `EnvVisβ`-related (the `level_envs_visβ` field of
    the resulting `MatInvβ`), and the single-side / count invariants hold. -/
theorem materialize_MatInvβ {T_a T_b T_a' T_b' : TowerState} {n : Nat}
    (h : MatInvβ T_a T_b)
    (h_mat_a : T_a.materialize n = some T_a') (h_mat_b : T_b.materialize n = some T_b') :
    MatInvβ T_a' T_b' := by
  have h_count := h.2.2.1
  unfold TowerState.materialize at h_mat_a h_mat_b
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1] at h_mat_a
  · simp [h1] at h_mat_a h_mat_b
    by_cases h2 : T_a.levels.length > n
    · have h2_b : T_b.levels.length > n := h_count ▸ h2
      simp [h2] at h_mat_a; simp [h2_b] at h_mat_b
      obtain rfl := h_mat_a.symm; obtain rfl := h_mat_b.symm
      exact h
    · have h2_b : ¬ T_b.levels.length > n := h_count ▸ h2
      simp [h2] at h_mat_a; simp [h2_b] at h_mat_b
      obtain rfl := h_mat_a.symm; obtain rfl := h_mat_b.symm
      have h_eq_k : n + 1 - T_a.levels.length = n + 1 - T_b.levels.length := by rw [h_count]
      rw [h_eq_k]
      exact materializeStep_iter_MatInvβ T_a T_b _ h

/-! ## 7e. Cross-side policy preservation under β, and `BetaRel.em_inv`

`materialize_cross_side_policies_eq` (`Tower.lean`) threads `heap_len_eq`; β
breaks it. But policies are unaffected by β (new levels get `rejectAllPolicy`
regardless of the heap), so the β version threads only `level_count_eq`. Plus
the `.em` `BetaRel` inversion (β under `.em` stays an `.em`). -/

/-- β under `.em` stays an `.em`, β-relating the body (the `lam_inv` family). -/
theorem BetaRel.em_inv {body b : Expr} (h : BetaRel (.em body) b) :
    ∃ body', b = .em body' ∧ BetaRel body body' := by
  induction h with
  | refl => exact ⟨body, rfl, .refl _⟩
  | tail _ step ih =>
      obtain ⟨body', rfl, hbody'⟩ := ih
      obtain ⟨C, x, bb, v, hC, hbb⟩ := step
      cases C with
      | em C' =>
          simp only [Ctx.plug, Expr.em.injEq] at hC
          obtain rfl := hC
          exact ⟨C'.plug (.letE x v bb), by rw [hbb]; simp [Ctx.plug],
                 hbody'.tail ⟨C', x, bb, v, rfl, rfl⟩⟩
      | _ => simp [Ctx.plug] at hC

/-- One `materializeStep` preserves cross-side policy equality (β version:
    `level_count_eq` instead of `level_envs_eq`). Mirror of the `private`
    `materializeStep_cross_side_policies`. -/
theorem materializeStep_policiesEqβ (T_a T_b : TowerState)
    (h_count : T_a.levels.length = T_b.levels.length)
    (h_pols : ∀ m, T_a.policyAt? m = T_b.policyAt? m) :
    ∀ m, (materializeStep T_a).policyAt? m = (materializeStep T_b).policyAt? m := by
  intro m
  unfold materializeStep TowerState.policyAt? TowerState.levelAt?
  by_cases h_in : m < T_a.levels.length
  · rw [List.getElem?_append_left h_in, List.getElem?_append_left (h_count ▸ h_in)]
    exact h_pols m
  · by_cases h_eq : m = T_a.levels.length
    · subst h_eq
      rw [List.getElem?_append_right (Nat.le_refl _),
          List.getElem?_append_right (h_count ▸ Nat.le_refl _)]
      simp [h_count]
    · rw [List.getElem?_eq_none (by simp [List.length_append]; omega),
          List.getElem?_eq_none (by simp [List.length_append]; omega)]

/-- Iterating `materializeStep` `k` times adds exactly `k` levels. -/
theorem materializeStep_iter_levels_length (T : TowerState) (k : Nat) :
    (Nat.fold k (fun _ _ T' => materializeStep T') T).levels.length = T.levels.length + k := by
  induction k with
  | zero => simp [Nat.fold]
  | succ k ih => simp only [Nat.fold]; rw [materializeStep_levels_length, ih]; omega

/-- Iterating `materializeStep` preserves cross-side policy equality. -/
theorem materializeStep_iter_policiesEqβ (T_a T_b : TowerState) (k : Nat)
    (h_count : T_a.levels.length = T_b.levels.length)
    (h_pols : ∀ m, T_a.policyAt? m = T_b.policyAt? m) :
    ∀ m, (Nat.fold k (fun _ _ T' => materializeStep T') T_a).policyAt? m =
         (Nat.fold k (fun _ _ T' => materializeStep T') T_b).policyAt? m := by
  induction k with
  | zero => simpa [Nat.fold] using h_pols
  | succ k ih =>
      simp only [Nat.fold]
      have h_count' : (Nat.fold k (fun _ _ T' => materializeStep T') T_a).levels.length =
          (Nat.fold k (fun _ _ T' => materializeStep T') T_b).levels.length := by
        rw [materializeStep_iter_levels_length, materializeStep_iter_levels_length, h_count]
      exact materializeStep_policiesEqβ _ _ h_count' ih

/-- Cross-side: parallel `materialize` results have equal `policyAt?` at all
    indices (β version: needs `level_count_eq`, not `heap_len_eq`). -/
theorem materialize_policiesEqβ {T_a T_b T_a' T_b' : TowerState} {n : Nat}
    (h_count : T_a.levels.length = T_b.levels.length)
    (h_pols : ∀ m, T_a.policyAt? m = T_b.policyAt? m)
    (h_mat_a : T_a.materialize n = some T_a') (h_mat_b : T_b.materialize n = some T_b') :
    ∀ m, T_a'.policyAt? m = T_b'.policyAt? m := by
  unfold TowerState.materialize at h_mat_a h_mat_b
  by_cases h1 : n ≥ Tower.maxDepth
  · simp [h1] at h_mat_a
  · simp [h1] at h_mat_a h_mat_b
    by_cases h2 : T_a.levels.length > n
    · have h2_b : T_b.levels.length > n := h_count ▸ h2
      simp [h2] at h_mat_a; simp [h2_b] at h_mat_b
      obtain rfl := h_mat_a.symm; obtain rfl := h_mat_b.symm; exact h_pols
    · have h2_b : ¬ T_b.levels.length > n := h_count ▸ h2
      simp [h2] at h_mat_a; simp [h2_b] at h_mat_b
      obtain rfl := h_mat_a.symm; obtain rfl := h_mat_b.symm
      have h_eq_k : n + 1 - T_a.levels.length = n + 1 - T_b.levels.length := by rw [h_count]
      rw [h_eq_k]
      exact materializeStep_iter_policiesEqβ T_a T_b _ h_count h_pols

/-! ## 7f. The `.em` eval case under `WFCtxTβ` — the first reflective case

`.em body` materializes `level + 1`, reads the up-env, and evaluates `body`
there. The β simulation threads: both sides materialize (cross-side
`some_iff`, reused), the up-envs are `EnvVisβ`-related and the level/policy
structure is preserved (`materialize_MatInvβ` §7d + `materialize_policiesEqβ`
§7e + `Frame`'s single-side preservation), giving `WFCtxTβ` at `level + 1` for
the eval IH; the output `WFCtxTβ` at `level` is rebuilt from the body's output
(level-structure fields are level-agnostic) plus lifting the ambient-env fields
across the materialize+body `HeapEvolutionβ`. The β-port of `frame_tower`'s
`.em` case (`Frame.lean:1669`), but far shorter — the heap-content level
reconstruction is now packaged in `materialize_MatInvβ`. -/

/-- A materialized level present on one side is present on the other (equal
    level counts). -/
theorem envAt?_some_cross (T_a T_b : TowerState) (n : Nat) (e : Env)
    (h_count : T_a.levels.length = T_b.levels.length) (h : T_a.envAt? n = some e) :
    ∃ e', T_b.envAt? n = some e' := by
  unfold TowerState.envAt? TowerState.levelAt? at h ⊢
  rw [Option.map_eq_some_iff] at h
  obtain ⟨ls, hls, _⟩ := h
  have hlt : n < T_b.levels.length := h_count ▸ (List.getElem?_eq_some_iff.mp hls).1
  exact ⟨(T_b.levels[n]'hlt).env, by rw [List.getElem?_eq_getElem hlt]; rfl⟩

/-- The eval clause over `WFCtxTβ` — the β-analog of `FrameStmtT`'s eval clause
    with the full reflective context. The cases proved over `WFβ` in
    `LamBeta.lean` (atoms / `.letE` / `.ifte` / `.seq`) re-thread over this
    wrapper (`WFβ` is `WFCtxTβ` minus the level/policy fields, which those cases
    preserve); this file proves the genuinely reflective `.em` case on it. -/
def FrameβEvalStmtW (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (exp_a exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    BetaRel exp_a exp_b →
    PolicyTableRespectsBisimT ptable →
    WFCtxTβ env_a env_b T_a T_b level →
    eval n ptable level exp_a env_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      eval n ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap

/-- **The `.em` case, on `FrameβEvalStmtW`.** Taking the eval IH, the reflective
    level-shift is discharged: materialize cross-side, build `WFCtxTβ` at
    `level + 1` (its level fields from §7d/§7e), run `body` by the IH, rebuild
    the output `WFCtxTβ` at `level`. -/
theorem frameβ_em_eval (n : Nat) (ptable : PolicyTable) (level : Nat)
    (body exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtW n)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.em body) exp_b)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.em body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨body', rfl, hβ_body⟩ := hβ.em_inv
  simp only [eval] at heval
  cases hm_a : T_a.materialize (level + 1) with
  | none => simp [hm_a] at heval
  | some T_a_mat =>
      simp only [hm_a] at heval
      cases he_a : T_a_mat.envAt? (level + 1) with
      | none => simp [he_a] at heval
      | some upEnv_a =>
          simp only [he_a] at heval
          -- b-side materializes (cross-side some-iff is heap/env-agnostic)
          have hm_b_some : (T_b.materialize (level + 1)).isSome := by
            cases h_some : T_b.materialize (level + 1) with
            | none =>
                rw [(T_a.materialize_cross_side_some_iff T_b _).mpr h_some] at hm_a; cases hm_a
            | some _ => simp
          obtain ⟨T_b_mat, hm_b⟩ := Option.isSome_iff_exists.mp hm_b_some
          -- the materialized cross-side level invariant (§7d) + policies (§7e)
          obtain ⟨hhm_a, hhm_b, hcount_m, hvalid_a_m, hvalid_b_m, hvisβ_m⟩ :=
            materialize_MatInvβ ⟨h_ctx.hv_a, h_ctx.hv_b, h_ctx.level_count_eq,
              h_ctx.level_envs_valid_a, h_ctx.level_envs_valid_b, h_ctx.level_envs_visβ⟩ hm_a hm_b
          obtain ⟨upEnv_b, he_b⟩ := envAt?_some_cross T_a_mat T_b_mat (level + 1) upEnv_a hcount_m he_a
          have hpolseq_m := materialize_policiesEqβ h_ctx.level_count_eq h_ctx.policies_eq hm_a hm_b
          have hrespall_m := materialize_policies_resp_preserves T_a T_a_mat (level + 1)
            PolicyRespectsBisimT hm_a h_ctx.policies_resp_all rejectAllPolicy_respects_bisimT
          -- `WFCtxTβ` at level+1 for the body call
          have h_ctx_up : WFCtxTβ upEnv_a upEnv_b T_a_mat T_b_mat (level + 1) :=
            { policy_eq_at := hpolseq_m (level + 1)
              hv_a := hhm_a, hv_b := hhm_b
              ev_a := hvalid_a_m (level + 1) upEnv_a he_a
              ev_b := hvalid_b_m (level + 1) upEnv_b he_b
              policy_resp := fun p hp => hrespall_m (level + 1) p hp
              env_visβ := hvisβ_m (level + 1) upEnv_a upEnv_b he_a he_b
              level_envs_valid_a := hvalid_a_m, level_envs_valid_b := hvalid_b_m
              level_count_eq := hcount_m
              policies_eq := hpolseq_m
              policies_resp_all := hrespall_m
              level_envs_visβ := hvisβ_m }
          -- run the body at level+1 by the eval IH
          obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_ctx_out_up, h_he_body, hv_ra, hv_rb⟩ :=
            ih ptable (level + 1) body body' upEnv_a upEnv_b T_a_mat T_b_mat r_a T_a'
              hβ_body hresp_pt h_ctx_up heval
          -- HeapEvolutionβ: materialize step, then the body
          have h_he_chain : HeapEvolutionβ T_a T_b T_a' T_b' :=
            (HeapEvolutionβ.from_heapExt h_ctx.hv_a h_ctx.hv_b
              (T_a.materialize_heap_extends T_a_mat (level + 1) hm_a)
              (T_b.materialize_heap_extends T_b_mat (level + 1) hm_b)).trans h_he_body
          refine ⟨r_b, T_b', ?_, h_vv_r, ?_, h_he_chain, hv_ra, hv_rb⟩
          · simp only [eval, hm_b, he_b]; exact h_eval_b
          · -- rebuild `WFCtxTβ` at the caller's level
            exact
            { policy_eq_at := h_ctx_out_up.policies_eq level
              hv_a := h_ctx_out_up.hv_a, hv_b := h_ctx_out_up.hv_b
              ev_a := h_ctx.ev_a.length_mono h_he_chain.len_a
              ev_b := h_ctx.ev_b.length_mono h_he_chain.len_b
              policy_resp := fun p hp => h_ctx_out_up.policies_resp_all level p hp
              env_visβ := h_he_chain.envVisβ_preserve env_a env_b h_ctx.ev_a h_ctx.ev_b h_ctx.env_visβ
              level_envs_valid_a := h_ctx_out_up.level_envs_valid_a
              level_envs_valid_b := h_ctx_out_up.level_envs_valid_b
              level_count_eq := h_ctx_out_up.level_count_eq
              policies_eq := h_ctx_out_up.policies_eq
              policies_resp_all := h_ctx_out_up.policies_resp_all
              level_envs_visβ := h_ctx_out_up.level_envs_visβ }

/-! ## 7g. The non-recursive eval cases over `WFCtxTβ`

The atoms (`.num` / `.bool`), variable lookup (`.var`), and closure formation
(`.lam`) on `FrameβEvalStmtW`. None changes the tower state, so the output
`WFCtxTβ` is the input verbatim — these are the β-analogs of `LamBeta`'s
`frameβ_num_case` / `frameβ_var_case` / `frameβ_lam_case` (proved over `WFβ`),
re-stated over the full reflective wrapper. The recursive gate-free cases
(`.letE` / `.ifte` / `.seq`) re-thread over `WFCtxTβ` by the same reassembly as
`frameβ_em_eval` (level-structure fields from the sub-eval outputs, ambient-env
fields lifted across `HeapEvolutionβ`), needing a `MatInvβ`-across-alloc lift;
deferred with the reflective `.set` / `applyVia` cases. -/

/-- `.num` on `FrameβEvalStmtW` (state unchanged ⟹ output context = input). -/
theorem frameβ_num_caseW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (i : Int) (exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.num i) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.num i) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  have hb := hβ.num_eq; subst hb
  simp only [eval, Option.some.injEq, Prod.mk.injEq] at heval
  obtain ⟨hr, ht⟩ := heval; subst hr; subst ht
  exact ⟨.num i, T_b, by simp [eval], (fun m => by cases m <;> simp [ValVisβ_aux]),
         h_ctx, HeapEvolutionβ.refl _ _, trivial, trivial⟩

/-- `.bool` on `FrameβEvalStmtW`. -/
theorem frameβ_bool_caseW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (c : Bool) (exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.bool c) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.bool c) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  have hb := hβ.bool_eq; subst hb
  simp only [eval, Option.some.injEq, Prod.mk.injEq] at heval
  obtain ⟨hr, ht⟩ := heval; subst hr; subst ht
  exact ⟨.bool c, T_b, by simp [eval], (fun m => by cases m <;> simp [ValVisβ_aux]),
         h_ctx, HeapEvolutionβ.refl _ _, trivial, trivial⟩

/-- `.var` on `FrameβEvalStmtW`: the lookup threads through `env_visβ` to a
    `ValVisβ`-related value; the state is unchanged. -/
theorem frameβ_var_caseW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (y : String) (exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.var y) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.var y) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  have hb := hβ.var_eq; subst hb
  simp only [eval] at heval
  cases hla : env_a.lookup y with
  | none => simp [hla] at heval
  | some idx_a =>
    simp only [hla] at heval
    cases hpa : T_a.heap[idx_a]? with
    | none => simp [hpa] at heval
    | some va =>
      simp only [hpa, Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, ht⟩ := heval; subst hr; subst ht
      have he := h_ctx.env_visβ 1 y
      simp only [hla] at he
      cases hlb : env_b.lookup y with
      | none => simp [hlb] at he
      | some idx_b =>
        simp only [hlb, hpa] at he
        cases hpb : T_b.heap[idx_b]? with
        | none => simp [hpb] at he
        | some vb =>
          refine ⟨vb, T_b, by simp only [eval, hlb, hpb], (fun m => ?_), h_ctx,
                  HeapEvolutionβ.refl _ _, h_ctx.hv_a idx_a va hpa, h_ctx.hv_b idx_b vb hpb⟩
          have hm := h_ctx.env_visβ m y
          simp only [hla, hlb, hpa, hpb] at hm
          exact hm

/-- `.lam` on `FrameβEvalStmtW`: closure formation (state unchanged); the
    closures relate by `ValVisβ_lam_closures` (`BetaRel` bodies + `env_visβ`). -/
theorem frameβ_lam_caseW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (ps : List String) (body exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.lam ps body) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.lam ps body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  rw [eval_lam_closure] at heval
  injection heval with heval'; injection heval' with hr ht; subst hr; subst ht
  obtain ⟨body', rfl, hbody⟩ := hβ.lam_inv
  exact ⟨.closure ps body' env_b, T_b, eval_lam_closure n ptable level ps body' env_b T_b,
         ValVisβ_lam_closures ps body body' env_a env_b T_a.heap T_b.heap hbody h_ctx.env_visβ,
         h_ctx, HeapEvolutionβ.refl _ _, h_ctx.ev_a, h_ctx.ev_b⟩

/-! ## 7h. The recursive gate-free eval cases over `WFCtxTβ`

`.ifte` / `.seq` / `.letE` on `FrameβEvalStmtW`, re-threading the `WFβ`-based
proofs of `LamBeta` onto the full reflective wrapper. `.ifte` / `.seq` keep the
ambient env fixed, so the output `WFCtxTβ` is the last sub-eval's output
verbatim (the level/policy fields ride through the eval IH). `.letE` binds a
fresh variable, so its body call needs a `WFCtxTβ` over the cons-extended env;
`level_fields_alloc` lifts the level fields across the allocation (levels
unchanged, heaps +1) and `EnvVisβ_alloc_cons` supplies the env relation. With
§7f (`.em`) and §7g (atoms) this closes the gate-free eval clause over
`WFCtxTβ`; only the reflective `.set` / `.app` remain. -/

/-- `.ifte` on `FrameβEvalStmtW`. -/
theorem frameβ_ifte_evalW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (c t e exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtW n) (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.ifte c t e) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.ifte c t e) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨c', t', e', rfl, hβ_c, hβ_t, hβ_e⟩ := hβ.ifte_inv
  cases hc : eval n ptable level c env_a T_a with
  | none => rw [eval_ifte_none n ptable level c t e env_a T_a hc] at heval; simp at heval
  | some pr =>
    obtain ⟨cv_a, T_c_a⟩ := pr
    rw [eval_ifte_step n ptable level c t e env_a T_a T_c_a cv_a hc] at heval
    obtain ⟨cv_b, T_c_b, h_eval_c_b, h_vv_c, h_ctx_c, h_he_c, _hv_ca, _hv_cb⟩ :=
      ih ptable level c c' env_a env_b T_a T_b cv_a T_c_a hβ_c hresp_pt h_ctx hc
    have hβ_branch : BetaRel (ifteBranch cv_a t e) (ifteBranch cv_b t' e') := by
      by_cases hbf : cv_a = .bool false
      · have hbf_b : cv_b = .bool false := (ValVisβ_bool_false_iff h_vv_c).mp hbf
        subst hbf; subst hbf_b; exact hβ_e
      · have hbf_b : cv_b ≠ .bool false :=
          fun hc' => hbf ((ValVisβ_bool_false_iff h_vv_c).mpr hc')
        rw [ifteBranch_ne t e hbf, ifteBranch_ne t' e' hbf_b]; exact hβ_t
    obtain ⟨r_b, T_b', h_eval_branch_b, h_vv_r, h_ctx_out, h_he_branch, hv_ra, hv_rb⟩ :=
      ih ptable level (ifteBranch cv_a t e) (ifteBranch cv_b t' e')
        env_a env_b T_c_a T_c_b r_a T_a' hβ_branch hresp_pt h_ctx_c heval
    refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_out, h_he_c.trans h_he_branch, hv_ra, hv_rb⟩
    rw [eval_ifte_step n ptable level c' t' e' env_b T_b T_c_b cv_b h_eval_c_b]
    exact h_eval_branch_b

/-- `.seq` on `FrameβEvalStmtW`. -/
theorem frameβ_seq_evalW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (exps : List Expr) (exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtW n) (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.seq exps) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.seq exps) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  cases exps with
  | nil =>
      have hb := hβ.seq_nil_inv; subst hb
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, ht⟩ := heval; subst hr; subst ht
      exact ⟨.nilV, T_b, by simp only [eval], fun m => by cases m <;> simp [ValVisβ_aux],
             h_ctx, HeapEvolutionβ.refl _ _, trivial, trivial⟩
  | cons e rest =>
      cases rest with
      | nil =>
          obtain ⟨e', rest', rfl, hβ_e, hβ_rest⟩ := hβ.seq_cons_inv
          have hr : rest' = [] := Expr.seq.inj hβ_rest.seq_nil_inv
          subst hr
          simp only [eval] at heval
          obtain ⟨r_b, T_b', h_eval_e_b, h_vv_r, h_ctx_out, h_he, hv_ra, hv_rb⟩ :=
            ih ptable level e e' env_a env_b T_a T_b r_a T_a' hβ_e hresp_pt h_ctx heval
          refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_out, h_he, hv_ra, hv_rb⟩
          simp only [eval]; exact h_eval_e_b
      | cons f rest2 =>
          obtain ⟨e', rest', rfl, hβ_e, hβ_rest⟩ := hβ.seq_cons_inv
          obtain ⟨f', rest2', hr'⟩ : ∃ f' rest2', rest' = f' :: rest2' := by
            obtain ⟨f', rest2', hb_eq, _, _⟩ := hβ_rest.seq_cons_inv
            exact ⟨f', rest2', Expr.seq.inj hb_eq⟩
          subst hr'
          cases hee : eval n ptable level e env_a T_a with
          | none =>
              rw [eval_seq_cons_none n ptable level e f rest2 env_a T_a hee] at heval
              simp at heval
          | some pr =>
              obtain ⟨v_a, T_e_a⟩ := pr
              rw [eval_seq_cons_step n ptable level e f rest2 env_a T_a T_e_a v_a hee] at heval
              obtain ⟨v_b, T_e_b, h_eval_e_b, _h_vv_v, h_ctx_e, h_he_e, _, _⟩ :=
                ih ptable level e e' env_a env_b T_a T_b v_a T_e_a hβ_e hresp_pt h_ctx hee
              obtain ⟨r_b, T_b', h_eval_rest_b, h_vv_r, h_ctx_out, h_he_rest, hv_ra, hv_rb⟩ :=
                ih ptable level (.seq (f :: rest2)) (.seq (f' :: rest2'))
                  env_a env_b T_e_a T_e_b r_a T_a' hβ_rest hresp_pt h_ctx_e heval
              refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_out, h_he_e.trans h_he_rest, hv_ra, hv_rb⟩
              rw [eval_seq_cons_step n ptable level e' f' rest2' env_b T_b T_e_b v_b h_eval_e_b]
              exact h_eval_rest_b

/-- The level fields (`level_envs_valid` both sides + `level_envs_visβ`) lift
    across a one-cell allocation on each side (levels unchanged, heaps +1). The
    `.letE` body call's `WFCtxTβ` level fields. -/
theorem level_fields_alloc {T_a T_b : TowerState} (v_a v_b : Val)
    (hh_a : HeapValid T_a.heap) (hh_b : HeapValid T_b.heap)
    (hva : ∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap)
    (hvb : ∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap)
    (hvisβ : ∀ n ea eb, T_a.envAt? n = some ea → T_b.envAt? n = some eb →
        EnvVisβ ea eb T_a.heap T_b.heap) :
    (∀ n env, T_a.envAt? n = some env → EnvValid env (T_a.heap ++ [v_a])) ∧
    (∀ n env, T_b.envAt? n = some env → EnvValid env (T_b.heap ++ [v_b])) ∧
    (∀ n ea eb, T_a.envAt? n = some ea → T_b.envAt? n = some eb →
        EnvVisβ ea eb (T_a.heap ++ [v_a]) (T_b.heap ++ [v_b])) := by
  refine ⟨fun n env hen => EnvValid.heap_extends (hva n env hen) ⟨[v_a], rfl⟩,
          fun n env hen => EnvValid.heap_extends (hvb n env hen) ⟨[v_b], rfl⟩, ?_⟩
  intro n ea eb hena henb
  exact EnvVisβ_extends ea eb T_a.heap T_b.heap [v_a] [v_b] hh_a hh_b
    (hva n ea hena) (hvb n eb henb) (hvisβ n ea eb hena henb)

/-- `.letE` on `FrameβEvalStmtW`: the allocating binder. Re-thread of
    `LamBeta`'s `frameβ_letE_eval` onto `WFCtxTβ` — the body call's level fields
    come from `level_fields_alloc`, its env relation from `EnvVisβ_alloc_cons`,
    and the output `WFCtxTβ` is rebuilt from the body output (level fields) plus
    the input ambient-env fields lifted across the chained `HeapEvolutionβ`. -/
theorem frameβ_letE_evalW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (e1 body exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtW n) (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.letE x e1 body) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.letE x e1 body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨e1', body', rfl, hβ_e, hβ_body⟩ := hβ.letE_inv
  simp only [eval] at heval
  cases he : eval n ptable level e1 env_a T_a with
  | none => rw [he] at heval; simp at heval
  | some pr =>
    obtain ⟨v_a, T_a_inner⟩ := pr
    rw [he] at heval
    obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner, hv_va, hv_vb⟩ :=
      ih ptable level e1 e1' env_a env_b T_a T_b v_a T_a_inner hβ_e hresp_pt h_ctx he
    simp only [TowerState.alloc, Heap.alloc] at heval
    -- alloc validity (body-agnostic; verbatim from `frameβ_letE_eval`)
    have h_lookup_a : (T_a_inner.heap ++ [v_a])[T_a_inner.heap.length]? = some v_a := getElem?_snoc _ _
    have h_lookup_b : (T_b_inner.heap ++ [v_b])[T_b_inner.heap.length]? = some v_b := getElem?_snoc _ _
    have hh_a_alloc : HeapValid (T_a_inner.heap ++ [v_a]) := by
      intro i v hp
      by_cases h_lt : i < T_a_inner.heap.length
      · have hp_old : T_a_inner.heap[i]? = some v := by
          rw [← getElem?_prefix T_a_inner.heap [v_a] i h_lt]; exact hp
        exact ValValid.heap_extends v (h_ctx_inner.hv_a i v hp_old) ⟨[v_a], rfl⟩
      · have h_eq : i = T_a_inner.heap.length := by
          have h_le : i < (T_a_inner.heap ++ [v_a]).length := by
            rw [List.getElem?_eq_some_iff] at hp; obtain ⟨h, _⟩ := hp; exact h
          simp [List.length_append] at h_le; omega
        subst h_eq; rw [h_lookup_a] at hp; simp only [Option.some.injEq] at hp; subst hp
        exact ValValid.heap_extends v_a hv_va ⟨[v_a], rfl⟩
    have hh_b_alloc : HeapValid (T_b_inner.heap ++ [v_b]) := by
      intro i v hp
      by_cases h_lt : i < T_b_inner.heap.length
      · have hp_old : T_b_inner.heap[i]? = some v := by
          rw [← getElem?_prefix T_b_inner.heap [v_b] i h_lt]; exact hp
        exact ValValid.heap_extends v (h_ctx_inner.hv_b i v hp_old) ⟨[v_b], rfl⟩
      · have h_eq : i = T_b_inner.heap.length := by
          have h_le : i < (T_b_inner.heap ++ [v_b]).length := by
            rw [List.getElem?_eq_some_iff] at hp; obtain ⟨h, _⟩ := hp; exact h
          simp [List.length_append] at h_le; omega
        subst h_eq; rw [h_lookup_b] at hp; simp only [Option.some.injEq] at hp; subst hp
        exact ValValid.heap_extends v_b hv_vb ⟨[v_b], rfl⟩
    have hev_a' : EnvValid (.cons x T_a_inner.heap.length env_a) (T_a_inner.heap ++ [v_a]) :=
      envValid_cons_fresh x v_a env_a T_a_inner.heap h_ctx_inner.ev_a
    have hev_b' : EnvValid (.cons x T_b_inner.heap.length env_b) (T_b_inner.heap ++ [v_b]) :=
      envValid_cons_fresh x v_b env_b T_b_inner.heap h_ctx_inner.ev_b
    have h_env' : EnvVisβ (.cons x T_a_inner.heap.length env_a) (.cons x T_b_inner.heap.length env_b)
        (T_a_inner.heap ++ [v_a]) (T_b_inner.heap ++ [v_b]) :=
      EnvVisβ_alloc_cons x env_a env_b v_a v_b T_a_inner.heap T_b_inner.heap
        h_ctx_inner.hv_a h_ctx_inner.hv_b h_ctx_inner.ev_a h_ctx_inner.ev_b hv_va hv_vb h_vv_v
        h_ctx_inner.env_visβ
    -- lift the level fields across the allocation
    obtain ⟨hlva', hlvb', hlvisβ'⟩ :=
      level_fields_alloc v_a v_b h_ctx_inner.hv_a h_ctx_inner.hv_b
        h_ctx_inner.level_envs_valid_a h_ctx_inner.level_envs_valid_b h_ctx_inner.level_envs_visβ
    -- `WFCtxTβ` for the body call
    have h_ctx_alloc : WFCtxTβ (.cons x T_a_inner.heap.length env_a)
        (.cons x T_b_inner.heap.length env_b)
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } level :=
      { policy_eq_at := h_ctx_inner.policy_eq_at
        hv_a := hh_a_alloc, hv_b := hh_b_alloc, ev_a := hev_a', ev_b := hev_b'
        policy_resp := h_ctx_inner.policy_resp
        env_visβ := h_env'
        level_envs_valid_a := hlva', level_envs_valid_b := hlvb'
        level_count_eq := h_ctx_inner.level_count_eq
        policies_eq := h_ctx_inner.policies_eq
        policies_resp_all := h_ctx_inner.policies_resp_all
        level_envs_visβ := hlvisβ' }
    obtain ⟨r_b, T_b', h_eval_b_b, h_vv_r, h_ctx_body, h_he_body, hv_ra, hv_rb⟩ :=
      ih ptable level body body'
        (.cons x T_a_inner.heap.length env_a) (.cons x T_b_inner.heap.length env_b)
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } r_a T_a'
        hβ_body hresp_pt h_ctx_alloc heval
    -- chain the heap evolutions: e, then alloc, then body
    have h_he_alloc : HeapEvolutionβ T_a_inner T_b_inner
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } :=
      HeapEvolutionβ.from_heapExt h_ctx_inner.hv_a h_ctx_inner.hv_b ⟨[v_a], rfl⟩ ⟨[v_b], rfl⟩
    have h_he_chain : HeapEvolutionβ T_a T_b T_a' T_b' :=
      h_he_inner.trans (h_he_alloc.trans h_he_body)
    refine ⟨r_b, T_b', ?_, h_vv_r, ?_, h_he_chain, hv_ra, hv_rb⟩
    · simp only [eval, h_eval_e_b, TowerState.alloc, Heap.alloc]; exact h_eval_b_b
    · -- rebuild the ambient `WFCtxTβ` (level fields from body output; env fields lifted)
      exact
      { policy_eq_at := h_ctx_body.policy_eq_at
        hv_a := h_ctx_body.hv_a, hv_b := h_ctx_body.hv_b
        ev_a := h_ctx.ev_a.length_mono h_he_chain.len_a
        ev_b := h_ctx.ev_b.length_mono h_he_chain.len_b
        policy_resp := h_ctx_body.policy_resp
        env_visβ := h_he_chain.envVisβ_preserve env_a env_b h_ctx.ev_a h_ctx.ev_b h_ctx.env_visβ
        level_envs_valid_a := h_ctx_body.level_envs_valid_a
        level_envs_valid_b := h_ctx_body.level_envs_valid_b
        level_count_eq := h_ctx_body.level_count_eq
        policies_eq := h_ctx_body.policies_eq
        policies_resp_all := h_ctx_body.policies_resp_all
        level_envs_visβ := h_ctx_body.level_envs_visβ }

/-! ## 7i. The tower invariant `TowerInvβ`, and the level-tracking `applyDirect`

`applyVia` / `applyDirect` take `op`/`args` but no ambient env; their cross-side
context is the *tower* invariant — the env-agnostic level/policy/heap fields of
`WFCtxTβ`. `applyDirect`'s gate-free clause (`LamBeta`, over `WFβ`) tracked only
`HeapValid` because it never *directly* touches levels — but its closure-body
eval can `.em`-materialize, so for the mutual statement the clause must carry the
full level invariant. `TowerInvβ` packages it; `WFCtxTβ.ofTower` / `.toTower`
convert at the body-eval boundary; `level_fields_extend` lifts the level fields
across the arg-allocation heap extension. -/

/-- The env-agnostic cross-side tower invariant — `WFCtxTβ` minus the ambient
    env fields. The context `applyDirect` / `applyVia` thread. -/
structure TowerInvβ (T_a T_b : TowerState) : Prop where
  hv_a : HeapValid T_a.heap
  hv_b : HeapValid T_b.heap
  count : T_a.levels.length = T_b.levels.length
  valid_a : ∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap
  valid_b : ∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap
  visβ : ∀ n ea eb, T_a.envAt? n = some ea → T_b.envAt? n = some eb →
    EnvVisβ ea eb T_a.heap T_b.heap
  pol_eq : ∀ n, T_a.policyAt? n = T_b.policyAt? n
  pol_resp : ∀ n p, T_a.policyAt? n = some p → PolicyRespectsBisimT p

/-- Build a `WFCtxTβ` from a `TowerInvβ` and an env pair's own fields. -/
def WFCtxTβ.ofTower {T_a T_b : TowerState} {env_a env_b : Env} {level : Nat}
    (h : TowerInvβ T_a T_b)
    (ev_a : EnvValid env_a T_a.heap) (ev_b : EnvValid env_b T_b.heap)
    (env_visβ : EnvVisβ env_a env_b T_a.heap T_b.heap) :
    WFCtxTβ env_a env_b T_a T_b level :=
  { policy_eq_at := h.pol_eq level, hv_a := h.hv_a, hv_b := h.hv_b, ev_a := ev_a, ev_b := ev_b
    policy_resp := fun p hp => h.pol_resp level p hp, env_visβ := env_visβ
    level_envs_valid_a := h.valid_a, level_envs_valid_b := h.valid_b
    level_count_eq := h.count, policies_eq := h.pol_eq, policies_resp_all := h.pol_resp
    level_envs_visβ := h.visβ }

/-- Extract the tower invariant from a `WFCtxTβ`. -/
def WFCtxTβ.toTower {T_a T_b : TowerState} {env_a env_b : Env} {level : Nat}
    (h : WFCtxTβ env_a env_b T_a T_b level) : TowerInvβ T_a T_b :=
  ⟨h.hv_a, h.hv_b, h.level_count_eq, h.level_envs_valid_a, h.level_envs_valid_b,
   h.level_envs_visβ, h.policies_eq, h.policies_resp_all⟩

/-- **The diagonal `WFCtxTβ`** — reflexivity of the cross-side context invariant.
    From a single tower/env's well-formedness (heap valid, env valid, level envs
    valid, policies respect bisim), `WFCtxTβ env env T T level` holds: the cross-
    side fields collapse to reflexivity (`EnvVisβ_refl`; equal level counts and
    policies). This instantiates the *cross-side* fundamental lemma *diagonally*
    to reason about a single-sided `ObsConv` observation (step 4). -/
theorem WFCtxTβ.refl {env : Env} {T : TowerState} {level : Nat}
    (hh : HeapValid T.heap) (hev : EnvValid env T.heap)
    (hlv : ∀ n e, T.envAt? n = some e → EnvValid e T.heap)
    (hpr : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) :
    WFCtxTβ env env T T level :=
  { policy_eq_at := rfl, hv_a := hh, hv_b := hh, ev_a := hev, ev_b := hev
    policy_resp := fun p hp => hpr level p hp
    env_visβ := EnvVisβ_refl hh hev
    level_envs_valid_a := hlv, level_envs_valid_b := hlv
    level_count_eq := rfl, policies_eq := fun _ => rfl, policies_resp_all := hpr
    level_envs_visβ := fun n ea eb hea heb => by
      obtain rfl : ea = eb := by rw [hea] at heb; exact (Option.some.inj heb)
      exact EnvVisβ_refl hh (hlv n ea hea) }

/-- The level fields lift across an arbitrary heap extension on each side
    (generalizes `level_fields_alloc` from a single cell). -/
theorem level_fields_extend {T_a T_b : TowerState} (ext_a ext_b : Heap)
    (hh_a : HeapValid T_a.heap) (hh_b : HeapValid T_b.heap)
    (hva : ∀ n env, T_a.envAt? n = some env → EnvValid env T_a.heap)
    (hvb : ∀ n env, T_b.envAt? n = some env → EnvValid env T_b.heap)
    (hvisβ : ∀ n ea eb, T_a.envAt? n = some ea → T_b.envAt? n = some eb →
        EnvVisβ ea eb T_a.heap T_b.heap) :
    (∀ n env, T_a.envAt? n = some env → EnvValid env (T_a.heap ++ ext_a)) ∧
    (∀ n env, T_b.envAt? n = some env → EnvValid env (T_b.heap ++ ext_b)) ∧
    (∀ n ea eb, T_a.envAt? n = some ea → T_b.envAt? n = some eb →
        EnvVisβ ea eb (T_a.heap ++ ext_a) (T_b.heap ++ ext_b)) := by
  refine ⟨fun n env hen => EnvValid.heap_extends (hva n env hen) ⟨ext_a, rfl⟩,
          fun n env hen => EnvValid.heap_extends (hvb n env hen) ⟨ext_b, rfl⟩, ?_⟩
  intro n ea eb hena henb
  exact EnvVisβ_extends ea eb T_a.heap T_b.heap ext_a ext_b hh_a hh_b
    (hva n ea hena) (hvb n eb henb) (hvisβ n ea eb hena henb)

/-- The level-tracking `applyDirect` clause: gate-free `applyDirect` over
    `TowerInvβ` (the body eval can materialize, so the level invariant is
    threaded). The β-analog of `FrameStmtT`'s `applyDirect` conjunct, with the
    `TowerCross` output as `TowerInvβ`. -/
def FrameβApplyDirectStmtW (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (op_a op_b : Val)
    (args_a args_b : List Val) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    TowerInvβ T_a T_b →
    ValVisβ op_a op_b T_a.heap T_b.heap →
    ListValVisβ args_a args_b T_a.heap T_b.heap →
    ValValid op_a T_a.heap → ValValid op_b T_b.heap →
    ListValValid args_a T_a.heap → ListValValid args_b T_b.heap →
    applyDirect n ptable level op_a args_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      applyDirect n ptable level op_b args_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ TowerInvβ T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap

/-- **The level-tracking `applyDirect` clause, proved.** Re-thread of the
    gate-free `frameβ_applyDirect_eval` (`LamBeta` §6j) onto `TowerInvβ`: the
    closure case runs its body via the level-tracking eval IH `FrameβEvalStmtW`
    (so `.em` inside a closure body is handled), with the level fields lifted
    across the argument allocation by `level_fields_extend`; `.builtinBaseApply`
    re-dispatches via the `applyDirect`-W IH; `.prim` leaves the state (hence
    `TowerInvβ`) unchanged. The applyDirect node of the mutual `FrameStmtβ`. -/
theorem frameβ_applyDirect_evalW (n : Nat)
    (ih_eval : FrameβEvalStmtW n) (ih_ad : FrameβApplyDirectStmtW n) :
    FrameβApplyDirectStmtW (n + 1) := by
  intro ptable level op_a op_b args_a args_b T_a T_b r_a T_a'
        hresp_pt h_tower h_vv_op h_lvv hv_opa hv_opb hv_argsa hv_argsb heval
  have h_vv1 := h_vv_op 1
  cases op_a with
  | num _ => simp [applyDirect] at heval
  | bool _ => simp [applyDirect] at heval
  | nilV => simp [applyDirect] at heval
  | sym _ => simp [applyDirect] at heval
  | cons _ _ => simp [applyDirect] at heval
  | prim name =>
      have h_opb : op_b = .prim name := by
        cases op_b with
        | prim n' => simp only [ValVisβ_aux] at h_vv1; rw [h_vv1]
        | num _ => simp [ValVisβ_aux] at h_vv1
        | bool _ => simp [ValVisβ_aux] at h_vv1
        | nilV => simp [ValVisβ_aux] at h_vv1
        | sym _ => simp [ValVisβ_aux] at h_vv1
        | cons _ _ => simp [ValVisβ_aux] at h_vv1
        | closure _ _ _ => simp [ValVisβ_aux] at h_vv1
        | builtinBaseApply => simp [ValVisβ_aux] at h_vv1
      subst h_opb
      simp only [applyDirect] at heval
      cases hp_a : applyPrim name args_a with
      | none => rw [hp_a] at heval; simp at heval
      | some v_a' =>
          rw [hp_a] at heval
          simp only [Option.some.injEq, Prod.mk.injEq] at heval
          obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
          obtain ⟨r_b, hp_b, h_vv_r, hv_ra, hv_rb⟩ :=
            applyPrim_bisimβ name args_a args_b T_a.heap T_b.heap h_lvv hv_argsa hv_argsb v_a' hp_a
          exact ⟨r_b, T_b, by simp only [applyDirect, hp_b], h_vv_r, h_tower,
                 HeapEvolutionβ.refl _ _, hv_ra, hv_rb⟩
  | builtinBaseApply =>
      have h_opb : op_b = .builtinBaseApply := by
        cases op_b with
        | builtinBaseApply => rfl
        | num _ => simp [ValVisβ_aux] at h_vv1
        | bool _ => simp [ValVisβ_aux] at h_vv1
        | nilV => simp [ValVisβ_aux] at h_vv1
        | sym _ => simp [ValVisβ_aux] at h_vv1
        | cons _ _ => simp [ValVisβ_aux] at h_vv1
        | closure _ _ _ => simp [ValVisβ_aux] at h_vv1
        | prim _ => simp [ValVisβ_aux] at h_vv1
      subst h_opb
      unfold applyDirect at heval
      match args_a, args_b, h_lvv, hv_argsa, hv_argsb with
      | [], _, _, _, _ => simp at heval
      | _ :: [], _, _, _, _ => simp at heval
      | _ :: _ :: _ :: _, _, _, _, _ => simp at heval
      | [_aO_a, _ol_a], [], h_lvv', _, _ => exact h_lvv'.elim
      | [_aO_a, _ol_a], [_], h_lvv', _, _ => exact h_lvv'.2.elim
      | [_aO_a, _ol_a], _ :: _ :: _ :: _, h_lvv', _, _ => exact h_lvv'.2.2.elim
      | [actualOp_a, operandsList_a], [actualOp_b, operandsList_b],
          ⟨h_vv_actual, h_vv_olist, _⟩, ⟨hv_actual_a, hv_olist_a, _⟩,
          ⟨hv_actual_b, hv_olist_b, _⟩ =>
          simp only at heval
          cases hl_a : valToList operandsList_a with
          | none => rw [hl_a] at heval; simp at heval
          | some operands_a =>
              rw [hl_a] at heval
              simp only at heval
              obtain ⟨operands_b, hl_b, h_lvv_ops, hv_ops_a, hv_ops_b⟩ :=
                valToList_bisimβ operands_a operandsList_a operandsList_b
                  T_a.heap T_b.heap hl_a h_vv_olist hv_olist_a hv_olist_b
              obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_tower', h_he', hv_ra, hv_rb⟩ :=
                ih_ad ptable level actualOp_a actualOp_b operands_a operands_b
                  T_a T_b r_a T_a' hresp_pt h_tower h_vv_actual h_lvv_ops
                  hv_actual_a hv_actual_b hv_ops_a hv_ops_b heval
              exact ⟨r_b, T_b', by simp only [applyDirect, hl_b, h_eval_b], h_vv_r,
                     h_tower', h_he', hv_ra, hv_rb⟩
  | closure ps body cenv =>
      obtain ⟨body', cenv_b, rfl⟩ := ValVisβ_closure_inv h_vv_op
      obtain ⟨_, hβ_body, h_env_cenv⟩ := closure_ValVisβ_imp h_vv_op
      simp only [applyDirect] at heval
      by_cases hlen : ps.length = args_a.length
      · have hlen_b : ps.length = args_b.length := by rw [hlen]; exact ListValVisβ.length_eq h_lvv
        have hne_a : (ps.length != args_a.length) = false := by simp [hlen]
        rw [hne_a] at heval
        simp only [Bool.false_eq_true, ↓reduceIte] at heval
        -- bind the arguments (§6g): EnvVisβ call envs + the heap-extension witnesses
        obtain ⟨hh_a', hh_b', hev_a', hev_b', h_env_alloc, ⟨ext_a, hex_a⟩, ⟨ext_b, hex_b⟩⟩ :=
          EnvVisβ_allocStep_chain args_a args_b ps cenv cenv_b T_a.heap T_b.heap
            hlen.symm hlen_b.symm h_lvv hv_argsa hv_argsb h_tower.hv_a h_tower.hv_b
            hv_opa hv_opb h_env_cenv
        -- lift the level fields across the argument allocation
        obtain ⟨hlva', hlvb', hlvisβ'⟩ :=
          level_fields_extend ext_a ext_b h_tower.hv_a h_tower.hv_b
            h_tower.valid_a h_tower.valid_b h_tower.visβ
        -- `TowerInvβ` at the alloc'd states (levels/policies unchanged; heaps += ext)
        have h_tower_alloc : TowerInvβ
            { T_a with heap := (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 }
            { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 } :=
          { hv_a := hh_a', hv_b := hh_b', count := h_tower.count
            valid_a := by rw [hex_a]; exact hlva', valid_b := by rw [hex_b]; exact hlvb'
            visβ := by rw [hex_a, hex_b]; exact hlvisβ'
            pol_eq := h_tower.pol_eq, pol_resp := h_tower.pol_resp }
        -- `WFCtxTβ` for the closure body call, then run it by the level-tracking eval IH
        obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_ctx_body, h_he_body, hv_ra, hv_rb⟩ :=
          ih_eval ptable level body body'
            (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).2
            (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).2
            { T_a with heap := (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 }
            { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 }
            r_a T_a' hβ_body hresp_pt
            (WFCtxTβ.ofTower h_tower_alloc hev_a' hev_b' h_env_alloc) heval
        have h_he_alloc : HeapEvolutionβ T_a T_b
            { T_a with heap := (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 }
            { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 } :=
          HeapEvolutionβ.from_heapExt h_tower.hv_a h_tower.hv_b ⟨ext_a, hex_a⟩ ⟨ext_b, hex_b⟩
        refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_body.toTower,
                h_he_alloc.trans h_he_body, hv_ra, hv_rb⟩
        simp only [applyDirect]
        have hne_b : (ps.length != args_b.length) = false := by simp [hlen_b]
        rw [hne_b]; simp only [Bool.false_eq_true, ↓reduceIte]; exact h_eval_b
      · have hne : (ps.length != args_a.length) = true := by simp [hlen]
        rw [hne] at heval; simp at heval

/-! ## 7j. The gated `.app` case — `applyVia`'s gate dispatch

`applyVia` materializes `level + 1`, looks up `base-apply` in that level's env,
and dispatches: the standard gate (`base-apply ↦ .builtinBaseApply`, or the
lookups missing) re-runs `applyDirect op args`; a non-standard gate
(`base-apply ↦ closure`) does the cross-level call `applyDirect baseApply
[op, listToVal args]`. Either way it bottoms out in `applyDirect` — so with the
level-tracking `frameβ_applyDirect_evalW` (§7i) + `materialize_MatInvβ` (§7d)
the whole case goes through: both sides materialize consistently, the up-envs
are `EnvVisβ`-related so the `base-apply` cells are `ValVisβ`-related (forcing
the *same* dispatch branch cross-side), and the dispatch is the applyDirect IH.
This is route (b)'s gate threading — the genuine reflective content. A few
cross-side lookup/`listToVal` helpers first. -/

/-- `listToVal` respects `ListValVisβ`. -/
theorem listToVal_visβ : ∀ {xs ys : List Val} {h_a h_b : Heap},
    ListValVisβ xs ys h_a h_b → ValVisβ (listToVal xs) (listToVal ys) h_a h_b
  | [], [], _, _, _ => ValVisβ_refl_closed .nilV rfl _ _
  | _ :: _, _ :: _, _, _, ⟨hh, ht⟩ => by
      intro d; cases d with
      | zero => trivial
      | succ d' => exact ⟨hh d', listToVal_visβ ht d'⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- `listToVal` of a valid list is valid. -/
theorem listToVal_valid : ∀ {xs : List Val} {h : Heap}, ListValValid xs h → ValValid (listToVal xs) h
  | [], _, _ => trivial
  | _ :: _, _, ⟨hx, ht⟩ => ⟨hx, listToVal_valid ht⟩

/-- `ListValVisβ` lifts across `HeapEvolutionβ`. -/
theorem HeapEvolutionβ.listValVisβ_preserve {s_a s_b s_a' s_b' : TowerState}
    (h : HeapEvolutionβ s_a s_b s_a' s_b') : ∀ (xs ys : List Val),
    ListValValid xs s_a.heap → ListValValid ys s_b.heap →
    ListValVisβ xs ys s_a.heap s_b.heap → ListValVisβ xs ys s_a'.heap s_b'.heap
  | [], [], _, _, _ => trivial
  | _ :: _, _ :: _, ⟨hvx, hvxs⟩, ⟨hvy, hvys⟩, ⟨hh, ht⟩ =>
      ⟨h.valVisβ_preserve _ _ hvx hvy hh, h.listValVisβ_preserve _ _ hvxs hvys ht⟩
  | [], _ :: _, _, _, hv => hv.elim
  | _ :: _, [], _, _, hv => hv.elim

/-- Cross-side env lookup: a bound name resolving to a cell on the a-side
    resolves to a `ValVisβ`-related cell on the b-side. -/
theorem EnvVisβ_lookup_some {env_a env_b : Env} {h_a h_b : Heap} {x : String}
    {i_a : Nat} {v_a : Val} (h : EnvVisβ env_a env_b h_a h_b)
    (hla : env_a.lookup x = some i_a) (hpa : h_a[i_a]? = some v_a) :
    ∃ i_b v_b, env_b.lookup x = some i_b ∧ h_b[i_b]? = some v_b ∧ ValVisβ v_a v_b h_a h_b := by
  have h1 := h 1 x
  simp only [hla] at h1
  cases hlb : env_b.lookup x with
  | none => simp [hlb] at h1
  | some i_b =>
      simp only [hlb, hpa] at h1
      cases hpb : h_b[i_b]? with
      | none => simp [hpb] at h1
      | some v_b =>
          refine ⟨i_b, v_b, rfl, hpb, fun d => ?_⟩
          have hd := h d x; simp only [hla, hlb, hpa, hpb] at hd; exact hd

/-- Cross-side env lookup: an unbound name on the a-side is unbound on the b-side. -/
theorem EnvVisβ_lookup_none {env_a env_b : Env} {h_a h_b : Heap} {x : String}
    (h : EnvVisβ env_a env_b h_a h_b) (hla : env_a.lookup x = none) :
    env_b.lookup x = none := by
  have h1 := h 1 x
  simp only [hla] at h1
  cases hlb : env_b.lookup x with
  | none => rfl
  | some i => simp [hlb] at h1

/-- The gated-`applyVia` clause over `TowerInvβ` (same shape as
    `FrameβApplyDirectStmtW`, with `applyVia` in place of `applyDirect`). -/
def FrameβApplyViaStmtW (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (op_a op_b : Val)
    (args_a args_b : List Val) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    TowerInvβ T_a T_b →
    ValVisβ op_a op_b T_a.heap T_b.heap →
    ListValVisβ args_a args_b T_a.heap T_b.heap →
    ValValid op_a T_a.heap → ValValid op_b T_b.heap →
    ListValValid args_a T_a.heap → ListValValid args_b T_b.heap →
    applyVia n ptable level op_a args_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      applyVia n ptable level op_b args_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ TowerInvβ T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap

/-! ### Operational reductions of `applyVia` to `applyDirect`

Each dispatch path of `applyVia` reduces to a concrete `applyDirect` call (or
`none`). Proving these once — the only `Val`-constructor case-bash is in
`applyVia_nonBuiltin` — lets the main proof rewrite both sides uniformly. -/

theorem applyVia_materialize_none (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T : TowerState) (hm : T.materialize (level + 1) = none) :
    applyVia (n + 1) ptable level op args T = none := by simp only [applyVia, hm]

theorem applyVia_envAt_none (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T T' : TowerState)
    (hm : T.materialize (level + 1) = some T') (he : T'.envAt? (level + 1) = none) :
    applyVia (n + 1) ptable level op args T = applyDirect n ptable level op args T' := by
  simp only [applyVia, hm, he]

theorem applyVia_baseApply_none (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T T' : TowerState) (upEnv : Env)
    (hm : T.materialize (level + 1) = some T') (he : T'.envAt? (level + 1) = some upEnv)
    (hba : upEnv.lookup "base-apply" = none) :
    applyVia (n + 1) ptable level op args T = applyDirect n ptable level op args T' := by
  simp only [applyVia, hm, he, hba]

theorem applyVia_cell_none (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T T' : TowerState) (upEnv : Env) (idx : Nat)
    (hm : T.materialize (level + 1) = some T') (he : T'.envAt? (level + 1) = some upEnv)
    (hba : upEnv.lookup "base-apply" = some idx) (hcell : T'.heap[idx]? = none) :
    applyVia (n + 1) ptable level op args T = none := by simp only [applyVia, hm, he, hba, hcell]

theorem applyVia_builtin (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T T' : TowerState) (upEnv : Env) (idx : Nat)
    (hm : T.materialize (level + 1) = some T') (he : T'.envAt? (level + 1) = some upEnv)
    (hba : upEnv.lookup "base-apply" = some idx)
    (hcell : T'.heap[idx]? = some .builtinBaseApply) :
    applyVia (n + 1) ptable level op args T = applyDirect n ptable level op args T' := by
  simp only [applyVia, hm, he, hba, hcell]

theorem applyVia_nonBuiltin (n : Nat) (ptable : PolicyTable) (level : Nat)
    (op : Val) (args : List Val) (T T' : TowerState) (upEnv : Env) (idx : Nat) (baseApply : Val)
    (hm : T.materialize (level + 1) = some T') (he : T'.envAt? (level + 1) = some upEnv)
    (hba : upEnv.lookup "base-apply" = some idx) (hcell : T'.heap[idx]? = some baseApply)
    (hne : baseApply ≠ .builtinBaseApply) :
    applyVia (n + 1) ptable level op args T
      = applyDirect n ptable level baseApply [op, listToVal args] T' := by
  cases baseApply with
  | builtinBaseApply => exact absurd rfl hne
  | num _ => simp only [applyVia, hm, he, hba, hcell]
  | bool _ => simp only [applyVia, hm, he, hba, hcell]
  | nilV => simp only [applyVia, hm, he, hba, hcell]
  | sym _ => simp only [applyVia, hm, he, hba, hcell]
  | cons _ _ => simp only [applyVia, hm, he, hba, hcell]
  | closure _ _ _ => simp only [applyVia, hm, he, hba, hcell]
  | prim _ => simp only [applyVia, hm, he, hba, hcell]

/-- `ValVisβ` two-sided agreement on being `.builtinBaseApply` (forces the same
    gate-dispatch branch cross-side). -/
theorem ValVisβ_builtinBaseApply_iff {a b : Val} {h_a h_b : Heap}
    (h : ValVisβ a b h_a h_b) : a = .builtinBaseApply ↔ b = .builtinBaseApply := by
  have h1 := h 1; cases a <;> cases b <;> simp_all [ValVisβ_aux]

/-- Cross-side: a level absent on the a-side is absent on the b-side. -/
theorem envAt?_none_cross (T_a T_b : TowerState) (n : Nat)
    (h_count : T_a.levels.length = T_b.levels.length) (h : T_a.envAt? n = none) :
    T_b.envAt? n = none := by
  unfold TowerState.envAt? TowerState.levelAt? at h ⊢
  rw [Option.map_eq_none_iff, List.getElem?_eq_none_iff] at h ⊢
  omega

/-- **The gated `.app` case, proved.** Taking the level-tracking `applyDirect`
    IH (`FrameβApplyDirectStmtW n`), `applyVia (n+1)` is discharged: both sides
    materialize `level+1` consistently (`materialize_MatInvβ` + the heap/env-
    agnostic `materialize_cross_side_some_iff`), the up-envs are `EnvVisβ`-related
    so the `base-apply` cells are `ValVisβ`-related and the *same* dispatch branch
    is taken cross-side, and the dispatch (standard `applyDirect op args` or the
    non-standard cross-level `applyDirect baseApply [op, listToVal args]`) is the
    `applyDirect` IH. The reflective gate threading of route (b). -/
theorem frameβ_applyVia_eval (n : Nat) (ih_ad : FrameβApplyDirectStmtW n) :
    FrameβApplyViaStmtW (n + 1) := by
  intro ptable level op_a op_b args_a args_b T_a T_b r_a T_a'
        hresp_pt h_tower h_vv_op h_lvv hv_opa hv_opb hv_argsa hv_argsb heval
  cases hm_a : T_a.materialize (level + 1) with
  | none => rw [applyVia_materialize_none n ptable level op_a args_a T_a hm_a] at heval; simp at heval
  | some T_a_mat =>
      -- b-side materializes (cross-side some-iff is heap/env-agnostic)
      have hm_b_some : (T_b.materialize (level + 1)).isSome := by
        cases h_some : T_b.materialize (level + 1) with
        | none => rw [(T_a.materialize_cross_side_some_iff T_b _).mpr h_some] at hm_a; cases hm_a
        | some _ => simp
      obtain ⟨T_b_mat, hm_b⟩ := Option.isSome_iff_exists.mp hm_b_some
      -- materialized tower invariant + heap evolution + op/args lifted to `T_mat`
      obtain ⟨hhm_a, hhm_b, hcount_m, hvalid_a_m, hvalid_b_m, hvisβ_m⟩ :=
        materialize_MatInvβ ⟨h_tower.hv_a, h_tower.hv_b, h_tower.count, h_tower.valid_a,
          h_tower.valid_b, h_tower.visβ⟩ hm_a hm_b
      have hpoleq_m := materialize_policiesEqβ h_tower.count h_tower.pol_eq hm_a hm_b
      have hpolresp_m := materialize_policies_resp_preserves T_a T_a_mat (level + 1)
        PolicyRespectsBisimT hm_a h_tower.pol_resp rejectAllPolicy_respects_bisimT
      have h_tower_mat : TowerInvβ T_a_mat T_b_mat :=
        ⟨hhm_a, hhm_b, hcount_m, hvalid_a_m, hvalid_b_m, hvisβ_m, hpoleq_m, hpolresp_m⟩
      have h_he_mat : HeapEvolutionβ T_a T_b T_a_mat T_b_mat :=
        HeapEvolutionβ.from_heapExt h_tower.hv_a h_tower.hv_b
          (T_a.materialize_heap_extends T_a_mat (level + 1) hm_a)
          (T_b.materialize_heap_extends T_b_mat (level + 1) hm_b)
      have h_vv_op_m := h_he_mat.valVisβ_preserve op_a op_b hv_opa hv_opb h_vv_op
      have h_lvv_m := h_he_mat.listValVisβ_preserve args_a args_b hv_argsa hv_argsb h_lvv
      have hv_opa_m := ValValid.length_mono op_a hv_opa h_he_mat.len_a
      have hv_opb_m := ValValid.length_mono op_b hv_opb h_he_mat.len_b
      have hv_argsa_m := ListValValid.length_mono hv_argsa h_he_mat.len_a
      have hv_argsb_m := ListValValid.length_mono hv_argsb h_he_mat.len_b
      cases he_a : T_a_mat.envAt? (level + 1) with
      | none =>
          -- no level-(level+1) env → dispatch `applyDirect op args` (both sides)
          rw [applyVia_envAt_none n ptable level op_a args_a T_a T_a_mat hm_a he_a] at heval
          have he_b : T_b_mat.envAt? (level + 1) = none :=
            envAt?_none_cross T_a_mat T_b_mat (level + 1) hcount_m he_a
          obtain ⟨r_b, T_b', h_ad_b, h_vv_r, h_tower', h_he_ad, hv_ra, hv_rb⟩ :=
            ih_ad ptable level op_a op_b args_a args_b T_a_mat T_b_mat r_a T_a' hresp_pt
              h_tower_mat h_vv_op_m h_lvv_m hv_opa_m hv_opb_m hv_argsa_m hv_argsb_m heval
          refine ⟨r_b, T_b', ?_, h_vv_r, h_tower', h_he_mat.trans h_he_ad, hv_ra, hv_rb⟩
          rw [applyVia_envAt_none n ptable level op_b args_b T_b T_b_mat hm_b he_b]; exact h_ad_b
      | some upEnv_a =>
          obtain ⟨upEnv_b, he_b⟩ := envAt?_some_cross T_a_mat T_b_mat (level + 1) upEnv_a hcount_m he_a
          have h_env_up : EnvVisβ upEnv_a upEnv_b T_a_mat.heap T_b_mat.heap :=
            hvisβ_m (level + 1) upEnv_a upEnv_b he_a he_b
          cases hba_a : upEnv_a.lookup "base-apply" with
          | none =>
              -- no `base-apply` binding → dispatch `applyDirect op args`
              rw [applyVia_baseApply_none n ptable level op_a args_a T_a T_a_mat upEnv_a
                hm_a he_a hba_a] at heval
              have hba_b : upEnv_b.lookup "base-apply" = none := EnvVisβ_lookup_none h_env_up hba_a
              obtain ⟨r_b, T_b', h_ad_b, h_vv_r, h_tower', h_he_ad, hv_ra, hv_rb⟩ :=
                ih_ad ptable level op_a op_b args_a args_b T_a_mat T_b_mat r_a T_a' hresp_pt
                  h_tower_mat h_vv_op_m h_lvv_m hv_opa_m hv_opb_m hv_argsa_m hv_argsb_m heval
              refine ⟨r_b, T_b', ?_, h_vv_r, h_tower', h_he_mat.trans h_he_ad, hv_ra, hv_rb⟩
              rw [applyVia_baseApply_none n ptable level op_b args_b T_b T_b_mat upEnv_b hm_b he_b hba_b]
              exact h_ad_b
          | some idx_a =>
              cases hcell_a : T_a_mat.heap[idx_a]? with
              | none =>
                  rw [applyVia_cell_none n ptable level op_a args_a T_a T_a_mat upEnv_a idx_a
                    hm_a he_a hba_a hcell_a] at heval; simp at heval
              | some baseApply_a =>
                  obtain ⟨idx_b, baseApply_b, hba_b, hcell_b, h_vv_cell⟩ :=
                    EnvVisβ_lookup_some h_env_up hba_a hcell_a
                  by_cases hbuiltin : baseApply_a = .builtinBaseApply
                  · -- standard gate: `base-apply ↦ builtinBaseApply` → `applyDirect op args`
                    subst hbuiltin
                    rw [applyVia_builtin n ptable level op_a args_a T_a T_a_mat upEnv_a idx_a
                      hm_a he_a hba_a hcell_a] at heval
                    have hbb_b : baseApply_b = .builtinBaseApply :=
                      (ValVisβ_builtinBaseApply_iff h_vv_cell).mp rfl
                    rw [hbb_b] at hcell_b
                    obtain ⟨r_b, T_b', h_ad_b, h_vv_r, h_tower', h_he_ad, hv_ra, hv_rb⟩ :=
                      ih_ad ptable level op_a op_b args_a args_b T_a_mat T_b_mat r_a T_a' hresp_pt
                        h_tower_mat h_vv_op_m h_lvv_m hv_opa_m hv_opb_m hv_argsa_m hv_argsb_m heval
                    refine ⟨r_b, T_b', ?_, h_vv_r, h_tower', h_he_mat.trans h_he_ad, hv_ra, hv_rb⟩
                    rw [applyVia_builtin n ptable level op_b args_b T_b T_b_mat upEnv_b idx_b
                      hm_b he_b hba_b hcell_b]
                    exact h_ad_b
                  · -- non-standard gate: cross-level `applyDirect baseApply [op, listToVal args]`
                    rw [applyVia_nonBuiltin n ptable level op_a args_a T_a T_a_mat upEnv_a idx_a
                      baseApply_a hm_a he_a hba_a hcell_a hbuiltin] at heval
                    have hbuiltin_b : baseApply_b ≠ .builtinBaseApply :=
                      fun h => hbuiltin ((ValVisβ_builtinBaseApply_iff h_vv_cell).mpr h)
                    have h_lvv_cross : ListValVisβ [op_a, listToVal args_a] [op_b, listToVal args_b]
                        T_a_mat.heap T_b_mat.heap := ⟨h_vv_op_m, listToVal_visβ h_lvv_m, trivial⟩
                    obtain ⟨r_b, T_b', h_ad_b, h_vv_r, h_tower', h_he_ad, hv_ra, hv_rb⟩ :=
                      ih_ad ptable level baseApply_a baseApply_b
                        [op_a, listToVal args_a] [op_b, listToVal args_b] T_a_mat T_b_mat r_a T_a'
                        hresp_pt h_tower_mat h_vv_cell h_lvv_cross
                        (hhm_a idx_a baseApply_a hcell_a) (hhm_b idx_b baseApply_b hcell_b)
                        ⟨hv_opa_m, listToVal_valid hv_argsa_m, trivial⟩
                        ⟨hv_opb_m, listToVal_valid hv_argsb_m, trivial⟩ heval
                    refine ⟨r_b, T_b', ?_, h_vv_r, h_tower', h_he_mat.trans h_he_ad, hv_ra, hv_rb⟩
                    rw [applyVia_nonBuiltin n ptable level op_b args_b T_b T_b_mat upEnv_b idx_b
                      baseApply_b hm_b he_b hba_b hcell_b hbuiltin_b]
                    exact h_ad_b

/-! ## 7k. The `evalList` clause over `WFCtxTβ`

The argument-list traversal re-threaded onto the reflective wrapper — a faithful
β-port of `LamBeta`'s `frameβ_evalList_eval` (over `WFβ`), the two-IH list clause
that eval's `.app`/`.primApp` run before applying. The ambient env is fixed, so
the output `WFCtxTβ` is the tail's output; the head's value/validity are lifted
across the tail's `HeapEvolutionβ`. -/

def FrameβEvalListStmtW (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (exps_a exps_b : List Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (rs_a : List Val) (T_a' : TowerState),
    BetaRelList exps_a exps_b →
    PolicyTableRespectsBisimT ptable →
    WFCtxTβ env_a env_b T_a T_b level →
    evalList n ptable level exps_a env_a T_a = some (rs_a, T_a') →
    ∃ rs_b T_b',
      evalList n ptable level exps_b env_b T_b = some (rs_b, T_b') ∧
      ListValVisβ rs_a rs_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ListValValid rs_a T_a'.heap ∧ ListValValid rs_b T_b'.heap

/-- The `evalList` inductive step over `WFCtxTβ` (the two-IH list traversal). -/
theorem frameβ_evalList_evalW (n : Nat)
    (ih_eval : FrameβEvalStmtW n) (ih_list : FrameβEvalListStmtW n) :
    FrameβEvalListStmtW (n + 1) := by
  intro ptable level exps_a exps_b env_a env_b T_a T_b rs_a T_a' hβ hresp_pt h_ctx heval
  cases hβ with
  | nil =>
      simp only [evalList, Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
      exact ⟨[], T_b, by simp [evalList], trivial, h_ctx, HeapEvolutionβ.refl _ _, trivial, trivial⟩
  | cons hβ_e hβ_rest =>
      rename_i e e' rest rest'
      simp only [evalList] at heval
      cases he : eval n ptable level e env_a T_a with
      | none => rw [he] at heval; simp at heval
      | some pr =>
          obtain ⟨v_a, T_a_inner⟩ := pr
          rw [he] at heval; simp only at heval
          cases hrest : evalList n ptable level rest env_a T_a_inner with
          | none => rw [hrest] at heval; simp at heval
          | some pr2 =>
              obtain ⟨vs_a, T_a_inner2⟩ := pr2
              rw [hrest] at heval; simp only [Option.some.injEq, Prod.mk.injEq] at heval
              obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
              obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner, hv_va, hv_vb⟩ :=
                ih_eval ptable level e e' env_a env_b T_a T_b v_a T_a_inner hβ_e hresp_pt h_ctx he
              obtain ⟨vs_b, T_b_inner2, h_eval_rest_b, h_lvv, h_ctx_inner2, h_he_inner2,
                      hv_vsa, hv_vsb⟩ :=
                ih_list ptable level rest rest' env_a env_b T_a_inner T_b_inner vs_a T_a_inner2
                  hβ_rest hresp_pt h_ctx_inner hrest
              have h_vv_v' : ValVisβ v_a v_b T_a_inner2.heap T_b_inner2.heap :=
                h_he_inner2.valVisβ_preserve v_a v_b hv_va hv_vb h_vv_v
              have hv_va' : ValValid v_a T_a_inner2.heap := ValValid.length_mono v_a hv_va h_he_inner2.len_a
              have hv_vb' : ValValid v_b T_b_inner2.heap := ValValid.length_mono v_b hv_vb h_he_inner2.len_b
              refine ⟨v_b :: vs_b, T_b_inner2, ?_, ⟨h_vv_v', h_lvv⟩, h_ctx_inner2,
                      h_he_inner.trans h_he_inner2, ⟨hv_va', hv_vsa⟩, ⟨hv_vb', hv_vsb⟩⟩
              simp [evalList, h_eval_e_b, h_eval_rest_b]

/-! ## 7l. The minor reflective-adjacent eval cases: `.quote`, `.installPolicy`

`.quote` returns a `closedValB` literal (state unchanged); `.installPolicy idx`
swaps the level-`level` policy for `ptable[idx]?` (`setPolicyAt`, heap/envs
unchanged). Both β-invert trivially (no `Ctx` slot, so β never fires from or
under them). With these the only eval constructors left are the two deep cruxes
— eval's `.app` (root-contraction / β-firing) and `.set`. -/

/-- β never fires from a quote. -/
theorem BetaRel.quote_eq {v : Val} {b : Expr} (h : BetaRel (.quote v) b) : b = .quote v := by
  induction h with
  | refl => rfl
  | tail _ step ih => subst ih; obtain ⟨C, _, _, _, hC, _⟩ := step; cases C <;> simp [Ctx.plug] at hC

/-- β never fires from an `installPolicy`. -/
theorem BetaRel.installPolicy_eq {idx : Nat} {b : Expr} (h : BetaRel (.installPolicy idx) b) :
    b = .installPolicy idx := by
  induction h with
  | refl => rfl
  | tail _ step ih => subst ih; obtain ⟨C, _, _, _, hC, _⟩ := step; cases C <;> simp [Ctx.plug] at hC

/-- `.quote` on `FrameβEvalStmtW` (state unchanged; closed literal self-relates). -/
theorem frameβ_quote_caseW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (v : Val) (exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (hβ : BetaRel (.quote v) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.quote v) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  have hb := hβ.quote_eq; subst hb
  simp only [eval] at heval
  split at heval
  · rename_i hclosed
    simp only [Option.some.injEq, Prod.mk.injEq] at heval
    obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
    refine ⟨v, T_b, ?_, ValVisβ_refl_closed v hclosed _ _, h_ctx, HeapEvolutionβ.refl _ _,
            closedVal_ValValid v hclosed _, closedVal_ValValid v hclosed _⟩
    simp only [eval, hclosed, ↓reduceIte]
  · simp at heval

/-- `.installPolicy` on `FrameβEvalStmtW`: swaps the level-`level` policy for
    `ptable[idx]?` (heap/envs unchanged). The new policy respects bisim
    (`PolicyTableRespectsBisimT`), and the `setPolicyAt` lemmas carry every
    `WFCtxTβ` field through (`setPolicyAt` touches only the policy at `level`). -/
theorem frameβ_installPolicy_caseW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (idx : Nat) (exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.installPolicy idx) exp_b) (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.installPolicy idx) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  have hb := hβ.installPolicy_eq; subst hb
  simp only [eval] at heval
  cases hpt : ptable[idx]? with
  | none =>
      rw [hpt] at heval
      simp only [Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
      exact ⟨.bool false, T_b, by simp only [eval, hpt], (fun d => by cases d <;> simp [ValVisβ_aux]),
             h_ctx, HeapEvolutionβ.refl _ _, trivial, trivial⟩
  | some np =>
      rw [hpt] at heval
      simp only [Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
      have hresp_np : PolicyRespectsBisimT np := hresp_pt idx np hpt
      refine ⟨.bool true, T_b.setPolicyAt level np, by simp only [eval, hpt],
              (fun d => by cases d <;> simp [ValVisβ_aux]), ?_, ?_, trivial, trivial⟩
      · exact
        { policy_eq_at := by
            rw [TowerState.setPolicyAt_policyAt?_self, TowerState.setPolicyAt_policyAt?_self,
                h_ctx.policy_eq_at]
          hv_a := by rw [TowerState.setPolicyAt_heap]; exact h_ctx.hv_a
          hv_b := by rw [TowerState.setPolicyAt_heap]; exact h_ctx.hv_b
          ev_a := by rw [TowerState.setPolicyAt_heap]; exact h_ctx.ev_a
          ev_b := by rw [TowerState.setPolicyAt_heap]; exact h_ctx.ev_b
          policy_resp := by
            intro p hp
            rw [TowerState.setPolicyAt_policyAt?_self, Option.map_eq_some_iff] at hp
            obtain ⟨_, _, hpq⟩ := hp; rw [← hpq]; exact hresp_np
          env_visβ := by
            rw [TowerState.setPolicyAt_heap, TowerState.setPolicyAt_heap]; exact h_ctx.env_visβ
          level_envs_valid_a := by
            intro m env hen
            rw [TowerState.setPolicyAt_envAt?] at hen; rw [TowerState.setPolicyAt_heap]
            exact h_ctx.level_envs_valid_a m env hen
          level_envs_valid_b := by
            intro m env hen
            rw [TowerState.setPolicyAt_envAt?] at hen; rw [TowerState.setPolicyAt_heap]
            exact h_ctx.level_envs_valid_b m env hen
          level_count_eq := by
            rw [TowerState.setPolicyAt_levels_length, TowerState.setPolicyAt_levels_length]
            exact h_ctx.level_count_eq
          policies_eq := by
            intro m; by_cases hm : level = m
            · subst hm
              rw [TowerState.setPolicyAt_policyAt?_self, TowerState.setPolicyAt_policyAt?_self,
                  h_ctx.policy_eq_at]
            · rw [TowerState.setPolicyAt_policyAt?_other _ _ _ _ hm,
                  TowerState.setPolicyAt_policyAt?_other _ _ _ _ hm]
              exact h_ctx.policies_eq m
          policies_resp_all := by
            intro m p hp; by_cases hm : level = m
            · subst hm
              rw [TowerState.setPolicyAt_policyAt?_self, Option.map_eq_some_iff] at hp
              obtain ⟨_, _, hpq⟩ := hp; rw [← hpq]; exact hresp_np
            · rw [TowerState.setPolicyAt_policyAt?_other _ _ _ _ hm] at hp
              exact h_ctx.policies_resp_all m p hp
          level_envs_visβ := by
            intro m ea eb hena henb
            rw [TowerState.setPolicyAt_envAt?] at hena henb
            rw [TowerState.setPolicyAt_heap, TowerState.setPolicyAt_heap]
            exact h_ctx.level_envs_visβ m ea eb hena henb }
      · exact HeapEvolutionβ.from_heapExt h_ctx.hv_a h_ctx.hv_b
          ⟨[], by rw [TowerState.setPolicyAt_heap]; simp⟩
          ⟨[], by rw [TowerState.setPolicyAt_heap]; simp⟩

/-! ## 7m. eval's `.app` — the structural branch (no root contraction)

The first of the two remaining eval cases (`DUMP_LAM.md` §3 step 3a). `.app`'s
`BetaRel` inversion (`BetaRel.app_inv`, `LamBeta` §4d) is a *disjunction*: a
**structural** branch — `exp_b = .app args'` with `BetaRelList args args'`, no
redex contracted at the root — and the **root-contraction** branch (where β
fires). This section discharges the structural branch: a faithful β-port of
`frame_tower`'s `.app` case (`Frame.lean:1152`), composing the three
already-proven reflective clauses — the eval IH on the head, the `evalList`
clause (§7k) on the argument tail, and the gated `applyVia` clause (§7j) on the
application — then rebuilding the output `WFCtxTβ` from the `applyVia` output
`TowerInvβ` (`WFCtxTβ.ofTower`) with the ambient-env fields lifted across the
composed `HeapEvolutionβ`.

It is **unconditional** (no `BuiltinReady` premise): both sides run an `.app`, so
`applyVia`'s cross-side gate dispatch (`frameβ_applyVia_eval`) handles the gate
uniformly — the `base-apply` cells are `ValVisβ`-related, forcing the same branch.
The conditional-β premise is needed only by the root-contraction branch, where the
a-side runs an application and the b-side a `.letE` (`DUMP_LAM.md` §0 Obstruction
B). That branch — the genuine research crux — is the single remaining eval case
after this (with `.set`). -/

/-- **eval's `.app`, structural branch.** Given `BetaRelList args args'` (the
    `app_inv` inl case), `.app args` (a-side) and `.app args'` (b-side) simulate:
    eval the head by the eval IH, the argument tail by the `evalList` clause, and
    apply by the `applyVia` clause. Takes the fuel-`n` eval / evalList / applyVia
    clauses as IHs, exactly as `frame_tower`'s `.app` case takes `ih_eval` /
    `ih_evalList` / `ih_applyVia`. -/
theorem frameβ_app_structural_evalW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (args args' : List Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih_eval : FrameβEvalStmtW n) (ih_list : FrameβEvalListStmtW n)
    (ih_via : FrameβApplyViaStmtW n)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ_args : BetaRelList args args')
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (heval : eval (n + 1) ptable level (.app args) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level (.app args') env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  cases hβ_args with
  | nil => simp only [eval] at heval; exact absurd heval (by simp)
  | cons hβ_f hβ_rest =>
      rename_i f f' rest rest'
      simp only [eval] at heval
      cases hf : eval n ptable level f env_a T_a with
      | none => rw [hf] at heval; simp at heval
      | some pr =>
          obtain ⟨fv_a, T_a_inner⟩ := pr
          rw [hf] at heval; simp only at heval
          obtain ⟨fv_b, T_b_inner, h_eval_f_b, h_vv_f, h_ctx1, h_he1, hv_fva, hv_fvb⟩ :=
            ih_eval ptable level f f' env_a env_b T_a T_b fv_a T_a_inner hβ_f hresp_pt h_ctx hf
          cases ha : evalList n ptable level rest env_a T_a_inner with
          | none => rw [ha] at heval; simp at heval
          | some pr2 =>
              obtain ⟨avs_a, T_a_inner2⟩ := pr2
              rw [ha] at heval; simp only at heval
              obtain ⟨avs_b, T_b_inner2, h_eval_args_b, h_lvv, h_ctx2, h_he2, hv_avsa, hv_avsb⟩ :=
                ih_list ptable level rest rest' env_a env_b T_a_inner T_b_inner avs_a T_a_inner2
                  hβ_rest hresp_pt h_ctx1 ha
              -- lift the head value (ValVisβ + ValValid) across the args evolution
              have h_vv_f' : ValVisβ fv_a fv_b T_a_inner2.heap T_b_inner2.heap :=
                h_he2.valVisβ_preserve fv_a fv_b hv_fva hv_fvb h_vv_f
              have hv_fva2 : ValValid fv_a T_a_inner2.heap :=
                ValValid.length_mono fv_a hv_fva h_he2.len_a
              have hv_fvb2 : ValValid fv_b T_b_inner2.heap :=
                ValValid.length_mono fv_b hv_fvb h_he2.len_b
              -- apply via the gated `applyVia` clause (§7j)
              obtain ⟨r_b, T_b', h_eval_av_b, h_vv, h_tower3, h_he3, hv_ra, hv_rb⟩ :=
                ih_via ptable level fv_a fv_b avs_a avs_b T_a_inner2 T_b_inner2 r_a T_a'
                  hresp_pt h_ctx2.toTower h_vv_f' h_lvv hv_fva2 hv_fvb2 hv_avsa hv_avsb heval
              have h_he_chain : HeapEvolutionβ T_a T_b T_a' T_b' :=
                h_he1.trans (h_he2.trans h_he3)
              refine ⟨r_b, T_b', ?_, h_vv, ?_, h_he_chain, hv_ra, hv_rb⟩
              · simp only [eval, h_eval_f_b, h_eval_args_b]; exact h_eval_av_b
              · exact WFCtxTβ.ofTower h_tower3
                  (EnvValid.length_mono h_ctx.ev_a h_he_chain.len_a)
                  (EnvValid.length_mono h_ctx.ev_b h_he_chain.len_b)
                  (h_he_chain.envVisβ_preserve env_a env_b h_ctx.ev_a h_ctx.ev_b h_ctx.env_visβ)

/-! ### 7m (cont.). The root-contraction branch, modulo the b-side gate bridge

The `app_inv` `inr` case — **where β fires**. `BetaRel.app_to_redex_inv` (`LamBeta`
§4d) exposes the a-side redex shape `args = [f, a]` (`f` `BetaRel`-reaching the
lambda, `a` the operand); `BetaRel.letE_inv` exposes the *reduced* contractum
`exp_b = .letE x v' body'`. The key move avoids any diagonal/reflexivity: lift the
intermediate redex to the **reduced** one `(λx. body') v'` (so `f ↝ λx.body'` by
`BetaRel.congr` under the binder, `a ↝ v'`), then the **already-proven structural
branch** (`frameβ_app_structural_evalW`) maps the a-side `.app args` onto the
*b-side reduced redex* `.app [λx.body', v']` — delivering `ValVisβ`, `WFCtxTβ`,
`HeapEvolutionβ`, and validity for `(r_b, T_b')` outright. What is left is purely
operational and *on the b-side only*: the reduced redex `.app [λx.body', v']` and
its contractum `.letE x v' body'` (= `exp_b`) must produce the **same** outcome at
`(env_b, T_b)`.

That last step is exactly `DUMP_LAM.md` §0 Obstruction B: redex≡contractum holds
only under the **standard gate** (`applyVia` falls through to `applyDirect`); a
non-standard gate or top-of-tower separates them. So it is the operational content
of the conditional `BuiltinReady` premise — provided here as an explicit hypothesis
`h_gate_b` (a `RedexContractumAgree`-style predicate on the b-side state), which
the eventual conditional fundamental lemma discharges from `BuiltinReady` via the
proven base β `beta_letE_pure_EvalEquivAt` (`ContextualBetaPure.lean:214`). The
route is thus fully type-checked end to end; only `h_gate_b`'s discharge (the
premise threading) remains for the mutual assembly. -/

/-- **eval's `.app`, root-contraction branch, modulo the b-side gate bridge.** The
    `app_inv` `inr` case, reduced to a single explicit operational obligation
    `h_gate_b`: on the b-side, every redex's outcome is matched by its contractum's.
    Everything else — exposing the redex (`app_to_redex_inv`), reducing the
    contractum (`letE_inv`), lifting to the reduced redex (`BetaRel.congr`), and the
    cross-side simulation (`frameβ_app_structural_evalW`) — is discharged. `h_gate_b`
    is the operational form of the standard-gate `BuiltinReady` condition (`DUMP_LAM`
    §0 Obstruction B); it is `beta_letE_pure_EvalEquivAt` instantiated at `(env_b,
    T_b)` once the premise is threaded into the statement. -/
theorem frameβ_app_root_evalW_cond (n : Nat) (ptable : PolicyTable) (level : Nat)
    (args : List Expr) (x : String) (body v exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (ih_eval : FrameβEvalStmtW n) (ih_list : FrameβEvalListStmtW n)
    (ih_via : FrameβApplyViaStmtW n)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (h1 : BetaRel (.app args) (.app [.lam [x] body, v]))
    (h2 : BetaRel (.letE x v body) exp_b)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (h_gate_b : ∀ (y : String) (B V : Expr) (rr : Val) (TT : TowerState),
        eval (n + 1) ptable level (.app [.lam [y] B, V]) env_b T_b = some (rr, TT) →
        eval (n + 1) ptable level (.letE y V B) env_b T_b = some (rr, TT))
    (heval : eval (n + 1) ptable level (.app args) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  -- expose the a-side redex shape and the reduced b-side contractum
  obtain ⟨f, a, rfl, hf, ha⟩ := h1.app_to_redex_inv
  obtain ⟨v', body', rfl, hv', hbody'⟩ := h2.letE_inv
  -- lift to the *reduced* redex `(λx. body') v'` (β-congruence under the binder)
  have hlam_cong : BetaRel (.lam [x] body) (.lam [x] body') :=
    BetaRel.congr hbody' (.lam [x] .hole)
  have hbrl : BetaRelList [f, a] [.lam [x] body', v'] :=
    .cons (hf.trans hlam_cong) (.cons (ha.trans hv') .nil)
  -- the already-proven structural branch maps a-side `.app args` to the b-side redex
  obtain ⟨r_b, T_b', h_redex_b, h_vv, h_ctx', h_he, hv_ra, hv_rb⟩ :=
    frameβ_app_structural_evalW n ptable level [f, a] [.lam [x] body', v']
      env_a env_b T_a T_b r_a T_a' ih_eval ih_list ih_via hresp_pt hbrl h_ctx heval
  -- the b-side gate bridge turns the redex outcome into the contractum (= exp_b) outcome
  exact ⟨r_b, T_b', h_gate_b x body' v' r_b T_b' h_redex_b, h_vv, h_ctx', h_he, hv_ra, hv_rb⟩

/-! ### 7m (cont.). Discharging the b-side gate bridge from the standard gate

`h_gate_b` is the operational content of the standard-gate `BuiltinReady` condition
(`DUMP_LAM.md` §0 Obstruction B). Its **fixed-fuel** core is `redex_to_letE_fixed`:
the ∃-fuel `beta_letE_conv_equiv` (`ContextualBeta.lean`) does not suffice — the
reflective fundamental lemma's conclusion fixes the b-side output fuel — so the
redex→contractum bridge is re-derived at a *fixed* fuel. Both sides reduce to body
evaluation in the **same** extended env/heap (`eval_beta_builtin` for the redex,
`eval_letE` for the contractum), differing only in fuel, reconciled by
`eval_fuel_mono`. The conditions are exactly the gate facts at the *post-operand*
state (depth margin, level+1 materialized, builtin `base-apply`) — which the
eventual conditional fundamental lemma supplies from a `BuiltinReady` premise +
operand purity. -/

/-- **Fixed-fuel redex→contractum bridge.** At fuel `n+3`, given the operand `V`
    evaluates (at `n+1`) to `(v_val, T')` with the standard gate live at `T'`, the
    β-redex `(λx.B) V` and its contractum `let x=V in B` reach the same outcome.
    The fixed-fuel companion to `beta_letE_conv_equiv` (which is ∃-fuel). This is
    the operational core that discharges `frameβ_app_root_evalW_cond`'s `h_gate_b`. -/
theorem redex_to_letE_fixed (n : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (B V : Expr) (env : Env) (T : TowerState)
    (h_depth : level + 1 < Tower.maxDepth)
    (v_val : Val) (T' : TowerState)
    (h_eval_v : eval (n + 1) ptable level V env T = some (v_val, T'))
    (h_mat' : T'.levels.length > level + 1)
    (h_builtin' : builtinBaseApplyAt level T')
    (r : Val) (Tf : TowerState)
    (h_redex : eval (n + 3) ptable level (.app [.lam [x] B, V]) env T = some (r, Tf)) :
    eval (n + 3) ptable level (.letE x V B) env T = some (r, Tf) := by
  have h_eq := eval_beta_builtin n ptable level x B V env T h_depth v_val T' h_eval_v h_mat' h_builtin'
  rw [h_eq] at h_redex
  rw [eval_letE (n + 2) ptable level x V B env T v_val T' (eval_fuel_mono (by omega) h_eval_v)]
  exact eval_fuel_mono (by omega) h_redex

/-- A converging β-redex `(λx.B) V` needs at least fuel 3 (head step, operand step,
    apply step), so its fuel has the `m + 3` shape `redex_to_letE_fixed` expects. -/
theorem app_lam_redex_min_fuel {k : Nat} {ptable : PolicyTable} {level : Nat}
    {x : String} {B V : Expr} {env : Env} {T : TowerState} {p : Val × TowerState}
    (h : eval k ptable level (.app [.lam [x] B, V]) env T = some p) : 3 ≤ k := by
  match k with
  | 0 => simp [eval] at h
  | 1 => simp [eval] at h
  | 2 => simp [eval, evalList] at h
  | _ + 3 => omega

/-- A converging `applyVia` forces the depth margin `level + 1 < maxDepth`:
    `applyVia` materializes `level + 1` *before* dispatching on the operator, and
    `materialize (level+1)` succeeds iff `level + 1 < maxDepth` (state-independent,
    `TowerState.materialize`). -/
theorem applyVia_converges_depth {k : Nat} {ptable : PolicyTable} {level : Nat}
    {op : Val} {args : List Val} {T : TowerState} {p : Val × TowerState}
    (h : applyVia (k + 1) ptable level op args T = some p) : level + 1 < Tower.maxDepth := by
  cases hm : T.materialize (level + 1) with
  | none => rw [applyVia_materialize_none k ptable level op args T hm] at h; exact absurd h (by simp)
  | some Tm =>
      unfold TowerState.materialize at hm
      split at hm
      · exact absurd hm (by simp)
      · omega

/-- A converging β-redex `(λx.B) V` forces the depth margin `level + 1 < maxDepth`
    — the apply step routes through the reflective `base-apply` gate at `level + 1`
    (Obstruction B: at the top level the redex cannot fire).  Unfolds the redex to
    its `applyVia` (mirroring `gate_redex_to_letE`'s operand extraction) and applies
    `applyVia_converges_depth`. -/
theorem app_lam_redex_depth {k : Nat} {ptable : PolicyTable} {level : Nat}
    {x : String} {B V : Expr} {env : Env} {T : TowerState} {p : Val × TowerState}
    (h : eval k ptable level (.app [.lam [x] B, V]) env T = some p) :
    level + 1 < Tower.maxDepth := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by have := app_lam_redex_min_fuel h; omega⟩
  rw [eval_app_lam_v_step (m + 2) ptable level x B V env T,
      eval_lam (m + 1) ptable level [x] B env T] at h
  simp only at h
  rw [evalList_single m ptable level V env T] at h
  cases h_ev : eval (m + 1) ptable level V env T with
  | none => rw [h_ev] at h; simp at h
  | some pr =>
      obtain ⟨v_val, T'⟩ := pr
      rw [h_ev] at h
      simp only at h
      exact applyVia_converges_depth h

/-- **The standard-gate discharge of the redex→contractum bridge.** Under the
    standard gate live at the *input* state (depth margin, level+1 materialized,
    builtin `base-apply`) and a **pure** operand (so the gate survives the operand's
    evaluation, `eval_pure_extends` + `builtinBaseApplyAt_extends`), the β-redex and
    its `.letE` contractum reach the same outcome — at fixed fuel. The operand's
    convergence is *extracted* from the converging redex (`eval_app_lam_v_step` /
    `evalList_single`), so this needs no separate operand hypothesis. This is the
    operational content of `frameβ_app_root_evalW_cond`'s `h_gate_b` under the
    recognized `BuiltinReady` + pure-operand conditions (`DUMP_LAM` §0 Obstruction B,
    matching `contextual_beta_pure`'s side conditions). -/
theorem gate_redex_to_letE (m : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (B V : Expr) (env : Env) (T : TowerState)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat0 : T.levels.length > level + 1)
    (h_builtin0 : builtinBaseApplyAt level T)
    (h_pure : Pure V = true) (h_heap : PureHeap T.heap)
    (r : Val) (Tf : TowerState)
    (h_redex : eval (m + 3) ptable level (.app [.lam [x] B, V]) env T = some (r, Tf)) :
    eval (m + 3) ptable level (.letE x V B) env T = some (r, Tf) := by
  -- extract the operand's convergence (at fuel m+1) from the converging redex
  have h2 := h_redex
  rw [eval_app_lam_v_step (m + 2) ptable level x B V env T,
      eval_lam (m + 1) ptable level [x] B env T] at h2
  simp only at h2
  rw [evalList_single m ptable level V env T] at h2
  cases h_ev : eval (m + 1) ptable level V env T with
  | none => rw [h_ev] at h2; simp at h2
  | some pr =>
      obtain ⟨v_val, T'⟩ := pr
      -- purity carries the standard gate through the operand to the post-operand state
      have h_ext : StateExtends T T' := eval_pure_extends h_pure h_heap h_ev
      have h_mat' : T'.levels.length > level + 1 := by have := h_ext.levels_le; omega
      have h_builtin' : builtinBaseApplyAt level T' := builtinBaseApplyAt_extends h_ext h_builtin0
      exact redex_to_letE_fixed m ptable level x B V env T h_depth v_val T' h_ev
        h_mat' h_builtin' r Tf h_redex

/-- `gate_redex_to_letE` at arbitrary fuel: the redex's convergence forces `3 ≤ k`
    (`app_lam_redex_min_fuel`), giving the `m + 3` shape. This is exactly the shape
    `frameβ_app_root_evalW_cond`'s `h_gate_b` requires (`eval k redex = some → eval k
    letE = some` on the b-side), so it discharges that hypothesis once the conditional
    statement carries the standard-gate + pure-operand premise. -/
theorem gate_redex_to_letE_anyfuel (k : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (B V : Expr) (env : Env) (T : TowerState)
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat0 : T.levels.length > level + 1)
    (h_builtin0 : builtinBaseApplyAt level T)
    (h_pure : Pure V = true) (h_heap : PureHeap T.heap)
    (r : Val) (Tf : TowerState)
    (h_redex : eval k ptable level (.app [.lam [x] B, V]) env T = some (r, Tf)) :
    eval k ptable level (.letE x V B) env T = some (r, Tf) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 :=
    ⟨k - 3, by have := app_lam_redex_min_fuel h_redex; omega⟩
  exact gate_redex_to_letE m ptable level x B V env T h_depth h_mat0 h_builtin0
    h_pure h_heap r Tf h_redex

/-- **eval's `.app` root-contraction branch, under the recognized conditional
    premise** — `frameβ_app_root_evalW_cond` with its abstract `h_gate_b` discharged.
    The premise is now exactly `DUMP_LAM.md` §0's standard-gate `BuiltinReady` (depth
    margin, level+1 materialized, builtin `base-apply` on the b-side) plus heap/operand
    purity — the same side conditions `contextual_beta_pure` carries for the lam-free
    cases. The cross-side relational work is the structural branch
    (`frameβ_app_structural_evalW`); the gate bridge is `gate_redex_to_letE_anyfuel`. So
    this is the *conditional* fundamental-lemma `.app` case — the only thing keeping it
    from the mutual `FrameStmtβ` is that those premises must be carried by the threaded
    statement (and the hard `.set`). -/
theorem frameβ_app_root_evalW (n : Nat) (ptable : PolicyTable) (level : Nat)
    (args : List Expr) (x : String) (body v exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (ih_eval : FrameβEvalStmtW n) (ih_list : FrameβEvalListStmtW n)
    (ih_via : FrameβApplyViaStmtW n)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (h1 : BetaRel (.app args) (.app [.lam [x] body, v]))
    (h2 : BetaRel (.letE x v body) exp_b)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    -- the recognized standard-gate + purity premise on the b-side (§0 Obstruction B):
    (h_depth : level + 1 < Tower.maxDepth)
    (h_mat0 : T_b.levels.length > level + 1)
    (h_builtin0 : builtinBaseApplyAt level T_b)
    (h_heap : PureHeap T_b.heap)
    (h_pure_op : ∀ y W C, exp_b = .letE y W C → Pure W = true)
    (heval : eval (n + 1) ptable level (.app args) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨f, a, rfl, hf, ha⟩ := h1.app_to_redex_inv
  obtain ⟨v', body', rfl, hv', hbody'⟩ := h2.letE_inv
  have hbrl : BetaRelList [f, a] [.lam [x] body', v'] :=
    .cons (hf.trans (BetaRel.congr hbody' (.lam [x] .hole))) (.cons (ha.trans hv') .nil)
  obtain ⟨r_b, T_b', h_redex_b, h_vv, h_ctx', h_he, hv_ra, hv_rb⟩ :=
    frameβ_app_structural_evalW n ptable level [f, a] [.lam [x] body', v']
      env_a env_b T_a T_b r_a T_a' ih_eval ih_list ih_via hresp_pt hbrl h_ctx heval
  refine ⟨r_b, T_b', ?_, h_vv, h_ctx', h_he, hv_ra, hv_rb⟩
  exact gate_redex_to_letE_anyfuel (n + 1) ptable level x body' v' env_b T_b
    h_depth h_mat0 h_builtin0 (h_pure_op x v' body' rfl) h_heap r_b T_b' h_redex_b

/-! ## 7n. The step-4 observation bridge (forward), modulo the fundamental lemma

The payoff direction: the cross-side `ValVisβ` fundamental lemma yields ground
`ObsConv` **refinement** in every context — the forward half of the (conditional)
ground `CtxEquiv` that `CtxEquiv.under_lam` (`CtxEquiv.lean`, already proved) lifts
through the binder *for free*. Three pieces compose: `BetaRel.congr` lifts `BetaRel
M N` into the context `C`; `WFCtxTβ.refl` instantiates the **cross-side** FL
**diagonally** (`env_a=env_b`, `T_a=T_b`) so it speaks about the *single-sided*
observation; and `ValVisβ_isGround_eq` collapses the related ground result to
*equality*, so the two sides converge to the *same* ground value. The fundamental
lemma itself (`hFL`, the cross-side eval simulation) is the remaining obligation —
its β-firing crux `.app` root is done (`frameβ_app_root_evalW`); assembling the
mutual statement that carries the `Pure` + `BuiltinReadyN` premise is the mechanical
remainder. -/

/-- **FL ⟹ forward ground-observational refinement (conditional).** Given the
    cross-side eval fundamental lemma `hFL`, at any well-formed, standard-gate, pure
    state, `M`'s convergences to a *ground* value are matched by `N` (for a
    `BetaRel`-pair `M`/`N`). This is the forward half of the conditional ground
    `CtxEquiv` — combined with the (operational) backward direction and the free
    `CtxEquiv.under_lam`, it gives the conditional `.lam` congruence. -/
theorem obsConv_refine_of_FL {M N : Expr} (d : Nat) (hβ : BetaRel M N)
    (hFL : ∀ (k : Nat) (pt : PolicyTable) (lvl : Nat) (ea eb : Expr)
             (va vb : Env) (Sa Sb : TowerState) (ra : Val) (Sa' : TowerState),
        BetaRel ea eb → Pure ea = true → PolicyTableRespectsBisimT pt →
        WFCtxTβ va vb Sa Sb lvl →
        BuiltinReadyN d pt lvl vb Sb → PureHeap Sb.heap →
        eval k pt lvl ea va Sa = some (ra, Sa') →
        ∃ rb Sb', eval k pt lvl eb vb Sb = some (rb, Sb') ∧
          ValVisβ ra rb Sa'.heap Sb'.heap)
    (C : Ctx) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState) (g : Val)
    (hg : g.isGround = true)
    (hresp : PolicyTableRespectsBisimT ptable)
    (hpure : Pure (C.plug M) = true)
    (hready : BuiltinReadyN d ptable level env T) (hheap : PureHeap T.heap)
    (hh : HeapValid T.heap) (hev_env : EnvValid env T.heap)
    (hlv : ∀ n e, T.envAt? n = some e → EnvValid e T.heap)
    (hpr : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (hobs : ObsConv (C.plug M) ptable level env T g) :
    ObsConv (C.plug N) ptable level env T g := by
  obtain ⟨k, T', hev⟩ := hobs
  obtain ⟨r_b, T_b', hev_b, hvv⟩ :=
    hFL k ptable level (C.plug M) (C.plug N) env env T T g T'
      (hβ.congr C) hpure hresp (WFCtxTβ.refl hh hev_env hlv hpr) hready hheap hev
  exact ⟨k, T_b', (ValVisβ_isGround_eq hg hvv) ▸ hev_b⟩

/-- **FL_rev ⟹ backward ground-observational refinement (conditional).** The mirror
    of `obsConv_refine_of_FL`: given the *reverse* eval fundamental lemma `hFL_rev`
    (the reduced b-side's convergence ⟹ the a-side's), `N`'s ground convergences are
    matched by `M`. Forward + backward give the conditional ground `CtxEquiv` `↔` — the
    base relation `CtxEquiv.under_lam` lifts through `.lam` for free. The two FLs are
    the remaining obligation; for the β redex/contractum they are the cross-side
    simulation in each direction (`gate_redex_to_letE` gives the operational core). -/
theorem obsConv_refine_of_FL_rev {M N : Expr} (d : Nat) (hβ : BetaRel M N)
    (hFL_rev : ∀ (k : Nat) (pt : PolicyTable) (lvl : Nat) (ea eb : Expr)
             (va vb : Env) (Sa Sb : TowerState) (rb : Val) (Sb' : TowerState),
        BetaRel ea eb → Pure ea = true → PolicyTableRespectsBisimT pt →
        WFCtxTβ va vb Sa Sb lvl →
        BuiltinReadyN d pt lvl vb Sb → PureHeap Sb.heap →
        eval k pt lvl eb vb Sb = some (rb, Sb') →
        ∃ ra Sa', eval k pt lvl ea va Sa = some (ra, Sa') ∧
          ValVisβ ra rb Sa'.heap Sb'.heap)
    (C : Ctx) (ptable : PolicyTable) (level : Nat) (env : Env) (T : TowerState) (g : Val)
    (hg : g.isGround = true)
    (hresp : PolicyTableRespectsBisimT ptable)
    (hpure : Pure (C.plug M) = true)
    (hready : BuiltinReadyN d ptable level env T) (hheap : PureHeap T.heap)
    (hh : HeapValid T.heap) (hev_env : EnvValid env T.heap)
    (hlv : ∀ n e, T.envAt? n = some e → EnvValid e T.heap)
    (hpr : ∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p)
    (hobs : ObsConv (C.plug N) ptable level env T g) :
    ObsConv (C.plug M) ptable level env T g := by
  obtain ⟨k, T', hev⟩ := hobs
  obtain ⟨r_a, T_a', hev_a, hvv⟩ :=
    hFL_rev k ptable level (C.plug M) (C.plug N) env env T T g T'
      (hβ.congr C) hpure hresp (WFCtxTβ.refl hh hev_env hlv hpr) hready hheap hev
  exact ⟨k, T_a', (ValVisβ_isGround_eq_right hg hvv) ▸ hev_a⟩

/-! ## 7o₀. The all-levels standard-gate premise `BuiltinReadyAll` / `BReady`

The d-window `BuiltinReadyN d` is the right premise for `contextual_beta_pure`
(lam-free, no closures) but **not** for the fundamental lemma: a closure created at
low em-depth can be *applied* arbitrarily deep — running its body below any syntactic
`d`-bound (`applyDirect`'s closure case). So the FL carries the **all-levels** standard
gate: a fully-materialized tower with builtin `base-apply` at every level. It is
preserved with no depth bookkeeping — `≥ maxDepth` rides `StateExtends.levels_le`,
gates ride `builtinBaseApplyAt_extends`, and `materialize` is a no-op (already full) so
`.em` needs no decrement. `BReady` bundles it with `PureHeap` (the FL's b-side premise);
`closed` / `alloc` mirror `BuiltinReadyP_closed` / `BuiltinReadyP_alloc`. -/

/-- The standard gate at *every* level of a fully-materialized tower. -/
def BuiltinReadyAll (T : TowerState) : Prop :=
  Tower.maxDepth ≤ T.levels.length ∧ ∀ L, L + 1 < Tower.maxDepth → builtinBaseApplyAt L T

/-- `BuiltinReadyAll` rides any state extension (`≥` via `levels_le`, gates via
    `builtinBaseApplyAt_extends`). -/
theorem BuiltinReadyAll.extends {T T' : TowerState}
    (hAll : BuiltinReadyAll T) (h_ext : StateExtends T T') : BuiltinReadyAll T' :=
  ⟨Nat.le_trans hAll.1 h_ext.levels_le,
   fun L hL => builtinBaseApplyAt_extends h_ext (hAll.2 L hL)⟩

/-- The FL's b-side premise: all-levels standard gate + pure heap. -/
def BReady (T : TowerState) : Prop := BuiltinReadyAll T ∧ PureHeap T.heap

/-- `BReady` is closed under evaluation of a pure expression (mirror of
    `BuiltinReadyP_closed`). -/
theorem BReady.closed {k : Nat} {ptable : PolicyTable} {level : Nat} {e : Expr}
    {env : Env} {T : TowerState} {v : Val} {T' : TowerState}
    (hBR : BReady T) (h_pe : Pure e = true)
    (h_ev : eval k ptable level e env T = some (v, T')) : BReady T' := by
  obtain ⟨hAll, h_heap⟩ := hBR
  have h_ext := eval_pure_extends h_pe h_heap h_ev
  exact ⟨hAll.extends h_ext, (((allPureIndep k).1 level e env T h_pe h_heap).2 ptable v T' h_ev).2⟩

/-- List version of `BReady.closed`: `BReady` is closed under `evalList` of a
    pure expression list. -/
theorem BReady.closedList {k : Nat} {ptable : PolicyTable} {level : Nat}
    {exps : List Expr} {env : Env} {T : TowerState} {vs : List Val} {T' : TowerState}
    (hBR : BReady T) (h_pl : PureList exps = true)
    (h_ev : evalList k ptable level exps env T = some (vs, T')) : BReady T' := by
  obtain ⟨hAll, h_heap⟩ := hBR
  have h_ext := evalList_pure_extends h_pl h_heap h_ev
  exact ⟨hAll.extends h_ext, (((allPureIndep k).2.1 level exps env T h_pl h_heap).2 ptable vs T' h_ev).2⟩

/-- `BReady` survives the `.letE` binding step (mirror of `BuiltinReadyP_alloc`). -/
theorem BReady.alloc {k : Nat} {ptable : PolicyTable} {level : Nat} {e : Expr}
    {env : Env} {T : TowerState} {v : Val} {T' : TowerState}
    (hBR : BReady T) (h_pe : Pure e = true)
    (h_ev : eval k ptable level e env T = some (v, T')) :
    BReady { T' with heap := T'.heap ++ [v] } := by
  obtain ⟨hAll, h_heap⟩ := hBR
  have h_ext := eval_pure_extends h_pe h_heap h_ev
  obtain ⟨h_pval, h_heap'⟩ := ((allPureIndep k).1 level e env T h_pe h_heap).2 ptable v T' h_ev
  refine ⟨hAll.extends (h_ext.trans (StateExtends.of_heap_append T' [v])), ?_⟩
  exact PureHeap_append _ _ h_heap' (fun w hw => by simp at hw; subst hw; exact h_pval)

/-! ## 7o. The pure conditional eval statement (FL assembly — non-recursive cases)

Assembling the forward fundamental lemma `hFL` (`obsConv_refine_of_FL`) means
re-cutting the mutual statement to carry the premise the `.app` root case needs:
`Pure exp_a` + the b-side all-levels gate `BReady T_b` (§7o₀). Under
`Pure exp_a` the hard `.set` / `.installPolicy` cases are **vacuous**
(`Pure (.set _ _) = Pure (.installPolicy _) = false`), and the non-recursive cases
forward verbatim to the premise-free `frameβ_*_caseW` lemmas (the added premises are
unused — same conclusion). This is the first slice; the recursive cases
(`.ifte`/`.seq`/`.letE`/`.em`) and `.app` re-cut (threading the premise to the IH via
`BuiltinReadyN_extends` / `BetaRel.pure_preserve`) follow. -/

/-- The eval clause carrying the conditional premise (`Pure exp_a` + the b-side
    all-levels gate `BReady T_b`). Conclusion identical to `FrameβEvalStmtW`. -/
def FrameβEvalStmtWP (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (exp_a exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    BetaRel exp_a exp_b →
    Pure exp_a = true →
    PolicyTableRespectsBisimT ptable →
    WFCtxTβ env_a env_b T_a T_b level →
    BReady T_b →
    eval n ptable level exp_a env_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      eval n ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧
      WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧
      ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap

section
variable (n : Nat) (ptable : PolicyTable) (level : Nat) (exp_b : Expr)
  (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
  (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
include h_ctx

/-- `.num` on `FrameβEvalStmtWP` — forwards to `frameβ_num_caseW` (premise unused). -/
theorem frameβ_num_caseWP (i : Int)
    (hβ : BetaRel (.num i) exp_b) (_hpure : Pure (.num i) = true)
    (_hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.num i) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap :=
  frameβ_num_caseW n ptable level i exp_b env_a env_b T_a T_b r_a T_a' hβ h_ctx heval

/-- `.bool` on `FrameβEvalStmtWP` — forwards to `frameβ_bool_caseW`. -/
theorem frameβ_bool_caseWP (c : Bool)
    (hβ : BetaRel (.bool c) exp_b) (_hpure : Pure (.bool c) = true)
    (_hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.bool c) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap :=
  frameβ_bool_caseW n ptable level c exp_b env_a env_b T_a T_b r_a T_a' hβ h_ctx heval

/-- `.var` on `FrameβEvalStmtWP` — forwards to `frameβ_var_caseW`. -/
theorem frameβ_var_caseWP (y : String)
    (hβ : BetaRel (.var y) exp_b) (_hpure : Pure (.var y) = true)
    (_hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.var y) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap :=
  frameβ_var_caseW n ptable level y exp_b env_a env_b T_a T_b r_a T_a' hβ h_ctx heval

/-- `.lam` on `FrameβEvalStmtWP` — forwards to `frameβ_lam_caseW`. -/
theorem frameβ_lam_caseWP (ps : List String) (body : Expr)
    (hβ : BetaRel (.lam ps body) exp_b) (_hpure : Pure (.lam ps body) = true)
    (_hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.lam ps body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap :=
  frameβ_lam_caseW n ptable level ps body exp_b env_a env_b T_a T_b r_a T_a' hβ h_ctx heval

/-- `.quote` on `FrameβEvalStmtWP` — forwards to `frameβ_quote_caseW`. -/
theorem frameβ_quote_caseWP (v : Val)
    (hβ : BetaRel (.quote v) exp_b) (_hpure : Pure (.quote v) = true)
    (_hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.quote v) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap :=
  frameβ_quote_caseW n ptable level v exp_b env_a env_b T_a T_b r_a T_a' hβ h_ctx heval

omit h_ctx in
/-- **`.set` is vacuous under `Pure`** — `Pure (.set _ _) = false`. The pure
    restriction dissolves the hard cross-side meta-mutation case. -/
theorem frameβ_set_caseWP (x : String) (e : Expr)
    (_hβ : BetaRel (.set x e) exp_b) (hpure : Pure (.set x e) = true)
    (_hbr : BReady T_b)
    (_heval : eval (n + 1) ptable level (.set x e) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  simp [Pure] at hpure

omit h_ctx in
/-- **`.installPolicy` is vacuous under `Pure`** — `Pure (.installPolicy _) = false`. -/
theorem frameβ_installPolicy_caseWP (idx : Nat)
    (_hβ : BetaRel (.installPolicy idx) exp_b) (hpure : Pure (.installPolicy idx) = true)
    (_hbr : BReady T_b)
    (_heval : eval (n + 1) ptable level (.installPolicy idx) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  simp [Pure] at hpure

end

/-! ### 7o (cont.). The recursive eval cases over `FrameβEvalStmtWP`

These take the premised IH `FrameβEvalStmtWP n` (the leaf-forward trick fails — a
recursive case must call the IH on sub-expressions, and the IH carries the premise).
So they re-cut the corresponding `frameβ_*_evalW` proof, threading the premise to each
sub-call: `Pure` decomposes structurally (and `BetaRel.pure_preserve` carries it to the
b-side sub-expression); the b-side all-levels gate `BReady` rides across the (pure)
b-side sub-evaluations by `BReady.closed` (and `BReady.alloc` for `.letE`). -/

/-- `.ifte` on `FrameβEvalStmtWP` — re-cut of `frameβ_ifte_evalW`, threading the premise
    across the (pure) condition evaluation to the branch sub-call. -/
theorem frameβ_ifte_evalWP (n : Nat) (ptable : PolicyTable) (level : Nat)
    (c t e exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtWP n) (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.ifte c t e) exp_b) (hpure : Pure (.ifte c t e) = true)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.ifte c t e) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨c', t', e', rfl, hβ_c, hβ_t, hβ_e⟩ := hβ.ifte_inv
  simp only [Pure, Bool.and_eq_true] at hpure
  obtain ⟨⟨hpc, hpt⟩, hpe⟩ := hpure
  cases hc : eval n ptable level c env_a T_a with
  | none => rw [eval_ifte_none n ptable level c t e env_a T_a hc] at heval; simp at heval
  | some pr =>
    obtain ⟨cv_a, T_c_a⟩ := pr
    rw [eval_ifte_step n ptable level c t e env_a T_a T_c_a cv_a hc] at heval
    obtain ⟨cv_b, T_c_b, h_eval_c_b, h_vv_c, h_ctx_c, h_he_c, _hv_ca, _hv_cb⟩ :=
      ih ptable level c c' env_a env_b T_a T_b cv_a T_c_a hβ_c hpc hresp_pt h_ctx hbr hc
    have hbr_c : BReady T_c_b := BReady.closed hbr (hβ_c.pure_preserve hpc) h_eval_c_b
    have hβ_branch : BetaRel (ifteBranch cv_a t e) (ifteBranch cv_b t' e') := by
      by_cases hbf : cv_a = .bool false
      · have hbf_b : cv_b = .bool false := (ValVisβ_bool_false_iff h_vv_c).mp hbf
        subst hbf; subst hbf_b; exact hβ_e
      · have hbf_b : cv_b ≠ .bool false :=
          fun hc' => hbf ((ValVisβ_bool_false_iff h_vv_c).mpr hc')
        rw [ifteBranch_ne t e hbf, ifteBranch_ne t' e' hbf_b]; exact hβ_t
    have hp_branch : Pure (ifteBranch cv_a t e) = true := by
      by_cases hbf : cv_a = .bool false
      · subst hbf; exact hpe
      · rw [ifteBranch_ne t e hbf]; exact hpt
    obtain ⟨r_b, T_b', h_eval_branch_b, h_vv_r, h_ctx_out, h_he_branch, hv_ra, hv_rb⟩ :=
      ih ptable level (ifteBranch cv_a t e) (ifteBranch cv_b t' e')
        env_a env_b T_c_a T_c_b r_a T_a' hβ_branch hp_branch hresp_pt h_ctx_c hbr_c heval
    refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_out, h_he_c.trans h_he_branch, hv_ra, hv_rb⟩
    rw [eval_ifte_step n ptable level c' t' e' env_b T_b T_c_b cv_b h_eval_c_b]
    exact h_eval_branch_b

/-- `.seq` on `FrameβEvalStmtWP` — re-cut of `frameβ_seq_evalW`; only the
    multi-element case recurses twice (premise threaded across the head eval). -/
theorem frameβ_seq_evalWP (n : Nat) (ptable : PolicyTable) (level : Nat)
    (exps : List Expr) (exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtWP n) (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.seq exps) exp_b) (hpure : Pure (.seq exps) = true)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.seq exps) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  cases exps with
  | nil =>
      have hb := hβ.seq_nil_inv; subst hb
      simp only [eval, Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, ht⟩ := heval; subst hr; subst ht
      exact ⟨.nilV, T_b, by simp only [eval], fun m => by cases m <;> simp [ValVisβ_aux],
             h_ctx, HeapEvolutionβ.refl _ _, trivial, trivial⟩
  | cons e rest =>
      simp only [Pure, PureList, Bool.and_eq_true] at hpure
      obtain ⟨hpe, hprest⟩ := hpure
      cases rest with
      | nil =>
          obtain ⟨e', rest', rfl, hβ_e, hβ_rest⟩ := hβ.seq_cons_inv
          have hr : rest' = [] := Expr.seq.inj hβ_rest.seq_nil_inv
          subst hr
          simp only [eval] at heval
          obtain ⟨r_b, T_b', h_eval_e_b, h_vv_r, h_ctx_out, h_he, hv_ra, hv_rb⟩ :=
            ih ptable level e e' env_a env_b T_a T_b r_a T_a' hβ_e hpe hresp_pt h_ctx hbr heval
          refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_out, h_he, hv_ra, hv_rb⟩
          simp only [eval]; exact h_eval_e_b
      | cons f rest2 =>
          obtain ⟨e', rest', rfl, hβ_e, hβ_rest⟩ := hβ.seq_cons_inv
          obtain ⟨f', rest2', hr'⟩ : ∃ f' rest2', rest' = f' :: rest2' := by
            obtain ⟨f', rest2', hb_eq, _, _⟩ := hβ_rest.seq_cons_inv
            exact ⟨f', rest2', Expr.seq.inj hb_eq⟩
          subst hr'
          cases hee : eval n ptable level e env_a T_a with
          | none =>
              rw [eval_seq_cons_none n ptable level e f rest2 env_a T_a hee] at heval
              simp at heval
          | some pr =>
              obtain ⟨v_a, T_e_a⟩ := pr
              rw [eval_seq_cons_step n ptable level e f rest2 env_a T_a T_e_a v_a hee] at heval
              obtain ⟨v_b, T_e_b, h_eval_e_b, _h_vv_v, h_ctx_e, h_he_e, _, _⟩ :=
                ih ptable level e e' env_a env_b T_a T_b v_a T_e_a hβ_e hpe hresp_pt h_ctx hbr hee
              have hbr_e : BReady T_e_b := BReady.closed hbr (hβ_e.pure_preserve hpe) h_eval_e_b
              obtain ⟨r_b, T_b', h_eval_rest_b, h_vv_r, h_ctx_out, h_he_rest, hv_ra, hv_rb⟩ :=
                ih ptable level (.seq (f :: rest2)) (.seq (f' :: rest2'))
                  env_a env_b T_e_a T_e_b r_a T_a' hβ_rest hprest hresp_pt h_ctx_e hbr_e heval
              refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_out, h_he_e.trans h_he_rest, hv_ra, hv_rb⟩
              rw [eval_seq_cons_step n ptable level e' f' rest2' env_b T_b T_e_b v_b h_eval_e_b]
              exact h_eval_rest_b

/-- `.letE` on `FrameβEvalStmtWP` — re-cut of `frameβ_letE_evalW` (alloc-validity
    plumbing verbatim, body-agnostic), threading the body call's premise across the
    bound-expr eval **and** the allocation via `BuiltinReadyP_alloc`. -/
theorem frameβ_letE_evalWP (n : Nat) (ptable : PolicyTable) (level : Nat)
    (x : String) (e1 body exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtWP n) (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.letE x e1 body) exp_b) (hpure : Pure (.letE x e1 body) = true)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.letE x e1 body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨e1', body', rfl, hβ_e, hβ_body⟩ := hβ.letE_inv
  simp only [Pure, Bool.and_eq_true] at hpure
  obtain ⟨hpe1, hpbody⟩ := hpure
  simp only [eval] at heval
  cases he : eval n ptable level e1 env_a T_a with
  | none => rw [he] at heval; simp at heval
  | some pr =>
    obtain ⟨v_a, T_a_inner⟩ := pr
    rw [he] at heval
    obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner, hv_va, hv_vb⟩ :=
      ih ptable level e1 e1' env_a env_b T_a T_b v_a T_a_inner hβ_e hpe1 hresp_pt h_ctx hbr he
    have hbr_body : BReady { T_b_inner with heap := T_b_inner.heap ++ [v_b] } :=
      BReady.alloc hbr (hβ_e.pure_preserve hpe1) h_eval_e_b
    simp only [TowerState.alloc, Heap.alloc] at heval
    -- alloc validity (body-agnostic; verbatim from `frameβ_letE_evalW`)
    have h_lookup_a : (T_a_inner.heap ++ [v_a])[T_a_inner.heap.length]? = some v_a := getElem?_snoc _ _
    have h_lookup_b : (T_b_inner.heap ++ [v_b])[T_b_inner.heap.length]? = some v_b := getElem?_snoc _ _
    have hh_a_alloc : HeapValid (T_a_inner.heap ++ [v_a]) := by
      intro i v hp
      by_cases h_lt : i < T_a_inner.heap.length
      · have hp_old : T_a_inner.heap[i]? = some v := by
          rw [← getElem?_prefix T_a_inner.heap [v_a] i h_lt]; exact hp
        exact ValValid.heap_extends v (h_ctx_inner.hv_a i v hp_old) ⟨[v_a], rfl⟩
      · have h_eq : i = T_a_inner.heap.length := by
          have h_le : i < (T_a_inner.heap ++ [v_a]).length := by
            rw [List.getElem?_eq_some_iff] at hp; obtain ⟨h, _⟩ := hp; exact h
          simp [List.length_append] at h_le; omega
        subst h_eq; rw [h_lookup_a] at hp; simp only [Option.some.injEq] at hp; subst hp
        exact ValValid.heap_extends v_a hv_va ⟨[v_a], rfl⟩
    have hh_b_alloc : HeapValid (T_b_inner.heap ++ [v_b]) := by
      intro i v hp
      by_cases h_lt : i < T_b_inner.heap.length
      · have hp_old : T_b_inner.heap[i]? = some v := by
          rw [← getElem?_prefix T_b_inner.heap [v_b] i h_lt]; exact hp
        exact ValValid.heap_extends v (h_ctx_inner.hv_b i v hp_old) ⟨[v_b], rfl⟩
      · have h_eq : i = T_b_inner.heap.length := by
          have h_le : i < (T_b_inner.heap ++ [v_b]).length := by
            rw [List.getElem?_eq_some_iff] at hp; obtain ⟨h, _⟩ := hp; exact h
          simp [List.length_append] at h_le; omega
        subst h_eq; rw [h_lookup_b] at hp; simp only [Option.some.injEq] at hp; subst hp
        exact ValValid.heap_extends v_b hv_vb ⟨[v_b], rfl⟩
    have hev_a' : EnvValid (.cons x T_a_inner.heap.length env_a) (T_a_inner.heap ++ [v_a]) :=
      envValid_cons_fresh x v_a env_a T_a_inner.heap h_ctx_inner.ev_a
    have hev_b' : EnvValid (.cons x T_b_inner.heap.length env_b) (T_b_inner.heap ++ [v_b]) :=
      envValid_cons_fresh x v_b env_b T_b_inner.heap h_ctx_inner.ev_b
    have h_env' : EnvVisβ (.cons x T_a_inner.heap.length env_a) (.cons x T_b_inner.heap.length env_b)
        (T_a_inner.heap ++ [v_a]) (T_b_inner.heap ++ [v_b]) :=
      EnvVisβ_alloc_cons x env_a env_b v_a v_b T_a_inner.heap T_b_inner.heap
        h_ctx_inner.hv_a h_ctx_inner.hv_b h_ctx_inner.ev_a h_ctx_inner.ev_b hv_va hv_vb h_vv_v
        h_ctx_inner.env_visβ
    obtain ⟨hlva', hlvb', hlvisβ'⟩ :=
      level_fields_alloc v_a v_b h_ctx_inner.hv_a h_ctx_inner.hv_b
        h_ctx_inner.level_envs_valid_a h_ctx_inner.level_envs_valid_b h_ctx_inner.level_envs_visβ
    have h_ctx_alloc : WFCtxTβ (.cons x T_a_inner.heap.length env_a)
        (.cons x T_b_inner.heap.length env_b)
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } level :=
      { policy_eq_at := h_ctx_inner.policy_eq_at
        hv_a := hh_a_alloc, hv_b := hh_b_alloc, ev_a := hev_a', ev_b := hev_b'
        policy_resp := h_ctx_inner.policy_resp
        env_visβ := h_env'
        level_envs_valid_a := hlva', level_envs_valid_b := hlvb'
        level_count_eq := h_ctx_inner.level_count_eq
        policies_eq := h_ctx_inner.policies_eq
        policies_resp_all := h_ctx_inner.policies_resp_all
        level_envs_visβ := hlvisβ' }
    obtain ⟨r_b, T_b', h_eval_b_b, h_vv_r, h_ctx_body, h_he_body, hv_ra, hv_rb⟩ :=
      ih ptable level body body'
        (.cons x T_a_inner.heap.length env_a) (.cons x T_b_inner.heap.length env_b)
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } r_a T_a'
        hβ_body hpbody hresp_pt h_ctx_alloc hbr_body heval
    have h_he_alloc : HeapEvolutionβ T_a_inner T_b_inner
        { T_a_inner with heap := T_a_inner.heap ++ [v_a] }
        { T_b_inner with heap := T_b_inner.heap ++ [v_b] } :=
      HeapEvolutionβ.from_heapExt h_ctx_inner.hv_a h_ctx_inner.hv_b ⟨[v_a], rfl⟩ ⟨[v_b], rfl⟩
    have h_he_chain : HeapEvolutionβ T_a T_b T_a' T_b' :=
      h_he_inner.trans (h_he_alloc.trans h_he_body)
    refine ⟨r_b, T_b', ?_, h_vv_r, ?_, h_he_chain, hv_ra, hv_rb⟩
    · simp only [eval, h_eval_e_b, TowerState.alloc, Heap.alloc]; exact h_eval_b_b
    · exact
      { policy_eq_at := h_ctx_body.policy_eq_at
        hv_a := h_ctx_body.hv_a, hv_b := h_ctx_body.hv_b
        ev_a := h_ctx.ev_a.length_mono h_he_chain.len_a
        ev_b := h_ctx.ev_b.length_mono h_he_chain.len_b
        policy_resp := h_ctx_body.policy_resp
        env_visβ := h_he_chain.envVisβ_preserve env_a env_b h_ctx.ev_a h_ctx.ev_b h_ctx.env_visβ
        level_envs_valid_a := h_ctx_body.level_envs_valid_a
        level_envs_valid_b := h_ctx_body.level_envs_valid_b
        level_count_eq := h_ctx_body.level_count_eq
        policies_eq := h_ctx_body.policies_eq
        policies_resp_all := h_ctx_body.policies_resp_all
        level_envs_visβ := h_ctx_body.level_envs_visβ }

/-- `.em` on `FrameβEvalStmtWP` — **clean under `BReady`**: the full tower (both
    sides, via `level_count_eq`) makes `materialize (level+1)` a *no-op*
    (`T_mat = T`), so the body runs at `level+1` in the *same* towers, carrying
    `BReady T_b` directly. No depth decrement and none of `frameβ_em_eval`'s
    `materialize_MatInvβ` plumbing — the level-`(level+1)` `WFCtxTβ` is read straight
    off the input's level fields, and rebuilt at `level` from the body output. -/
theorem frameβ_em_evalWP (n : Nat) (ptable : PolicyTable) (level : Nat)
    (body exp_b : Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih : FrameβEvalStmtWP n) (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.em body) exp_b) (hpure : Pure (.em body) = true)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.em body) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b', eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨body', rfl, hβ_body⟩ := hβ.em_inv
  simp only [Pure] at hpure
  simp only [eval] at heval
  have hTb_full : Tower.maxDepth ≤ T_b.levels.length := hbr.1.1
  have hTa_full : Tower.maxDepth ≤ T_a.levels.length := h_ctx.level_count_eq ▸ hTb_full
  cases hm_a : T_a.materialize (level + 1) with
  | none => simp [hm_a] at heval
  | some T_a_mat =>
      simp only [hm_a] at heval
      have hd : level + 1 < Tower.maxDepth := by
        unfold TowerState.materialize at hm_a
        split at hm_a
        · exact absurd hm_a (by simp)
        · omega
      have hTa_eq : T_a_mat = T_a := by
        have hnoop := materialize_noop (show T_a.levels.length > level + 1 by omega) hd
        rw [hnoop] at hm_a; exact (Option.some.inj hm_a).symm
      subst T_a_mat
      have hm_b : T_b.materialize (level + 1) = some T_b :=
        materialize_noop (show T_b.levels.length > level + 1 by omega) hd
      cases he_a : T_a.envAt? (level + 1) with
      | none => simp [he_a] at heval
      | some upEnv_a =>
          simp only [he_a] at heval
          obtain ⟨upEnv_b, he_b⟩ : ∃ e, T_b.envAt? (level + 1) = some e :=
            envAt?_some_cross T_a T_b (level + 1) upEnv_a h_ctx.level_count_eq he_a
          have h_ctx_up : WFCtxTβ upEnv_a upEnv_b T_a T_b (level + 1) :=
            { policy_eq_at := h_ctx.policies_eq (level + 1)
              hv_a := h_ctx.hv_a, hv_b := h_ctx.hv_b
              ev_a := h_ctx.level_envs_valid_a (level + 1) upEnv_a he_a
              ev_b := h_ctx.level_envs_valid_b (level + 1) upEnv_b he_b
              policy_resp := fun p hp => h_ctx.policies_resp_all (level + 1) p hp
              env_visβ := h_ctx.level_envs_visβ (level + 1) upEnv_a upEnv_b he_a he_b
              level_envs_valid_a := h_ctx.level_envs_valid_a
              level_envs_valid_b := h_ctx.level_envs_valid_b
              level_count_eq := h_ctx.level_count_eq
              policies_eq := h_ctx.policies_eq
              policies_resp_all := h_ctx.policies_resp_all
              level_envs_visβ := h_ctx.level_envs_visβ }
          obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_ctx_out, h_he_body, hv_ra, hv_rb⟩ :=
            ih ptable (level + 1) body body' upEnv_a upEnv_b T_a T_b r_a T_a'
              hβ_body hpure hresp_pt h_ctx_up hbr heval
          refine ⟨r_b, T_b', ?_, h_vv_r, ?_, h_he_body, hv_ra, hv_rb⟩
          · simp only [eval, hm_b, he_b]; exact h_eval_b
          · exact
            { policy_eq_at := h_ctx_out.policies_eq level
              hv_a := h_ctx_out.hv_a, hv_b := h_ctx_out.hv_b
              ev_a := h_ctx.ev_a.length_mono h_he_body.len_a
              ev_b := h_ctx.ev_b.length_mono h_he_body.len_b
              policy_resp := fun p hp => h_ctx_out.policies_resp_all level p hp
              env_visβ := h_he_body.envVisβ_preserve env_a env_b h_ctx.ev_a h_ctx.ev_b h_ctx.env_visβ
              level_envs_valid_a := h_ctx_out.level_envs_valid_a
              level_envs_valid_b := h_ctx_out.level_envs_valid_b
              level_count_eq := h_ctx_out.level_count_eq
              policies_eq := h_ctx_out.policies_eq
              policies_resp_all := h_ctx_out.policies_resp_all
              level_envs_visβ := h_ctx_out.level_envs_visβ }

/-! ## 7p. The other three mutual clauses over `BReady`

eval's `.app` calls `evalList` then `applyVia`, so those clauses must be premised
too (eval's `.app` will feed them its `BReady`). Re-cuts of `frameβ_evalList_evalW`
/ `frameβ_applyVia_eval` / `frameβ_applyDirect_evalW` onto the `BReady` premise; the
threading is the same `BReady.closed` / `BReady.alloc` used in the eval cases. The
value-side premise is `PureVal` / `PureValList` (the closure bodies a closure-op
carries are pure). -/

/-- `evalList` over `BReady` (the premised analog of `FrameβEvalListStmtW`). -/
def FrameβEvalListStmtWP (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (exps_a exps_b : List Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (rs_a : List Val) (T_a' : TowerState),
    BetaRelList exps_a exps_b →
    PureList exps_a = true →
    PolicyTableRespectsBisimT ptable →
    WFCtxTβ env_a env_b T_a T_b level →
    BReady T_b →
    evalList n ptable level exps_a env_a T_a = some (rs_a, T_a') →
    ∃ rs_b T_b',
      evalList n ptable level exps_b env_b T_b = some (rs_b, T_b') ∧
      ListValVisβ rs_a rs_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ListValValid rs_a T_a'.heap ∧ ListValValid rs_b T_b'.heap

/-- The `evalList` inductive step over `BReady` — re-cut of `frameβ_evalList_evalW`,
    threading `BReady` across the (pure) head evaluation via `BReady.closed`. -/
theorem frameβ_evalList_evalWP (n : Nat)
    (ih_eval : FrameβEvalStmtWP n) (ih_list : FrameβEvalListStmtWP n) :
    FrameβEvalListStmtWP (n + 1) := by
  intro ptable level exps_a exps_b env_a env_b T_a T_b rs_a T_a' hβ hpure hresp_pt h_ctx hbr heval
  cases hβ with
  | nil =>
      simp only [evalList, Option.some.injEq, Prod.mk.injEq] at heval
      obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
      exact ⟨[], T_b, by simp [evalList], trivial, h_ctx, HeapEvolutionβ.refl _ _, trivial, trivial⟩
  | cons hβ_e hβ_rest =>
      rename_i e e' rest rest'
      simp only [PureList, Bool.and_eq_true] at hpure
      obtain ⟨hpe, hprest⟩ := hpure
      simp only [evalList] at heval
      cases he : eval n ptable level e env_a T_a with
      | none => rw [he] at heval; simp at heval
      | some pr =>
          obtain ⟨v_a, T_a_inner⟩ := pr
          rw [he] at heval; simp only at heval
          cases hrest : evalList n ptable level rest env_a T_a_inner with
          | none => rw [hrest] at heval; simp at heval
          | some pr2 =>
              obtain ⟨vs_a, T_a_inner2⟩ := pr2
              rw [hrest] at heval; simp only [Option.some.injEq, Prod.mk.injEq] at heval
              obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
              obtain ⟨v_b, T_b_inner, h_eval_e_b, h_vv_v, h_ctx_inner, h_he_inner, hv_va, hv_vb⟩ :=
                ih_eval ptable level e e' env_a env_b T_a T_b v_a T_a_inner hβ_e hpe hresp_pt h_ctx hbr he
              have hbr_inner : BReady T_b_inner := BReady.closed hbr (hβ_e.pure_preserve hpe) h_eval_e_b
              obtain ⟨vs_b, T_b_inner2, h_eval_rest_b, h_lvv, h_ctx_inner2, h_he_inner2,
                      hv_vsa, hv_vsb⟩ :=
                ih_list ptable level rest rest' env_a env_b T_a_inner T_b_inner vs_a T_a_inner2
                  hβ_rest hprest hresp_pt h_ctx_inner hbr_inner hrest
              have h_vv_v' : ValVisβ v_a v_b T_a_inner2.heap T_b_inner2.heap :=
                h_he_inner2.valVisβ_preserve v_a v_b hv_va hv_vb h_vv_v
              have hv_va' : ValValid v_a T_a_inner2.heap := ValValid.length_mono v_a hv_va h_he_inner2.len_a
              have hv_vb' : ValValid v_b T_b_inner2.heap := ValValid.length_mono v_b hv_vb h_he_inner2.len_b
              refine ⟨v_b :: vs_b, T_b_inner2, ?_, ⟨h_vv_v', h_lvv⟩, h_ctx_inner2,
                      h_he_inner.trans h_he_inner2, ⟨hv_va', hv_vsa⟩, ⟨hv_vb', hv_vsb⟩⟩
              simp [evalList, h_eval_e_b, h_eval_rest_b]

/-! ### 7p (cont.). Purity foundations for the `applyVia` / `applyDirect` clauses

Those clauses run a closure's body via the eval IH, which needs `Pure body` + `BReady`
at the *post-arg-binding* state. Two facts carry that: **`ValVisβ_pureVal`** transfers
`PureVal` to the b-side (closure bodies via `BetaRel.pure_preserve`), and
**`allocStep_foldl_pureHeap`** keeps `PureHeap` across the multi-arg `allocStep` binding
(each step appends a pure arg value). -/

/-- **`ValVisβ` transfers purity (forward).** A `ValVisβ`-related b-side value is pure
    when the a-side is — ground values are equal, closure bodies are `BetaRel`-related
    (`BetaRel.pure_preserve`). Carries `PureValList args_a` to the b-side args. -/
theorem ValVisβ_pureVal : ∀ {a b : Val} {h_a h_b : Heap},
    ValVisβ a b h_a h_b → PureVal a = true → PureVal b = true
  | .num _, _, _, _, h, hpa => by rw [closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpa
  | .bool _, _, _, _, h, hpa => by rw [closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpa
  | .nilV, _, _, _, h, hpa => by rw [closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpa
  | .sym _, _, _, _, h, hpa => by rw [closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpa
  | .prim _, _, _, _, h, hpa => by rw [closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpa
  | .builtinBaseApply, _, _, _, h, hpa => by rw [closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpa
  | .cons x y, _, _, _, h, hpa => by
      obtain ⟨xb, yb, rfl, hvx, hvy⟩ := ValVisβ_cons_inv h
      simp only [PureVal, Bool.and_eq_true] at hpa ⊢
      exact ⟨ValVisβ_pureVal hvx hpa.1, ValVisβ_pureVal hvy hpa.2⟩
  | .closure ps body cenv, _, _, _, h, hpa => by
      obtain ⟨body', cenv_b, rfl⟩ := ValVisβ_closure_inv h
      obtain ⟨_, hβ_body, _⟩ := closure_ValVisβ_imp h
      simp only [PureVal] at hpa ⊢
      exact hβ_body.pure_preserve hpa

/-- `PureValList` transfers across `ListValVisβ` (pointwise `ValVisβ_pureVal`). -/
theorem ListValVisβ_pureValList : ∀ {as bs : List Val} {h_a h_b : Heap},
    ListValVisβ as bs h_a h_b → PureValList as = true → PureValList bs = true
  | [], [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, ⟨hh, ht⟩, hpa => by
      simp only [PureValList, Bool.and_eq_true] at hpa ⊢
      exact ⟨ValVisβ_pureVal hh hpa.1, ListValVisβ_pureValList ht hpa.2⟩
  | [], _ :: _, _, _, hv, _ => hv.elim
  | _ :: _, [], _, _, hv, _ => hv.elim

/-- Reverse direction of `ValVisβ_pureVal`: a-side value purity is recoverable
    from the b-side, because β closures keep purity *both ways*
    (`BetaRel.pure_eq`).  This is what lets the cross-side fundamental lemma run
    with only the b-side `BReady` premise — no a-side heap-purity hypothesis. -/
theorem ValVisβ_pureVal_rev : ∀ {a b : Val} {h_a h_b : Heap},
    ValVisβ a b h_a h_b → PureVal b = true → PureVal a = true
  | .num _, _, _, _, h, hpb => by rw [← closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpb
  | .bool _, _, _, _, h, hpb => by rw [← closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpb
  | .nilV, _, _, _, h, hpb => by rw [← closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpb
  | .sym _, _, _, _, h, hpb => by rw [← closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpb
  | .prim _, _, _, _, h, hpb => by rw [← closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpb
  | .builtinBaseApply, _, _, _, h, hpb => by rw [← closedVal_ValVisβ_eq _ _ _ _ rfl h]; exact hpb
  | .cons x y, _, _, _, h, hpb => by
      obtain ⟨xb, yb, rfl, hvx, hvy⟩ := ValVisβ_cons_inv h
      simp only [PureVal, Bool.and_eq_true] at hpb ⊢
      exact ⟨ValVisβ_pureVal_rev hvx hpb.1, ValVisβ_pureVal_rev hvy hpb.2⟩
  | .closure ps body cenv, _, _, _, h, hpb => by
      obtain ⟨body', cenv_b, rfl⟩ := ValVisβ_closure_inv h
      obtain ⟨_, hβ_body, _⟩ := closure_ValVisβ_imp h
      simp only [PureVal] at hpb ⊢
      rw [hβ_body.pure_eq]; exact hpb

/-- List lift of `ValVisβ_pureVal_rev`. -/
theorem ListValVisβ_pureValList_rev : ∀ {as bs : List Val} {h_a h_b : Heap},
    ListValVisβ as bs h_a h_b → PureValList bs = true → PureValList as = true
  | [], [], _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, ⟨hh, ht⟩, hpb => by
      simp only [PureValList, Bool.and_eq_true] at hpb ⊢
      exact ⟨ValVisβ_pureVal_rev hh hpb.1, ListValVisβ_pureValList_rev ht hpb.2⟩
  | [], _ :: _, _, _, hv, _ => hv.elim
  | _ :: _, [], _, _, hv, _ => hv.elim

/-- `PureHeap` survives the multi-arg `allocStep` binding when every bound value is
    pure (each step appends `vp.1` via `Heap.alloc`). -/
theorem allocStep_foldl_pureHeap : ∀ (lst : List (Val × String)) (h : Heap) (cenv : Env),
    PureHeap h → (∀ vp ∈ lst, PureVal vp.1 = true) →
    PureHeap (lst.foldl allocStep (h, cenv)).1
  | [], h, _, hh, _ => hh
  | (v, p) :: tl, h, cenv, hh, hpure => by
      have hv : PureVal v = true := hpure (v, p) (by simp)
      have hh' : PureHeap (h ++ [v]) :=
        PureHeap_append h [v] hh (fun w hw => by simp at hw; subst hw; exact hv)
      have htl : ∀ vp ∈ tl, PureVal vp.1 = true := fun vp hvp => hpure vp (List.mem_cons_of_mem _ hvp)
      have hrec := allocStep_foldl_pureHeap tl (h ++ [v]) (.cons p h.length cenv) hh' htl
      simpa only [List.foldl_cons, allocStep, Heap.alloc] using hrec

/-- Every zipped `(value, param)` pair drawn from a `PureValList` has a pure value —
    the hypothesis `allocStep_foldl_pureHeap` consumes for the closure binding. -/
theorem pureValList_zip_fst : ∀ {as : List Val} {bs : List String},
    PureValList as = true → ∀ vp ∈ as.zip bs, PureVal vp.1 = true
  | [], _, _, vp, hvp => by simp at hvp
  | _ :: _, [], _, vp, hvp => by simp at hvp
  | a :: as, b :: bs, hpa, vp, hvp => by
      simp only [PureValList, Bool.and_eq_true] at hpa
      simp only [List.zip_cons_cons, List.mem_cons] at hvp
      rcases hvp with rfl | hvp
      · exact hpa.1
      · exact pureValList_zip_fst hpa.2 vp hvp

/-- `applyDirect` over `BReady` — re-cut of `frameβ_applyDirect_evalW`. Carries
    `PureVal op_a` + `PureValList args_a` + `BReady T_b`. The closure case runs the body
    via the eval IH with `Pure body` (from `PureVal op_a`) and `BReady` at the
    arg-bound state (`BuiltinReadyAll.extends` for the gate, `allocStep_foldl_pureHeap`
    for `PureHeap`); `.builtinBaseApply` re-dispatches with `valToList_PureValList`;
    `.prim` is ground (premises unused). -/
def FrameβApplyDirectStmtWP (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (op_a op_b : Val)
    (args_a args_b : List Val) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    TowerInvβ T_a T_b →
    BReady T_b →
    PureVal op_a = true →
    PureValList args_a = true →
    ValVisβ op_a op_b T_a.heap T_b.heap →
    ListValVisβ args_a args_b T_a.heap T_b.heap →
    ValValid op_a T_a.heap → ValValid op_b T_b.heap →
    ListValValid args_a T_a.heap → ListValValid args_b T_b.heap →
    applyDirect n ptable level op_a args_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      applyDirect n ptable level op_b args_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ TowerInvβ T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap

theorem frameβ_applyDirect_evalWP (n : Nat)
    (ih_eval : FrameβEvalStmtWP n) (ih_ad : FrameβApplyDirectStmtWP n) :
    FrameβApplyDirectStmtWP (n + 1) := by
  intro ptable level op_a op_b args_a args_b T_a T_b r_a T_a'
        hresp_pt h_tower hbr hpop hpargs h_vv_op h_lvv hv_opa hv_opb hv_argsa hv_argsb heval
  have h_vv1 := h_vv_op 1
  cases op_a with
  | num _ => simp [applyDirect] at heval
  | bool _ => simp [applyDirect] at heval
  | nilV => simp [applyDirect] at heval
  | sym _ => simp [applyDirect] at heval
  | cons _ _ => simp [applyDirect] at heval
  | prim name =>
      have h_opb : op_b = .prim name := by
        cases op_b with
        | prim n' => simp only [ValVisβ_aux] at h_vv1; rw [h_vv1]
        | num _ => simp [ValVisβ_aux] at h_vv1
        | bool _ => simp [ValVisβ_aux] at h_vv1
        | nilV => simp [ValVisβ_aux] at h_vv1
        | sym _ => simp [ValVisβ_aux] at h_vv1
        | cons _ _ => simp [ValVisβ_aux] at h_vv1
        | closure _ _ _ => simp [ValVisβ_aux] at h_vv1
        | builtinBaseApply => simp [ValVisβ_aux] at h_vv1
      subst h_opb
      simp only [applyDirect] at heval
      cases hp_a : applyPrim name args_a with
      | none => rw [hp_a] at heval; simp at heval
      | some v_a' =>
          rw [hp_a] at heval
          simp only [Option.some.injEq, Prod.mk.injEq] at heval
          obtain ⟨hr, hT⟩ := heval; subst hr; subst hT
          obtain ⟨r_b, hp_b, h_vv_r, hv_ra, hv_rb⟩ :=
            applyPrim_bisimβ name args_a args_b T_a.heap T_b.heap h_lvv hv_argsa hv_argsb v_a' hp_a
          exact ⟨r_b, T_b, by simp only [applyDirect, hp_b], h_vv_r, h_tower,
                 HeapEvolutionβ.refl _ _, hv_ra, hv_rb⟩
  | builtinBaseApply =>
      have h_opb : op_b = .builtinBaseApply := by
        cases op_b with
        | builtinBaseApply => rfl
        | num _ => simp [ValVisβ_aux] at h_vv1
        | bool _ => simp [ValVisβ_aux] at h_vv1
        | nilV => simp [ValVisβ_aux] at h_vv1
        | sym _ => simp [ValVisβ_aux] at h_vv1
        | cons _ _ => simp [ValVisβ_aux] at h_vv1
        | closure _ _ _ => simp [ValVisβ_aux] at h_vv1
        | prim _ => simp [ValVisβ_aux] at h_vv1
      subst h_opb
      unfold applyDirect at heval
      match args_a, args_b, h_lvv, hv_argsa, hv_argsb, hpargs with
      | [], _, _, _, _, _ => simp at heval
      | _ :: [], _, _, _, _, _ => simp at heval
      | _ :: _ :: _ :: _, _, _, _, _, _ => simp at heval
      | [_aO_a, _ol_a], [], h_lvv', _, _, _ => exact h_lvv'.elim
      | [_aO_a, _ol_a], [_], h_lvv', _, _, _ => exact h_lvv'.2.elim
      | [_aO_a, _ol_a], _ :: _ :: _ :: _, h_lvv', _, _, _ => exact h_lvv'.2.2.elim
      | [actualOp_a, operandsList_a], [actualOp_b, operandsList_b],
          ⟨h_vv_actual, h_vv_olist, _⟩, ⟨hv_actual_a, hv_olist_a, _⟩,
          ⟨hv_actual_b, hv_olist_b, _⟩, hpargs' =>
          simp only at heval
          simp only [PureValList, Bool.and_eq_true, and_true] at hpargs'
          cases hl_a : valToList operandsList_a with
          | none => rw [hl_a] at heval; simp at heval
          | some operands_a =>
              rw [hl_a] at heval
              simp only at heval
              obtain ⟨operands_b, hl_b, h_lvv_ops, hv_ops_a, hv_ops_b⟩ :=
                valToList_bisimβ operands_a operandsList_a operandsList_b
                  T_a.heap T_b.heap hl_a h_vv_olist hv_olist_a hv_olist_b
              have hp_ops : PureValList operands_a = true := valToList_PureValList hpargs'.2 hl_a
              obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_tower', h_he', hv_ra, hv_rb⟩ :=
                ih_ad ptable level actualOp_a actualOp_b operands_a operands_b
                  T_a T_b r_a T_a' hresp_pt h_tower hbr hpargs'.1 hp_ops h_vv_actual h_lvv_ops
                  hv_actual_a hv_actual_b hv_ops_a hv_ops_b heval
              exact ⟨r_b, T_b', by simp only [applyDirect, hl_b, h_eval_b], h_vv_r,
                     h_tower', h_he', hv_ra, hv_rb⟩
  | closure ps body cenv =>
      obtain ⟨body', cenv_b, rfl⟩ := ValVisβ_closure_inv h_vv_op
      obtain ⟨_, hβ_body, h_env_cenv⟩ := closure_ValVisβ_imp h_vv_op
      simp only [applyDirect] at heval
      by_cases hlen : ps.length = args_a.length
      · have hlen_b : ps.length = args_b.length := by rw [hlen]; exact ListValVisβ.length_eq h_lvv
        have hne_a : (ps.length != args_a.length) = false := by simp [hlen]
        rw [hne_a] at heval
        simp only [Bool.false_eq_true, ↓reduceIte] at heval
        obtain ⟨hh_a', hh_b', hev_a', hev_b', h_env_alloc, ⟨ext_a, hex_a⟩, ⟨ext_b, hex_b⟩⟩ :=
          EnvVisβ_allocStep_chain args_a args_b ps cenv cenv_b T_a.heap T_b.heap
            hlen.symm hlen_b.symm h_lvv hv_argsa hv_argsb h_tower.hv_a h_tower.hv_b
            hv_opa hv_opb h_env_cenv
        obtain ⟨hlva', hlvb', hlvisβ'⟩ :=
          level_fields_extend ext_a ext_b h_tower.hv_a h_tower.hv_b
            h_tower.valid_a h_tower.valid_b h_tower.visβ
        have h_tower_alloc : TowerInvβ
            { T_a with heap := (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 }
            { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 } :=
          { hv_a := hh_a', hv_b := hh_b', count := h_tower.count
            valid_a := by rw [hex_a]; exact hlva', valid_b := by rw [hex_b]; exact hlvb'
            visβ := by rw [hex_a, hex_b]; exact hlvisβ'
            pol_eq := h_tower.pol_eq, pol_resp := h_tower.pol_resp }
        have hpargs_b : PureValList args_b = true := ListValVisβ_pureValList h_lvv hpargs
        have hbr_alloc : BReady
            { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 } := by
          refine ⟨?_, allocStep_foldl_pureHeap (args_b.zip ps) T_b.heap cenv_b hbr.2
                    (pureValList_zip_fst hpargs_b)⟩
          rw [hex_b]; exact hbr.1.extends (StateExtends.of_heap_append T_b ext_b)
        obtain ⟨r_b, T_b', h_eval_b, h_vv_r, h_ctx_body, h_he_body, hv_ra, hv_rb⟩ :=
          ih_eval ptable level body body'
            (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).2
            (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).2
            { T_a with heap := (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 }
            { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 }
            r_a T_a' hβ_body hpop hresp_pt
            (WFCtxTβ.ofTower h_tower_alloc hev_a' hev_b' h_env_alloc) hbr_alloc heval
        have h_he_alloc : HeapEvolutionβ T_a T_b
            { T_a with heap := (args_a.zip ps |>.foldl allocStep (T_a.heap, cenv)).1 }
            { T_b with heap := (args_b.zip ps |>.foldl allocStep (T_b.heap, cenv_b)).1 } :=
          HeapEvolutionβ.from_heapExt h_tower.hv_a h_tower.hv_b ⟨ext_a, hex_a⟩ ⟨ext_b, hex_b⟩
        refine ⟨r_b, T_b', ?_, h_vv_r, h_ctx_body.toTower,
                h_he_alloc.trans h_he_body, hv_ra, hv_rb⟩
        simp only [applyDirect]
        have hne_b : (ps.length != args_b.length) = false := by simp [hlen_b]
        rw [hne_b]; simp only [Bool.false_eq_true, ↓reduceIte]; exact h_eval_b
      · have hne : (ps.length != args_a.length) = true := by simp [hlen]
        rw [hne] at heval; simp at heval

/-- `applyVia` over `BReady` — re-cut of `frameβ_applyVia_eval`. Under `BReady` the
    tower is full so `materialize (level+1)` is a no-op (`T_b_mat = T_b`), and the
    **non-standard-gate branch is vacuous** (the b-side `base-apply` cell is
    `builtinBaseApply`, contradicting it). Every live branch dispatches to the
    `applyDirect` IH, forwarding the premise (`BReady T_b_mat`, `PureVal op_a`,
    `PureValList args_a` — purity is heap-independent). -/
def FrameβApplyViaStmtWP (n : Nat) : Prop :=
  ∀ (ptable : PolicyTable) (level : Nat) (op_a op_b : Val)
    (args_a args_b : List Val) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState),
    PolicyTableRespectsBisimT ptable →
    TowerInvβ T_a T_b →
    BReady T_b →
    PureVal op_a = true →
    PureValList args_a = true →
    ValVisβ op_a op_b T_a.heap T_b.heap →
    ListValVisβ args_a args_b T_a.heap T_b.heap →
    ValValid op_a T_a.heap → ValValid op_b T_b.heap →
    ListValValid args_a T_a.heap → ListValValid args_b T_b.heap →
    applyVia n ptable level op_a args_a T_a = some (r_a, T_a') →
    ∃ r_b T_b',
      applyVia n ptable level op_b args_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ TowerInvβ T_a' T_b' ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap

theorem frameβ_applyVia_evalWP (n : Nat) (ih_ad : FrameβApplyDirectStmtWP n) :
    FrameβApplyViaStmtWP (n + 1) := by
  intro ptable level op_a op_b args_a args_b T_a T_b r_a T_a'
        hresp_pt h_tower hbr hpop hpargs h_vv_op h_lvv hv_opa hv_opb hv_argsa hv_argsb heval
  cases hm_a : T_a.materialize (level + 1) with
  | none => rw [applyVia_materialize_none n ptable level op_a args_a T_a hm_a] at heval; simp at heval
  | some T_a_mat =>
      have hm_b_some : (T_b.materialize (level + 1)).isSome := by
        cases h_some : T_b.materialize (level + 1) with
        | none => rw [(T_a.materialize_cross_side_some_iff T_b _).mpr h_some] at hm_a; cases hm_a
        | some _ => simp
      obtain ⟨T_b_mat, hm_b⟩ := Option.isSome_iff_exists.mp hm_b_some
      -- full tower ⟹ materialize is a no-op ⟹ `BReady T_b_mat`
      have hd : level + 1 < Tower.maxDepth := by
        unfold TowerState.materialize at hm_a
        split at hm_a
        · exact absurd hm_a (by simp)
        · omega
      have hTbmat : T_b_mat = T_b := by
        have hnoop := materialize_noop (show T_b.levels.length > level + 1 by have := hbr.1.1; omega) hd
        rw [hnoop] at hm_b; exact (Option.some.inj hm_b).symm
      have hbr_mat : BReady T_b_mat := hTbmat ▸ hbr
      obtain ⟨hhm_a, hhm_b, hcount_m, hvalid_a_m, hvalid_b_m, hvisβ_m⟩ :=
        materialize_MatInvβ ⟨h_tower.hv_a, h_tower.hv_b, h_tower.count, h_tower.valid_a,
          h_tower.valid_b, h_tower.visβ⟩ hm_a hm_b
      have hpoleq_m := materialize_policiesEqβ h_tower.count h_tower.pol_eq hm_a hm_b
      have hpolresp_m := materialize_policies_resp_preserves T_a T_a_mat (level + 1)
        PolicyRespectsBisimT hm_a h_tower.pol_resp rejectAllPolicy_respects_bisimT
      have h_tower_mat : TowerInvβ T_a_mat T_b_mat :=
        ⟨hhm_a, hhm_b, hcount_m, hvalid_a_m, hvalid_b_m, hvisβ_m, hpoleq_m, hpolresp_m⟩
      have h_he_mat : HeapEvolutionβ T_a T_b T_a_mat T_b_mat :=
        HeapEvolutionβ.from_heapExt h_tower.hv_a h_tower.hv_b
          (T_a.materialize_heap_extends T_a_mat (level + 1) hm_a)
          (T_b.materialize_heap_extends T_b_mat (level + 1) hm_b)
      have h_vv_op_m := h_he_mat.valVisβ_preserve op_a op_b hv_opa hv_opb h_vv_op
      have h_lvv_m := h_he_mat.listValVisβ_preserve args_a args_b hv_argsa hv_argsb h_lvv
      have hv_opa_m := ValValid.length_mono op_a hv_opa h_he_mat.len_a
      have hv_opb_m := ValValid.length_mono op_b hv_opb h_he_mat.len_b
      have hv_argsa_m := ListValValid.length_mono hv_argsa h_he_mat.len_a
      have hv_argsb_m := ListValValid.length_mono hv_argsb h_he_mat.len_b
      cases he_a : T_a_mat.envAt? (level + 1) with
      | none =>
          rw [applyVia_envAt_none n ptable level op_a args_a T_a T_a_mat hm_a he_a] at heval
          have he_b : T_b_mat.envAt? (level + 1) = none :=
            envAt?_none_cross T_a_mat T_b_mat (level + 1) hcount_m he_a
          obtain ⟨r_b, T_b', h_ad_b, h_vv_r, h_tower', h_he_ad, hv_ra, hv_rb⟩ :=
            ih_ad ptable level op_a op_b args_a args_b T_a_mat T_b_mat r_a T_a' hresp_pt
              h_tower_mat hbr_mat hpop hpargs h_vv_op_m h_lvv_m hv_opa_m hv_opb_m hv_argsa_m hv_argsb_m heval
          refine ⟨r_b, T_b', ?_, h_vv_r, h_tower', h_he_mat.trans h_he_ad, hv_ra, hv_rb⟩
          rw [applyVia_envAt_none n ptable level op_b args_b T_b T_b_mat hm_b he_b]; exact h_ad_b
      | some upEnv_a =>
          obtain ⟨upEnv_b, he_b⟩ := envAt?_some_cross T_a_mat T_b_mat (level + 1) upEnv_a hcount_m he_a
          have h_env_up : EnvVisβ upEnv_a upEnv_b T_a_mat.heap T_b_mat.heap :=
            hvisβ_m (level + 1) upEnv_a upEnv_b he_a he_b
          cases hba_a : upEnv_a.lookup "base-apply" with
          | none =>
              rw [applyVia_baseApply_none n ptable level op_a args_a T_a T_a_mat upEnv_a
                hm_a he_a hba_a] at heval
              have hba_b : upEnv_b.lookup "base-apply" = none := EnvVisβ_lookup_none h_env_up hba_a
              obtain ⟨r_b, T_b', h_ad_b, h_vv_r, h_tower', h_he_ad, hv_ra, hv_rb⟩ :=
                ih_ad ptable level op_a op_b args_a args_b T_a_mat T_b_mat r_a T_a' hresp_pt
                  h_tower_mat hbr_mat hpop hpargs h_vv_op_m h_lvv_m hv_opa_m hv_opb_m hv_argsa_m hv_argsb_m heval
              refine ⟨r_b, T_b', ?_, h_vv_r, h_tower', h_he_mat.trans h_he_ad, hv_ra, hv_rb⟩
              rw [applyVia_baseApply_none n ptable level op_b args_b T_b T_b_mat upEnv_b hm_b he_b hba_b]
              exact h_ad_b
          | some idx_a =>
              cases hcell_a : T_a_mat.heap[idx_a]? with
              | none =>
                  rw [applyVia_cell_none n ptable level op_a args_a T_a T_a_mat upEnv_a idx_a
                    hm_a he_a hba_a hcell_a] at heval; simp at heval
              | some baseApply_a =>
                  obtain ⟨idx_b, baseApply_b, hba_b, hcell_b, h_vv_cell⟩ :=
                    EnvVisβ_lookup_some h_env_up hba_a hcell_a
                  by_cases hbuiltin : baseApply_a = .builtinBaseApply
                  · subst hbuiltin
                    rw [applyVia_builtin n ptable level op_a args_a T_a T_a_mat upEnv_a idx_a
                      hm_a he_a hba_a hcell_a] at heval
                    have hbb_b : baseApply_b = .builtinBaseApply :=
                      (ValVisβ_builtinBaseApply_iff h_vv_cell).mp rfl
                    rw [hbb_b] at hcell_b
                    obtain ⟨r_b, T_b', h_ad_b, h_vv_r, h_tower', h_he_ad, hv_ra, hv_rb⟩ :=
                      ih_ad ptable level op_a op_b args_a args_b T_a_mat T_b_mat r_a T_a' hresp_pt
                        h_tower_mat hbr_mat hpop hpargs h_vv_op_m h_lvv_m hv_opa_m hv_opb_m hv_argsa_m hv_argsb_m heval
                    refine ⟨r_b, T_b', ?_, h_vv_r, h_tower', h_he_mat.trans h_he_ad, hv_ra, hv_rb⟩
                    rw [applyVia_builtin n ptable level op_b args_b T_b T_b_mat upEnv_b idx_b
                      hm_b he_b hba_b hcell_b]
                    exact h_ad_b
                  · -- non-standard gate: vacuous under `BReady` (the b-side gate is `builtinBaseApply`)
                    exfalso
                    obtain ⟨upEnv', idx', henv', hlk', hcell'⟩ := hbr_mat.1.2 level hd
                    rw [he_b, Option.some.injEq] at henv'; subst henv'
                    rw [hba_b, Option.some.injEq] at hlk'; subst hlk'
                    rw [hcell_b, Option.some.injEq] at hcell'
                    exact hbuiltin ((ValVisβ_builtinBaseApply_iff h_vv_cell).mpr hcell')

/-! ### 7p (cont.). eval's `.app` — the structural branch, premised.

The premised re-cut of `frameβ_app_structural_evalW` (§7m) onto the `…WP`
statements (`BReady`- and purity-threaded).  Where the W-version's `applyVia`
clause was unconditional, the WP `applyVia` now additionally demands the a-side
value purities `PureVal fv_a` / `PureValList avs_a`.  We recover them from the
b-side: under `BReady T_b`, `allPureIndep` gives `PureVal fv_b` / `PureValList
avs_b`, and the reverse transfers `ValVisβ_pureVal_rev` /
`ListValVisβ_pureValList_rev` (β keeps purity *both ways*) push them back to the
a-side — so the structural case carries **no** a-side heap-purity hypothesis. -/
theorem frameβ_app_structural_evalWP (n : Nat) (ptable : PolicyTable) (level : Nat)
    (args args' : List Expr) (env_a env_b : Env) (T_a T_b : TowerState)
    (r_a : Val) (T_a' : TowerState)
    (ih_eval : FrameβEvalStmtWP n) (ih_list : FrameβEvalListStmtWP n)
    (ih_via : FrameβApplyViaStmtWP n)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ_args : BetaRelList args args')
    (hpure : Pure (.app args) = true)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.app args) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level (.app args') env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  cases hβ_args with
  | nil => simp only [eval] at heval; exact absurd heval (by simp)
  | cons hβ_f hβ_rest =>
      rename_i f f' rest rest'
      simp only [Pure, PureList, Bool.and_eq_true] at hpure
      obtain ⟨hpf, hprest⟩ := hpure
      have hpf' : Pure f' = true := hβ_f.pure_preserve hpf
      have hprest' : PureList rest' = true := hβ_rest.pure_preserve hprest
      simp only [eval] at heval
      cases hf : eval n ptable level f env_a T_a with
      | none => rw [hf] at heval; simp at heval
      | some pr =>
          obtain ⟨fv_a, T_a_inner⟩ := pr
          rw [hf] at heval; simp only at heval
          obtain ⟨fv_b, T_b_inner, h_eval_f_b, h_vv_f, h_ctx1, h_he1, hv_fva, hv_fvb⟩ :=
            ih_eval ptable level f f' env_a env_b T_a T_b fv_a T_a_inner hβ_f hpf hresp_pt h_ctx hbr hf
          have hbr1 : BReady T_b_inner := hbr.closed hpf' h_eval_f_b
          cases ha : evalList n ptable level rest env_a T_a_inner with
          | none => rw [ha] at heval; simp at heval
          | some pr2 =>
              obtain ⟨avs_a, T_a_inner2⟩ := pr2
              rw [ha] at heval; simp only at heval
              obtain ⟨avs_b, T_b_inner2, h_eval_args_b, h_lvv, h_ctx2, h_he2, hv_avsa, hv_avsb⟩ :=
                ih_list ptable level rest rest' env_a env_b T_a_inner T_b_inner avs_a T_a_inner2
                  hβ_rest hprest hresp_pt h_ctx1 hbr1 ha
              have hbr2 : BReady T_b_inner2 := hbr1.closedList hprest' h_eval_args_b
              -- recover the a-side value purities from the b-side (no a-side heap premise)
              have hpfv_a : PureVal fv_a = true :=
                ValVisβ_pureVal_rev h_vv_f
                  (((allPureIndep n).1 level f' env_b T_b hpf' hbr.2).2 ptable fv_b T_b_inner h_eval_f_b).1
              have hpavs_a : PureValList avs_a = true :=
                ListValVisβ_pureValList_rev h_lvv
                  (((allPureIndep n).2.1 level rest' env_b T_b_inner hprest' hbr1.2).2
                    ptable avs_b T_b_inner2 h_eval_args_b).1
              -- lift the head value (ValVisβ + ValValid) across the args evolution
              have h_vv_f' : ValVisβ fv_a fv_b T_a_inner2.heap T_b_inner2.heap :=
                h_he2.valVisβ_preserve fv_a fv_b hv_fva hv_fvb h_vv_f
              have hv_fva2 : ValValid fv_a T_a_inner2.heap :=
                ValValid.length_mono fv_a hv_fva h_he2.len_a
              have hv_fvb2 : ValValid fv_b T_b_inner2.heap :=
                ValValid.length_mono fv_b hv_fvb h_he2.len_b
              -- apply via the gated `applyVia` clause (§7p, now `BReady`-premised)
              obtain ⟨r_b, T_b', h_eval_av_b, h_vv, h_tower3, h_he3, hv_ra, hv_rb⟩ :=
                ih_via ptable level fv_a fv_b avs_a avs_b T_a_inner2 T_b_inner2 r_a T_a'
                  hresp_pt h_ctx2.toTower hbr2 hpfv_a hpavs_a h_vv_f' h_lvv hv_fva2 hv_fvb2
                  hv_avsa hv_avsb heval
              have h_he_chain : HeapEvolutionβ T_a T_b T_a' T_b' :=
                h_he1.trans (h_he2.trans h_he3)
              refine ⟨r_b, T_b', ?_, h_vv, ?_, h_he_chain, hv_ra, hv_rb⟩
              · simp only [eval, h_eval_f_b, h_eval_args_b]; exact h_eval_av_b
              · exact WFCtxTβ.ofTower h_tower3
                  (EnvValid.length_mono h_ctx.ev_a h_he_chain.len_a)
                  (EnvValid.length_mono h_ctx.ev_b h_he_chain.len_b)
                  (h_he_chain.envVisβ_preserve env_a env_b h_ctx.ev_a h_ctx.ev_b h_ctx.env_visβ)

/-! ### 7p (cont.). eval's `.app` — the root-contraction branch, premised.

The premised re-cut of `frameβ_app_root_evalW` (§7m): the recognized standard-gate
premise (`h_depth`/`h_mat0`/`h_builtin0`/`h_heap`/`h_pure_op`) is now **derived**
from `BReady T_b` plus the redex *firing*.  The structural lemma maps the a-side
`.app args` to the *reduced* b-side redex `.app [λx.body', v']`; that redex's
convergence forces `level + 1 < maxDepth` (`app_lam_redex_depth` — the apply routes
through the level+1 gate), whence `BReady`'s all-levels gate supplies the
materialized-depth and builtin `base-apply` facts, and `Pure (.app args)` supplies
the pure operand.  `gate_redex_to_letE_anyfuel` then closes redex ≡ contractum. -/
theorem frameβ_app_root_evalWP (n : Nat) (ptable : PolicyTable) (level : Nat)
    (args : List Expr) (x : String) (body v exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (ih_eval : FrameβEvalStmtWP n) (ih_list : FrameβEvalListStmtWP n)
    (ih_via : FrameβApplyViaStmtWP n)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (h1 : BetaRel (.app args) (.app [.lam [x] body, v]))
    (h2 : BetaRel (.letE x v body) exp_b)
    (hpure : Pure (.app args) = true)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.app args) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  obtain ⟨f, a, rfl, hf, ha⟩ := h1.app_to_redex_inv
  obtain ⟨v', body', rfl, hv', hbody'⟩ := h2.letE_inv
  have hbrl : BetaRelList [f, a] [.lam [x] body', v'] :=
    .cons (hf.trans (BetaRel.congr hbody' (.lam [x] .hole))) (.cons (ha.trans hv') .nil)
  obtain ⟨r_b, T_b', h_redex_b, h_vv, h_ctx', h_he, hv_ra, hv_rb⟩ :=
    frameβ_app_structural_evalWP n ptable level [f, a] [.lam [x] body', v']
      env_a env_b T_a T_b r_a T_a' ih_eval ih_list ih_via hresp_pt hbrl hpure h_ctx hbr heval
  -- the gate facts, derived from `BReady` + the redex firing
  have h_depth : level + 1 < Tower.maxDepth := app_lam_redex_depth h_redex_b
  have h_pa : Pure a = true := by
    simp only [Pure, PureList, Bool.and_eq_true, Bool.and_true] at hpure; exact hpure.2
  have h_pure_v' : Pure v' = true := (ha.trans hv').pure_preserve h_pa
  refine ⟨r_b, T_b', ?_, h_vv, h_ctx', h_he, hv_ra, hv_rb⟩
  exact gate_redex_to_letE_anyfuel (n + 1) ptable level x body' v' env_b T_b
    h_depth (by have := hbr.1.1; omega) (hbr.1.2 level h_depth) h_pure_v' hbr.2
    r_b T_b' h_redex_b

/-- §7p (cont.). eval's `.app` case, dispatched. `BetaRel.app_inv` splits a
    `BetaRel (.app args) exp_b` into the **structural** branch (`exp_b = .app args'`,
    handled by `frameβ_app_structural_evalWP`) and the **root** branch (β fires,
    handled by `frameβ_app_root_evalWP`).  This is the last eval case needed for the
    mutual `FrameβEvalStmtWP` clause. -/
theorem frameβ_app_evalWP (n : Nat) (ptable : PolicyTable) (level : Nat)
    (args : List Expr) (exp_b : Expr)
    (env_a env_b : Env) (T_a T_b : TowerState) (r_a : Val) (T_a' : TowerState)
    (ih_eval : FrameβEvalStmtWP n) (ih_list : FrameβEvalListStmtWP n)
    (ih_via : FrameβApplyViaStmtWP n)
    (hresp_pt : PolicyTableRespectsBisimT ptable)
    (hβ : BetaRel (.app args) exp_b)
    (hpure : Pure (.app args) = true)
    (h_ctx : WFCtxTβ env_a env_b T_a T_b level)
    (hbr : BReady T_b)
    (heval : eval (n + 1) ptable level (.app args) env_a T_a = some (r_a, T_a')) :
    ∃ r_b T_b',
      eval (n + 1) ptable level exp_b env_b T_b = some (r_b, T_b') ∧
      ValVisβ r_a r_b T_a'.heap T_b'.heap ∧ WFCtxTβ env_a env_b T_a' T_b' level ∧
      HeapEvolutionβ T_a T_b T_a' T_b' ∧ ValValid r_a T_a'.heap ∧ ValValid r_b T_b'.heap := by
  rcases hβ.app_inv with ⟨args', rfl, hbrl⟩ | ⟨x, body, v, h1, h2⟩
  · exact frameβ_app_structural_evalWP n ptable level args args' env_a env_b T_a T_b r_a T_a'
      ih_eval ih_list ih_via hresp_pt hbrl hpure h_ctx hbr heval
  · exact frameβ_app_root_evalWP n ptable level args x body v exp_b env_a env_b T_a T_b r_a T_a'
      ih_eval ih_list ih_via hresp_pt h1 h2 hpure h_ctx hbr heval

end LeanBlack






