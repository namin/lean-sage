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
  The non-recursive eval cases (`.num`/`.bool`/`.var`/`.lam`, §7g) are also done
  over `FrameβEvalStmtW`. Remaining for the eval clause: re-thread the recursive
  gate-free cases (`.letE`/`.ifte`/`.seq`, needs a `MatInvβ`-across-alloc lift)
  and the hard reflective cases `.set` (cross-side meta-mutation — `isMetaMutation`
  compares indices `EnvVisβ` does not pin; needs a β-`PolicyRespectsBisim` +
  different-index update machinery) and the gated `.app` (`applyVia`).
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

end LeanBlack

