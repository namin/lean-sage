# lean-black

A synthesis of [`lean-grey`](../lean-grey/) (abstract infinite tower with
proved governance coherence) and [`lean-green`](../lean-green/) (Black-faithful
heap+closure+`set!` interpreter with CakeML-style value bisimulation).

**Current snapshot:** 6712 LOC, 8 sorries (Tower 0, Frame 4, Policies 1, Soundness 3). Smoke 8/8. The cross-level synthesis is structurally complete: `.em` runs end-to-end through real `materialize_cross_side_*` lemmas and a fully-proved chain of materialize-preservation helpers. `all_preserves_envAt` (which `eval_preserves_envAt` wraps) is ~95% complete — only the `.set` meta-mutation sub-case remains (Lean tactic friction).

**Sorry breakdown — the 4 Frame sorries cluster around 2 architectural gaps + 2 mechanical issues:**
- **Architectural** (need cross-side heap-content-bisim invariant added to WFCtxT): `h_env_mat` in `.em`, `applyVia` clause in `frame_tower`. Both blocked on the same gap.
- **Mechanical** (Lean tactic friction): `.set` meta-mutation sub-case in `all_preserves_envAt` — joint `match T_e.heap[i]?, gate? with` resists clean cases-rw.
- **Substantial** (heaviest single case): `.set` in `frame_tower` — needs `ValVis_aux_update` machinery + policy gate semantics.

Plus 1 Policies sorry (`multnExact_soundForCE_first_install_tower` headline) and 3 Soundness sorries (`TowerCE.refl`, `eval_tower_safe`, `safeEvolution_necessary`) — all downstream of frame completion.

## What's here

This first cut is the **runtime substrate**: a tower-indexed interpreter that
runs nested `(em (em ...))` programs with real `set! base-apply` cells reaching
down through multiple levels. The bisim infrastructure and the headline
soundness theorem are deferred to follow-up rounds — they're additive on top of
the substrate, and follow lean-green's structure.

Status, by file:

| File | Status | Notes |
|---|---|---|
| `Black.lean` | done | Val/Expr/Env, Heap ops, primitives, MutationCtx, BlackPolicy |
| `Tower.lean` | **done (~755 LOC, 0 sorries)** | LevelState, TowerState, materialization, accessors, `RunState := TowerState` shim. The primitive bindings list `primPairs` is `@[irreducible]` so proofs about `freshLevelEnv` are decoupled from its 13-element content. **All proved**: `setPolicyAt`/`updateHeap`/`alloc`/`materialize` preservation facts; `materialize_envAt?_preserves`; `materialize_heap_grows`; `materialize_heap_extends` (prefix-extension, used by `.em`'s `HeapEvolution.from_heapExt`); `materialize_cross_side_some_iff`; `materialize_cross_side_envs_eq`; `materialize_cross_side_policies_eq`; `primPairs_length`; `freshLevelEnv_heap_length`; `freshLevelEnv_env_eq`; `freshLevelEnv_heap_extends`; `buildBindings_*` foldl helpers; `materializeStep_iter_*` Nat.fold inductions |
| `Eval.lean` | done | tower-indexed eval/evalList/applyVia/applyDirect |
| `Smoke.lean` | done | 8 tests across 4 scenes — all pass |
| `Bisim.lean` | partial (3057/7580 LOC) | depth-indexed bisim, validity, heap-extension, in-place-update preservation, `HeapEvolution`, list/listToVal/applyPrim bisim, alloc-chain, `bisim_imp_eq` — all ported verbatim via the `RunState := TowerState` shim |
| `Frame.lean` | partial (1880 LOC, 4 sorries) | tower-aware `WFCtxT` (13 fields), `TowerCross` (12 fields), `FrameStmtT`, `frame_tower` defined. `acceptAllPolicy_respects_bisimT` proved. **All 3 single-side materialize-preservation lemmas fully proved**: `materialize_HeapValid_preserves`, `materialize_level_envs_valid_preserves`, `materialize_policies_resp_preserves`. **`all_preserves_envAt`** (mutual conjunction theorem) — `eval_preserves_envAt` is now a wrapper projecting from it; body ~95% complete (only `.set` meta-mutation sub-case sorry'd). **`frame_tower` proved cases**: zero (all 4); eval `.num`/`.bool`/`.quote`/`.var`/`.lam`/`.ifte`/`.seq`/`.app`/`.primApp`/`.letE`/`.installPolicy`; full `evalList`; applyDirect `.builtinBaseApply`/`.prim`/`.closure`; **`.em` structurally complete** (`h_he_mat` closed via `materialize_heap_extends`). **4 remaining sorries**: `.set` meta-mutation sub-case in `all_preserves_envAt` (Lean tactic friction), `.set` in `frame_tower` (heaviest case), `h_env_mat` in `.em` (needs heap-content-bisim invariant), `applyVia` clause in `frame_tower` (same blocker as `h_env_mat`) |
| `Policies.lean` | scaffold (246 LOC, 1 sorry) | tower-aware `callAsBaseApply`, per-level `CE`/`CE_weak`, `BlackPolicy.SoundForCE`/`_weak`. Verbatim ports of `numGuardPolicy`/`multnExactPolicy` definitions + `numGuard_sound_for_shape`/`multnExact_sound_for_shape` shape lemmas. `verifiedTable`. Headline statement `multnExact_soundForCE_first_install_tower` (sorry — needs frame). The `*_respects_bisim`/`_respects_shift` theorems will port once Frame is complete |
| `Soundness.lean` | scaffold (131 LOC, 3 sorries) | the headline `eval_tower_safe` theorem statement (the synthesis of lean-grey's `eval_tower_conservative` and lean-green's `multnExact_soundForCE_first_install`) + `safeEvolution_necessary` counterexample statement + `TowerCE` cross-level CE predicate. All bodies sorry'd — discharging requires Frame + Policies completion |
| `DESIGN.md` | done | architectural rationale, decisions, scope |

## What works (smoke)

```
$ lake exe smoke
Scene 1: level 0 baseline
  OK  (+ 1 2): expected num(3), got num(3)
  OK  (2 3 4): expected <none>, got <none>

Scene 2: single-level reflection (lean-green parity)
  OK  install + (2 3 4): expected num(24), got num(24)
  OK  install + (+ 1 2): expected num(3), got num(3)

Scene 3: two-level reflection (the new thing)
  OK  install-2up + (em (2 3 4)): expected num(24), got num(24)
  OK  install-2up + (2 3 4): expected <none>, got <none>

Scene 4: governance
  OK  ungoverned bad-mod breaks +: expected num(0), got num(0)
  OK  rejectAll @ level 1 saves +: expected num(3), got num(3)
```

Scenes 1, 2, and 4 are lean-green parity (Scene 2 is exactly lean-green's
multn demo; Scene 4 is its governance demo). **Scene 3 is the new
capability** — it installs `multn` at level 2 (via `(em (em ...))` from level
0) so that level 1's `applyVia` finds the wrapper, and observes the result by
explicitly invoking application at level 1 via `(em (2 3 4))`. This is the
cross-level cascade the lean-green stage-1 metaEnv-of-meta-is-self
simplification couldn't express.

## Architecture (one paragraph)

A `TowerState` is a global heap plus a list of per-level `LevelState`s, each
holding an env and a policy. `(em body)` at level N materializes level N+1
(allocating fresh primitive cells + a fresh `base-apply` cell) and evaluates
`body` at level N+1. `(set! x e)` at level N gates via level N's policy if the
target cell is bound at the level-N root env (the architectural marker for
"meta-level mutation"). `(installPolicy n)` at level N replaces level N's
policy. `applyVia` at level N looks up `base-apply` in level (N+1)'s env and
dispatches through whatever value is there — `builtinBaseApply` (default,
recursive primitive dispatch) or a closure (the meta-level apply rule).

The single global heap is the load-bearing simplification vs. DESIGN.md's
initial sketch: it lets a closure created at level N+1 (via `set!`) be
dispatched from level N without translating its captured env idxes — those
idxes refer to the same backing store regardless of dispatch level. This is
consistent with lean-green (one heap, level-uniform allocation discipline).

## Build

```bash
lake build       # library
lake build smoke # executable
lake exe smoke   # run the 8 demos
```

Pinned to `leanprover/lean4:v4.20.0` via `lean-toolchain` (matches lean-green).

## What's next

Roughly ordered by load-bearingness, closing the 8 remaining sorries:

1. **Crack the `.set` meta-mutation Lean syntax** (~30 LOC). The joint
   `match T_e.heap[i]?, gate? with` in `all_preserves_envAt` resists
   `cases-rw`. Likely fixable via `obtain` on `Option.eq_some_iff` or a
   different destructuring tactic. Closes the inner `all_preserves_envAt`
   sorry, making `eval_preserves_envAt` fully proved.

2. **Add a 14th invariant to `WFCtxT`** (`heap_content_bisim_at_levels`)
   and propagate through 7 construction sites (~200 LOC cascade). Unlocks
   both `h_env_mat` in `.em` and the `applyVia` clause in `frame_tower` —
   they share this architectural blocker. After this cascade, only `.set`
   remains in `frame_tower`.

3. **`.set` case in `frame_tower`** (~300 LOC). The heaviest single case:
   uses `ValVis_aux_update` machinery from `Bisim.lean` + the policy gate
   semantics. This is the operational governance case.

4. **`safeEvolution_necessary`** (Soundness, ~100 LOC). Concrete
   counterexample matching Smoke Scene 4. Doesn't depend on `frame_tower`
   — independent of items 1-3.

5. **`multnExact_soundForCE_first_install_tower`** (Policies). Needs
   `frame_tower` complete (or at least `.set` + `applyVia`). Then this
   ports lean-green's headline.

6. **`eval_tower_safe`** (Soundness headline, ~500 LOC). Once Policies is
   done, this is the cross-level induction.

7. **`TowerCE.refl`** (Soundness, small). Needs an
   `applyDirect_preserves_HeapValid`-style helper.

8. **Optional: LLM cascade** (`Bedrock.lean` / `Elab.lean` / `Runner.lean`).
   Ports unchanged from lean-green for single-level demos; the interesting
   tower extension is a meta-meta proposer, but that's a separate research
   thread.

See [`DESIGN.md`](DESIGN.md) for the full architectural rationale.
