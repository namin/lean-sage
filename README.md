# lean-black

A synthesis of [`lean-grey`](../lean-grey/) (abstract infinite tower with
proved governance coherence) and [`lean-green`](../lean-green/) (Black-faithful
heap+closure+`set!` interpreter with CakeML-style value bisimulation).

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
| `Tower.lean` | **done (~700 LOC, 0 sorries)** | LevelState, TowerState, materialization, accessors, `RunState := TowerState` shim. The primitive bindings list `primPairs` is `@[irreducible]` so proofs about `freshLevelEnv` are decoupled from its 13-element content. **All proved**: `setPolicyAt`/`updateHeap`/`alloc`/`materialize` preservation facts; `materialize_envAt?_preserves`; `materialize_heap_grows`; `materialize_cross_side_some_iff`; `materialize_cross_side_envs_eq` (parallel envs); `materialize_cross_side_policies_eq` (parallel policies); `primPairs_length`; `freshLevelEnv_heap_length`; `freshLevelEnv_env_eq`; `buildBindings_*` foldl helpers; `materializeStep_iter_*` Nat.fold inductions |
| `Eval.lean` | done | tower-indexed eval/evalList/applyVia/applyDirect |
| `Smoke.lean` | done | 8 tests across 4 scenes — all pass |
| `Bisim.lean` | partial (3057/7580 LOC) | depth-indexed bisim, validity, heap-extension, in-place-update preservation, `HeapEvolution`, list/listToVal/applyPrim bisim, alloc-chain, `bisim_imp_eq` — all ported verbatim via the `RunState := TowerState` shim |
| `Frame.lean` | partial (~1430 LOC, 6 case sorries + 4 inner) | tower-aware `WFCtxT` (13 fields), `TowerCross` (12 fields), `FrameStmtT`, `frame_tower` defined. `acceptAllPolicy_respects_bisimT` proved. 3 single-side materialize-preservation lemmas exposed (sorry'd bodies): `materialize_HeapValid_preserves`, `materialize_level_envs_valid_preserves`, `materialize_policies_resp_preserves`. **Proved**: zero (all 4); eval cases `.num`/`.bool`/`.quote`/`.var`/`.lam`/`.ifte`/`.seq`/`.app`/`.primApp`/`.letE`/`.installPolicy`; full `evalList`; applyDirect `.builtinBaseApply`/`.prim`/`.closure` (structurally complete). **`.em` structurally complete** with 4 inner sorries (env self-bisim, HeapEvolution from materialize, outer WFCtxT projection, outer EnvVis lift). **Case-level sorries**: `.set`, full `applyVia` clause, the 3 materialize-preservation lemma bodies, and `eval_preserves_envAt` body |
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

Roughly ordered by load-bearingness:

1. **Port the frame theorem** (`Bisim.lean`, lines 3059-4790 of lean-green's
   version). This is genuine engineering — the lean-green `WFCtx` and
   `FrameStmt` carry a `metaEnv` parameter that the tower model collapses
   (env at level N+1 *is* the metaEnv from level N's view) and need a new
   `level : Nat` parameter. The `.em` case is genuinely new — it shifts
   levels and recurses at the new level, where lean-green's `(em body)` was
   essentially a no-op (stage-1 metaEnv-of-meta = self). Estimate:
   ~1500-2000 LOC of port + adaptation.

2. **Port the post-frame sections** (`shift`, `Deep`, runtime invariants —
   lines 4792-7580 of lean-green's version). Once frame ports, these are
   mostly mechanical: `shift_*` / `*Deep` / `*AllBelow` are heap-only
   primitives. The `runtime_invariants_initial` lemma needs to talk about
   the lean-black `initTower`, not lean-green's `initState`.

3. **Port `Policies.lean`** verbatim. `BlackPolicy` is unchanged (modulo
   the `level` field added to `MutationCtx`). `multnExactPolicy`,
   `numGuardPolicy`, `rejectAll` and their respect-bisim / respect-shift
   theorems port directly.

4. **`Soundness.lean`**: the headline `eval_tower_safe` theorem.
   Roughly 500-1500 new LOC: the tower-level induction over `eval`'s cases,
   composing per-level lemmas via a cross-level `TowerVis` lift.

5. **Refine the `RunState` shim.** Currently `RunState := TowerState` and
   `TowerState.policy` projects level 0's policy. This is adequate for the
   ported pre-frame theorems (which only need a stable, deterministic
   policy projection for `WFCtx.policy_resp`-style invariants). The
   refinement: parameterize the cross-side `WFCtx` and `StateExt` by
   `level : Nat`, so the policy that matters is `T.policyAt? level`. This
   is part of the frame port (item 1), not a separate task.

6. **Optional: LLM cascade** (`Bedrock.lean` / `Elab.lean` / `Runner.lean`).
   Ports unchanged from lean-green for single-level demos; the interesting
   tower extension is a meta-meta proposer, but that's a separate research
   thread.

See [`DESIGN.md`](DESIGN.md) for the full architectural rationale.
