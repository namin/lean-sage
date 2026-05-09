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
| `Tower.lean` | done | LevelState, TowerState, materialization, accessors |
| `Eval.lean` | done | tower-indexed eval/evalList/applyVia/applyDirect |
| `Smoke.lean` | done | 8 tests across 4 scenes — all pass |
| `Bisim.lean` | TODO | will port lean-green's ValVis/WFCtx/HeapEvolution |
| `Policies.lean` | TODO | will port multnExactPolicy + soundness theorem |
| `Soundness.lean` | TODO | the headline `eval_tower_safe` theorem |
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

1. **Port `Bisim.lean` from lean-green** verbatim. The per-level `ValVis` /
   `WFCtx` / `HeapEvolution` / `ValVis_aux_update` / `EnvVis_aux_update`
   apparatus is level-agnostic — it operates within a single eval call and
   doesn't see the tower structure. ~7K LOC port-as-is.

2. **Port `Policies.lean`** verbatim. `BlackPolicy` is unchanged (modulo
   the `level` field added to `MutationCtx`). `multnExactPolicy`,
   `numGuardPolicy`, `rejectAll` and their respect-bisim / respect-shift
   theorems port directly. The headline
   `multnExact_soundForCE_first_install` becomes per-level (it talks about
   one install at one level).

3. **`Soundness.lean`**: the headline `eval_tower_safe` theorem.
   Roughly 500-1500 new LOC: the tower-level induction over `eval`'s cases,
   composing per-level lemmas via a cross-level `TowerVis` lift.

4. **Optional: LLM cascade** (`Bedrock.lean` / `Elab.lean` / `Runner.lean`).
   Ports unchanged from lean-green for single-level demos; the interesting
   tower extension is a meta-meta proposer, but that's a separate research
   thread.

See [`DESIGN.md`](DESIGN.md) for the full architectural rationale.
