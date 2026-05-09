# lean-black — design

A synthesis of [`lean-grey`](https://github.com/namin/lean-grey) (abstract infinite tower, governance
coherence proved) and [`lean-green`](https://github.com/namin/lean-green) (Black-faithful
heap+closure+`set!`, value bisimulation à la CakeML). The goal is a single
formalization that is **both** infinite-and-reflective-in-its-governance **and**
operationally-faithful-to-Black.

> 13,571 LOC of library + 684 LOC of demo executables, 0 sorries. Headline
> theorems proved: `eval_tower_safe`, `frame_tower`, `shift_respect`,
> `applyDirect_heap_extend_weak`, `multnExact_soundForCE_first_install_tower`,
> `safeEvolution_necessary`. Smoke 8/8 + Demos 29/29 across 12 scenes.

## What each parent gives

| | lean-grey | lean-green |
|---|---|---|
| Tower shape | `Nat → LevelState`, infinite | one level (`metaEnv` = self) |
| Apply rule | abstract `Val → List Val → Option Val` | real `base-apply` heap cell |
| Modifications | `(install n)` from `mods` table | `(set! base-apply <closure>)` |
| Governance | `(installPolicy n)` per-level, proved coherent | `(installPolicy n)` global, real |
| Soundness | `eval_tower_conservative` (full tower) | `multnExact_soundForCE_first_install` (one level, conditional) |
| Bisim | none — `ApplyRule` equality is enough | ~700 LOC `ValVis` / `WFCtx` / `HeapEvolution` |
| LOC | 643 | ~10,000 |

The asymmetry: lean-grey has the **shape**, lean-green has the **substance**.
Neither alone is the whole picture.

## The encoding: per-level envs, one global heap

> **Implementation note.** The first draft of this design proposed
> per-level heaps (each `LevelState = { heap, policy }`). When the
> runtime hit the cross-level closure invocation problem — a closure
> `set!`-ed into level N's `base-apply` from level N+1 carries a
> captured env with idxes that were valid at level N+1, but the
> closure now runs at level N — the cleaner answer turned out to be
> **one global heap, per-level envs and policies**. The "level"
> abstraction is then about which name bindings are *root* at each
> level, not about which cells are physically located there.

```
TowerState  ≡  { heap : Heap,        -- global, level-uniform allocation
                 levels : List LevelState }
LevelState  ≡  { env : Env,          -- root bindings at this level
                 policy : BlackPolicy }  -- gates set!s happening at this level
```

`(em body)` at level N: shifts to level N+1, materializing it on demand. A
fresh level allocates its own primitive cells + a fresh `base-apply ↦
builtinBaseApply` cell, all in the global heap; the level's env binds those
names to the new idxes.

Cross-level closure invocation Just Works: a closure created at level N+1
captures global-heap idxes; those stay valid no matter who dispatches it.
This avoids a cascade of "translate the captured env" complications that
per-level heaps would have forced.

The infinite-in-principle / finite-in-practice gap is preserved: only
finitely many levels are materialized at runtime (`Tower.maxDepth = 16`).
The soundness theorem quantifies over arbitrary materialized prefixes.

## The three primitives, unified

lean-grey has `(em e) | (install n) | (installPolicy n)`. lean-green has
`(em e) | (set! x e) | (installPolicy n)`. The synthesis:

- `(em body)` — level-shift, lean-green's mechanism but tower-aware
- `(set! base-apply e)` — at level N+1, mutates the cell that level N's
  `applyVia` dispatches through. Replaces lean-grey's abstract `(install n)`
  with the real Black `set!` mechanism.
- `(installPolicy n)` — at level N, replaces level N's policy.
  *(Implementation note: the policy lives directly in the per-level
  `LevelState = { env, policy }` struct, not in a heap cell. The
  initial sketch envisioned policy-as-heap-cell to make policy
  modification reflective-via-`set!`, but a direct `setPolicyAt`
  primitive turned out simpler and equivalent for the governance
  story. `(em (installPolicy n))` still governs level N+1's policy
  from level N+2 — it just does so by mutating the LevelState
  directly rather than by `set!`-ing a heap cell.)* lean-grey's
  reflective-governance story is preserved.

`(install n)` is dropped: the abstract `mods`-table indirection was a stand-in
for "real Black-source modification", and we now have the real thing.

## The headline theorem

```
eval_tower_safe :
  HeapValid T.heap →
  (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
  PolicyTableRespectsBisimT ptable →
  (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
  (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
  SafeEvolution ptable T →
  eval fuel ptable level exp env T = some (r, T') →
  TowerCE T T' ∧ SafeEvolution ptable T'
```

`TowerCE T T'` is the cross-level lift of `CE_weak`: for every level `n`
that's materialized in either `T` or `T'`, the apply rule at level `n` in
`T'` is a `CE_weak`-conservative-extension of the apply rule at level `n`
in `T`. (`CE_weak` because lean-green's `multnExact_soundForCE_first_install`
already concludes `_weak`, not `_`. See `lean-green/WAND.md`.)

`SafeEvolution ptable T` says every materialized level's policy is universally
sound and every policy in `ptable` respects bisim. Newly-materialized levels
default to `rejectAllPolicy` (vacuously `UnivSoundAt`), so `SafeEvolution`
is preserved through `.em`. The proof goes via the 4-way mutual induction
`all_tower_safe`, which jointly preserves `TowerCE` and `SafeEvolution` for
`eval`/`evalList`/`applyVia`/`applyDirect`. `eval_tower_safe` is a wrapper
projecting the `eval` clause.

## What got ported from lean-green, what got built fresh

**Ported verbatim (modulo `RunState := TowerState` shim):**
- All ~3,400 LOC of `Bisim.lean`'s pre-frame infrastructure: depth-indexed
  `ValVis_aux`/`EnvVis_aux` + weak variants, `ValValid`/`EnvValid`/`HeapValid`,
  `HeapEvolution`, `ValVis_aux_update`/`EnvVis_aux_update`, list bisim,
  `listToVal`/`valToList` bisim, alloc-chain bisim, per-prim bisim helpers,
  `bisim_imp_eq`. Verified policy library's structural shape lemmas
  (`numGuard_sound_for_shape`, `multnExact_sound_for_shape`).

**Adapted (same shape, parameterized by level):**
- `MutationCtx` gained a `level : Nat` field.
- `isMetaMutation x env T level` checks `env.lookup x = (T.envAt? level).lookup x`
  — same idea as lean-green's `isMetaMutation x env metaEnv`, lifted to the
  tower.
- `WFCtx` (3 fields) became `WFCtxT` (13 fields). New invariants:
  `policy_eq_at`, `policy_resp` (per-level instead of global), `level_envs_eq`,
  `level_envs_valid_a`/`_b`, `policies_eq`, `policies_resp_all`,
  `heap_content_bisim_at_levels`. Each new field had to be threaded through
  every construction site (`installPolicy`, `app`, `primApp`, `em` ×2, `letE`
  ×2, `closure` ×2).
- `frame` (lean-green's framing theorem) became `frame_tower`, mutual over
  `eval`/`evalList`/`applyVia`/`applyDirect` with `WFCtxT` threading.

**Genuinely new (not in lean-green):**
- `TowerState` (global heap + per-level envs/policies), `materialize`,
  `setPolicyAt`, all of `Tower.lean`.
- `TowerCE` and its transitivity machinery (`TowerCE_trans`,
  `TowerCE_of_heap_extends`, `TowerCE_lift_source`, `CE_weaken_h_ref`).
- `safeEvolution_necessary` counterexample (concrete diverging-closure
  bad-mod construction).
- The shift apparatus tower-aware: `shift_state`, `materialize_shift_commutes`
  + helpers (~300 LOC).
- `heap_mono` and `policy_shift_preserved` (4-way mutual inductions over
  fuel, tower-aware).
- `shift_respect` (the 4-way commutativity proof, ~750 LOC).
- `applyDirect_heap_extend_weak` (prefix-extension lemma, derived via
  `shift_respect`).
- `all_tower_safe` (the 4-way mutual safety theorem) and `eval_tower_safe`.

**Final tally:** 13,571 LOC of library. Of that, roughly 4–5K is verbatim or
near-verbatim port from lean-green, ~9K is tower-aware adaptation or
genuinely new.

## What we deliberately do NOT change

- **No new value language.** `Val` / `Expr` / `Env` / `Heap` from lean-green
  port directly. Only `eval`'s signature changes (one heap → tower of heaps).
- **No new policies.** `rejectAll` / `numGuardPolicy` / `multnExactPolicy`
  port verbatim. Their soundness theorems remain per-level; the tower-level
  theorem composes them.
- **No coinduction.** Both per-level state and the level list are
  first-order. Per-level state stays exactly as lean-green's `RunState` (via
  the `RunState := TowerState` shim, lean-green's bisim infrastructure ports
  unchanged). The level list is `List LevelState` capped at `Tower.maxDepth`.
- **No per-level fuel separately.** One global fuel parameter, decremented
  on every recursive call regardless of level. Same simplification
  lean-green made.

## Tradeoffs (as resolved)

1. **First-order Tower.** `Tower.maxDepth = 16` runtime cap; `(em ...)`
   past that returns `none` like fuel exhaustion. No coinduction needed.

2. **`.set` gate freezes at entry.** Same TOCTOU defense lean-green
   uses — `T.policyAt? level` is captured at the start of `.set`, so an
   `installPolicy`-mid-RHS attack can't downgrade the gate before the
   admission check.

3. **Default policy for newly-materialized levels: `rejectAllPolicy`.**
   Vacuously `UnivSoundAt` (admits nothing), so `SafeEvolution` is
   preserved through `.em` without conditions. Materialization is itself
   a pure conservative extension (no apply rules change). The smoke tests
   that need permissive levels install `acceptAllPolicy` explicitly via
   `(em (installPolicy 0))`.

4. **The Wand story doesn't change.** `lean-green/Wand.lean`'s value-level
   existential defeat of Wand 1998 is per-level. The tower introduces no
   new contextual equivalences worth defeating.

5. **The `Bedrock`/`Elab`/`Runner` LLM cascade is not (yet) ported.** It
   would target `(set! base-apply ...)` at one level. The interesting
   tower extension — a *meta-meta* modification proposed at level N+1 to
   govern how level N+1 admits level-N modifications — is a follow-up.

## Actual layout

```
lean-black/
├── lakefile.lean                 — library + smoke + demos executables
├── lean-toolchain                — leanprover/lean4:v4.20.0
├── LeanBlack.lean                — top-level imports
├── LeanBlack/
│   ├── Black.lean         (452)  — Val/Expr/Env, Heap, primitives, MutationCtx, BlackPolicy, val_beq
│   ├── Tower.lean         (839)  — TowerState, LevelState, materialize, setPolicyAt
│   ├── Eval.lean          (226)  — eval/evalList/applyVia/applyDirect, tower-indexed
│   ├── Bisim.lean        (4505)  — ValVis*, ValValid, HeapEvolution, applyPrim bisim, AllBelow/Deep, full shift apparatus, materialize-shift commutativity
│   ├── Frame.lean        (4948)  — WFCtxT (13 fields), frame_tower, all_preserves_envAt, heap_mono, policy_shift_preserved, shift_respect, applyDirect_heap_extend_weak
│   ├── Policies.lean      (611)  — callAsBaseApply, CE/CE_weak, multnExactPolicy, InstallFacts, RuntimeWF, multn_closure_body_unfolds, multnExact_soundForCE_first_install_tower
│   └── Soundness.lean    (1990)  — TowerCE, SafeEvolution, all_tower_safe, eval_tower_safe, safeEvolution_necessary
├── Smoke.lean             (176)  — 4 scenes, 8 tests (nested-em + set! demos)
├── Demos.lean             (508)  — 12 scenes, 29 tests (doubling, identity, tripler, composition, three-level meta-meta, inspection, self-modifying, lazy multn, three-level governance, selective fail)
├── DESIGN.md
└── README.md
```

`Tower` ended up first-order (`List LevelState` with `Tower.maxDepth = 16`
runtime cap). No coinduction needed; the infinite tower is mathematical
idealization, not a literal type. `(em ...)` past `maxDepth` returns `none`
just like fuel exhaustion.

`MutationCtx` gained a `level : Nat` field (one of the proposed options) so
policies see the full level context.

`(installPolicy n)` at level N replaces level N's own policy — consistent
with lean-grey's choice.

`(set! base-apply e)` at level N freezes `T.policyAt? level` at the start
of `.set` (same TOCTOU defense lean-green uses), then applies the gate to
the post-RHS tower state.
