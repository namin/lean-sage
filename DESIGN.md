# lean-black — design sketch

A synthesis of [`lean-grey`](../lean-grey/) (abstract infinite tower, governance
coherence proved) and [`lean-green`](../lean-green/) (Black-faithful
heap+closure+`set!`, value bisimulation à la CakeML). The goal is a single
formalization that is **both** infinite-and-reflective-in-its-governance **and**
operationally-faithful-to-Black.

> **Status update**: this doc was the initial sketch before any code. The
> design has been substantially realized — see the README for the current
> snapshot (~6700 LOC, runtime + ported Bisim foundation + tower-aware
> framing infrastructure with the cross-level synthesis structurally
> complete). The architectural decisions below all hold; only the per-level
> *policy storage* (lines 67-74) deviated from this draft (see correction
> in that section).

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
finitely many levels are materialized at runtime (`Tower.maxDepth = 16`
in the runtime; the soundness theorem will quantify over arbitrary
materialized prefixes).

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

lean-grey's:

```
eval_tower_conservative :
  SafeEvolution ptable tower →
  eval mods ptable fuel level exp env tower = some (v, tower') →
  TowerConservative tower tower' ∧ SafeEvolution ptable tower'
```

becomes (informally):

```
eval_tower_safe :
  SafeEvolution ptable T →
  eval fuel ptable level exp env T = some (v, T') →
  TowerVis T T' ∧ SafeEvolution ptable T'
```

where `TowerVis T T'` is the cross-level lift: for every level `n` that's
materialized in either `T` or `T'`, the apply rule at level `n` in `T'` is a
`ValVis_weak`-extension of the apply rule at level `n` in `T`. (`ValVis_weak`
because lean-green's headline theorem already concludes `_weak`, not `_`. See
`lean-green/WAND.md`.)

`SafeEvolution ptable T` lifts pointwise across the materialized levels:
every realized level's policy is universally sound, every policy in `ptable`
is universally sound. Unmaterialized levels carry the `acceptAllPolicy`
default + `builtinBaseApply` (lean-green's initial state), which is
universally sound *for the empty mutation set* — and that's what they have.

## Where lean-green's lemmas plug in

The leverage: lean-green's hardest proofs port at the **per-level**
granularity, unchanged.

**Verbatim reuse:**
- `frame.eval` / `frame.evalList` / `frame.applyVia` / `frame.applyDirect` —
  apply within a single level. The `WFCtx` invariant bundle
  (`env_eq` / `heap_len_eq` / `policy_resp`), `HeapEvolution`,
  `ValVis_aux_update` / `EnvVis_aux_update` (~250 LOC of mutual depth
  induction) — all of this is per-level and does not need to know about the
  tower.
- `multnExact_soundForCE_first_install` — gives CE soundness of one install at
  one level. Side conditions (`InstallFacts`, `RuntimeWF`, deep validity,
  shift-respect) are all per-level.
- `multnExactPolicy_implies_InstallFacts` (already `oldVal`-parametric) —
  multi-install bridge. Ports unchanged.
- `verifiedTable_respects_bisim` / `verifiedTable_respects_shift` — the
  policy invariants are level-agnostic because `BlackPolicy` is just
  `MutationCtx → Val → Val → Bool`.

**Light adaptation:**
- `MutationCtx` gains a `level : Nat` field so a policy at level N+1 sees
  level N's heap when gating mutations. (Or equivalently: `MutationCtx.heap`
  *is* the level-below's heap, by convention; the runtime puts the right
  one there.)
- `isMetaMutation x env metaEnv` generalizes to "x's idx in level-N env
  equals x's idx in level-N+1 env". Same shape, same proofs — just
  parameterized by level.

**Genuinely new:**
- The coinductive `Tower` type (or vector-of-`RunState` with a max-depth
  bound, if we want to stay first-order — see *Honest tradeoffs* below).
- `TowerVis : Tower → Tower → Prop`, the cross-level lift of `ValVis_weak`.
  Probably ~200 LOC.
- The cross-level induction in `eval_tower_safe`. The cases that change
  vs. lean-green: `.em` (level-shift), `.set` of `base-apply` (now
  affects level-below dispatch), `.installPolicy` (now per-level).
  Estimate: ~500-1000 LOC.
- Tower-level smoke tests demonstrating nested `(em (em ...))` with real
  `set!` reaching down two levels.

**Total new code estimate:** ~2-3K LOC, leveraging ~7K LOC of lean-green
machinery as-is.

## What we deliberately do NOT change

- **No new value language.** `Val` / `Expr` / `Env` / `Heap` from lean-green
  port directly. Only `eval`'s signature changes (one heap → tower of heaps).
- **No new policies.** `rejectAll` / `numGuardPolicy` / `multnExactPolicy`
  port verbatim. Their soundness theorems remain per-level; the tower-level
  theorem composes them.
- **No coinduction over per-level state.** Per-level state stays first-order
  (lean-green's exact `RunState`). Only the level structure is coinductive.
  This keeps lean-green's bisim infrastructure usable as a black box.
- **No per-level fuel separately.** One global fuel parameter, decremented
  on every recursive call regardless of level. Same simplification
  lean-green made.

## Honest tradeoffs

1. **First-order vs. coinductive Tower.** A first-order `Tower := Vector
   RunState (maxDepth + 1)` plus a "you ran out of levels" failure mode is
   simpler and lets us avoid Lean coinduction entirely. The trade is that
   `(em (em (em body)))` past `maxDepth` returns `none`, just like fuel
   exhaustion. The infinite tower is then a mathematical idealization, not
   a literal type. **Recommendation: start first-order.** Coinductive can
   come later if it earns its weight.

2. **`.set` on `base-apply` of level N from level N+1: how does the gate
   work?** lean-green freezes `s.policy` at the start of `.set` to close the
   TOCTOU `installPolicy`-mid-RHS attack (see `lean-green/GOTCHAS.md` #1).
   In the tower, the gate is **level N's policy** (the policy governing
   modifications to level N), which is stored in level N+1's heap. The
   freeze still happens — at the start of `.set`, snapshot level N's policy
   from the tower at that moment. Same lemma, lifted by one index.

3. **Level-N+1's policy when level N+1 is unmaterialized.** First time
   `(em ...)` fires at level N, the runtime materializes level N+1 with
   a fresh `RunState` (default: `acceptAllPolicy`, `metaEnv` containing
   `base-apply ↦ builtinBaseApply`). `SafeEvolution` requires this
   default to be universally sound — it is, vacuously, because no
   modifications have happened yet. The materialization step itself is a
   pure conservative extension (no rules change).

4. **The `Wand` story doesn't change.** `lean-green/Wand.lean`'s
   value-level existential defeat of Wand 1998 is per-level. The tower
   doesn't introduce new contextual equivalences worth defeating.

5. **The `Bedrock`/`Elab`/`Runner` LLM cascade ports unchanged** — it
   targets `(set! base-apply ...)` at one level. The interesting tower
   extension would be: ask Claude to propose a *meta-meta* modification
   (a closure that, when installed at level N+1, governs how level N+1
   admits modifications to level N). That's a follow-up, not part of the
   core synthesis.

## Layout proposal

```
lean-black/
├── lakefile.lean
├── lean-toolchain                — same v4.20.0
├── LeanBlack.lean                — top-level imports
├── LeanBlack/
│   ├── Black.lean                — Val, Expr, Env, Heap (verbatim from lean-green)
│   ├── Tower.lean                — NEW: Tower type, level materialization
│   ├── Eval.lean                 — eval/evalList/applyVia/applyDirect, tower-indexed
│   ├── Bisim.lean                — ValVis* (verbatim from lean-green)
│   ├── TowerBisim.lean           — NEW: TowerVis, cross-level lift
│   ├── Policies.lean             — BlackPolicy library (verbatim from lean-green)
│   └── Soundness.lean            — eval_tower_safe, the headline theorem
├── Smoke.lean                    — nested-em + set! demos
├── DESIGN.md                     — this file
└── README.md
```

## Decision points before writing code

1. **First-order `Tower` (recommended) vs. coinductive.** Locks in whether
   we need Lean's `CoInductive` machinery.
2. **`maxDepth` as runtime parameter or compile-time.** Recommend runtime,
   threaded through `eval` like fuel.
3. **Whether `MutationCtx` grows a `level` field, or whether `heap` /
   `metaEnv` are by convention "level N's" / "level N+1's".** Recommend
   the latter — fewer signature changes to lean-green's policies.
4. **Whether `(installPolicy n)` at level N affects level N's policy
   (governing mutations to level N-1) or level N+1's policy (governing
   mutations to level N).** lean-grey chose the former; lean-green has
   only one level so the question is moot. Recommend the former for
   consistency with lean-grey's `installPolicy_safe`.

If this sketch holds up under one more round of scrutiny, the next concrete
step is `Tower.lean` + the `eval`-signature change — that's the load-bearing
seam. Everything else is bookkeeping or verbatim port.
