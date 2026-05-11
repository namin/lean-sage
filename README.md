# lean-sage

A synthesis of [`lean-grey`](../lean-grey/) (abstract infinite tower with
proved governance coherence) and [`lean-green`](../lean-green/) (Black-faithful
heap+closure+`set!` interpreter with CakeML-style value bisimulation).

**Status: 0 sorries** (in active code). ~14.1k LOC of library
(8 files in `LeanBlack/`) + ~828 LOC of demo executables. Smoke 8/8
passing. Demos 29/29 passing across 12 scenes. `proofBasedSmoke` 4/4
passing across 2 scenes. All headline theorems proved.

## What this is

A **tower-indexed reflective interpreter** for a Black-style language:
nested `(em (em ...))` programs, real `set! base-apply` cells reaching
through arbitrarily many materialized levels, single global heap, per-level
envs and policies. The cross-level reflection cascade — modifying level N+k's
apply rule from level N — is fully formalized with mechanized soundness
proofs.

## Headline theorems (all proved)

| Theorem | What it says |
|---|---|
| `eval_tower_safe` (Soundness.lean) | `eval` preserves `TowerCE` and `SafeEvolution` jointly. The 4-way mutual induction over `eval`/`evalList`/`applyVia`/`applyDirect`. The synthesis of lean-grey's tower-conservativeness with lean-green's CE-soundness. |
| `frame_tower` (Frame.lean) | Cross-side framing: bisim-related inputs ⇒ bisim-related outputs across `eval`/`evalList`/`applyVia`/`applyDirect`, threading the `WFCtxT` 13-field invariant. Tower-aware port of lean-green's `frame`. |
| `applyDirect_heap_extend_weak` (Frame.lean) | Prefix-extension: `applyDirect` succeeds with a `ValVis_weak`-related result on the prefix-extended state. Discharged via `shift_respect`. |
| `shift_respect` (Frame.lean) | `eval`/`evalList`/`applyVia`/`applyDirect` all commute with `shift_state`. ~750 LOC of case analysis × 4 mutual clauses. The technical engine for `applyDirect_heap_extend_weak`. |
| `materialize_shift_commutes` (Bisim.lean) | `(shift_state T).materialize n = (T.materialize n).map shift_state`. The lemma that lets `.em` and `applyVia` commute with shift in `shift_respect`. |
| `multnExact_soundForCE_first_install_tower` (Policies.lean) | Tower-aware port of lean-green's headline: a `multnExactPolicy`-admitted modification at first install conservatively extends `builtinBaseApply` for `CE_weak`. Combines numerical case (vacuous) and non-numerical case (substantive trace + framing). |
| `safeEvolution_necessary` (Soundness.lean) | Counterexample: without per-level policy soundness, `eval` can produce a `T'` that doesn't conservatively extend `T`. Concrete witness via a diverging-closure bad-mod. |

## Cross-level reflection in action

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

```
$ lake exe demos
Demo 1: Doubling wrapper (every num result × 2)
Demo 2: Identity wrapper (transparency check)
Demo 3: Tripler (multn variant)
Demo 4: Compose multn THEN doubling   ⇒ (2 3 4)=48, (+ 1 2)=6
Demo 5: Compose doubling THEN multn   ⇒ (2 3 4)=24, (+ 1 2)=6
Demo 6: Three-level meta-meta (install at L2, observe at L1)
Demo 7: Constant wrapper (everything ⇒ 42)
Demo 8: Inspection wrappers (apply returns op, or args, not result)
        ⇒ `(+ 1 2)` returns prim(+); `(car (+ 7 11 13))` returns num(7).
Demo 9: Self-modifying wrapper (1st call orig; future calls swap to const 999)
        Wrapper body does `(em (set! base-apply ...))` to overwrite itself.
Demo 10: Lazy multn (auto-installs proper multn after first num op)
        Adaptive meta-programming: behavior shifts based on runtime usage.
Demo 11: Three-level governance (L2 reject default protects L1)
        `(em (em (set! base-apply X)))` refused under L2's default rejectAll.
Demo 12: Selective fail (num-only wrapper kills non-num applications)
```

All 29 sub-tests pass. Each demo highlights a different reflective capability:

**Scene 3** is the headline new capability: `multn` is installed at level 2
(via `(em (em ...))` from level 0), making level 1's `applyVia` route through
the wrapper. The cross-level cascade — a level-2 `set!` reshaping how level 1
dispatches — is what lean-green's stage-1 `metaEnv-of-meta-is-self`
simplification couldn't express.

**Demo 4 vs Demo 5** — multiple installs **compose**: each new install's
`orig` captures the prior `base-apply`, so the order of installs determines
the dispatch chain.

**Demo 8** — apply is **first-class**: a wrapper can return the operator or
the arg list instead of computing a result. Useful as a `quote`-like
inspection of dispatched calls.

**Demo 9** — **self-modifying code at the apply-rule level**: the wrapper's
body does `(em (set! base-apply ...))`, replacing itself. The first call uses
the captured `orig`; subsequent calls go through the new wrapper. This is
only expressible because closures' bodies can reach back into meta-mutation.

**Demo 10** — **adaptive meta-programming**: a wrapper that detects a
condition (here: numeric op) and, on first match, installs a more
specialized wrapper. Subsequent calls go through the specialized one. Like
JIT specialization but at the apply-rule level.

**Demo 11** — **defense-in-depth from the safe default**: `materializeStep`
defaults newly-materialized levels to `rejectAllPolicy`. Even if the user
admits level-1 mutations, level-2 mutations are still refused unless
explicitly accepted. Demonstrated by an attempted level-2 install of a
constant-666 wrapper that's blocked by the default.

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

## Files

| File | LOC | Notes |
|---|---|---|
| `Black.lean` | 452 | Val/Expr/Env, Heap ops, primitives, MutationCtx, BlackPolicy. Includes `val_beq_eq`, `expr_beq_eq`, `env_beq_eq`, `valToList_listToVal`. |
| `Tower.lean` | 839 | LevelState, TowerState, materialization, accessors, `RunState := TowerState` shim. `primPairs` is `@[irreducible]`. All Tower lemmas proved: `setPolicyAt`/`updateHeap`/`alloc`/`materialize` preservation; `materialize_envAt?_preserves`; `materialize_heap_grows`; `materialize_heap_extends`; `materialize_cross_side_*`; `freshLevelEnv_*`; `buildBindings_*` foldl helpers. |
| `Eval.lean` | 226 | Tower-indexed `eval`/`evalList`/`applyVia`/`applyDirect`. |
| `Bisim.lean` | 4505 | Depth-indexed `ValVis`/`EnvVis` + weak variants, `ValValid`/`EnvValid`/`HeapValid`, heap-extension/in-place-update preservation, `HeapEvolution`, `ListValVis`/`ListValValid`, `bool_false_iff` characterizations, `applyPrim` bisim, alloc-chain bisim, `bisim_imp_eq`, `ValVis_trans`, `AllBelow`/`Deep` predicates. **Shift apparatus**: `shift_idx`/`shift_val`/`shift_env`/`shift_listVal`/`shift_heap`/`shift_state` (tower-aware), injectivity, identity-on-AllBelow, lookup/getElem? commutativity, `shift_heap_update`/`shift_heap_append`/`shift_heap_id_of_deep`, `valVis_weak_self_shift`, `PolicyRespectsShift`/`PolicyTableRespectsShift`, `shift_applyPrim`, `Tower-shift commutativity` (`shift_state_envAt?`/`policyAt?`/`setPolicyAt`/`updateHeap`/`alloc`), `allocStep_foldl_shift`, `buildBindings_foldl_shift`, `freshLevelEnv_heap_shift`/`env_shift`, `materializeStep_shift_commutes`/`iter_shift_commutes`/`materialize_shift_commutes`. |
| `Frame.lean` | 4948 | `PolicyRespectsBisimT`, `PolicyTableRespectsBisimT`. Single-side materialize preservation lemmas. Tower-aware `WFCtxT` (13 fields), `TowerCross` (12 fields), `FrameStmtT`, `frame_tower` (the framing theorem, all 4 mutual clauses, all 13 expression cases proved). `all_preserves_envAt` (mutual conjunction). `heap_mono` (4-way mutual induction over fuel). `policy_shift_preserved` (4-way mutual). `shift_respect` (the 4-way commutativity proof). `applyDirect_heap_extend_weak` (prefix-extension, derived via `shift_respect` + `frame_tower` self-bisim). |
| `Soundness.lean` | 1990 | `TowerCE`, `SafeEvolution`. `TowerCE` helpers (`refl`/`trans`/`of_heap_eq`/`of_heap_extends`/`lift_source`/`weaken_h_ref`). `Expr.IsAtomic` and `eval_atomic_T_unchanged`. `HeapValid_alloc_one`, `EnvValid_cons_alloc`, self-invariant preservation lemmas. `safeEvolution_necessary` (concrete counterexample). `all_tower_safe` (the 4-way mutual safety theorem). `eval_tower_safe` (wrapper). |
| `Policies.lean` | 611 | Tower-aware `callAsBaseApply`, per-level `CE`/`CE_weak`, `BlackPolicy.SoundForCE`/`_weak`, `numGuardPolicy`/`multnExactPolicy` definitions + shape lemmas, `verifiedTable`. `OrigBoundIn`/`NumQBoundIn`/`InstallFacts`/`RuntimeWF` (tower-aware install-protocol structures). `multnExactPolicy_implies_InstallFacts` (bridge lemma). `multn_closure_body_unfolds` (closure-body trace). `multnExact_CE_num_case_vacuous` (vacuous numerical case). `multnExact_CE_nonnum_case` (substantive non-numerical case via `applyDirect_heap_extend_weak`). `multnExact_soundForCE_first_install_tower` (the headline). |
| `ProofBased.lean` | 586 | Proof-based admission. `DecidableEq` for Val/Expr/Env (mutual `*_beq_self` + instance derivation from existing `*_beq_eq`). `CE_weak_strong` predicate + `CE_weak_to_strong` weakening + `BlackPolicy.SoundForCE_weak_strong` abbrev. `ApprovedModification` structure (proof field is `CE_weak_strong`-typed). `approvedPolicy` runtime gate. `structural_policy_yields_approval` (bridge from `SoundForCE_weak` to the new predicate). `CE_weak_strong_heap_mono`, `approvedPolicy_soundForCE_weak_strong` (headline soundness). `CE_weak_num_identity` + `numIdentityApproval` (vacuous identity). `callAsBaseApply_preserves` + `CE_weak_refl` + `identityApproval` (closure-identity). `ObsEquivConverges` + `wand_defeated_existential` (W1, the existential equational-theory defeat, proved sorry-free via `native_decide`). |
| `Smoke.lean` | 176 | 4 scenes, 8 tests. |
| `Demos.lean` | 508 | 12 demos, 29 tests. Doubling, identity, tripler, install-composition (multn-then-double, double-then-multn), three-level meta-meta, constant wrapper, inspection (return op/args), self-modifying wrapper, lazy multn (adaptive), three-level governance, selective fail. |
| `ProofBasedSmoke.lean` | 144 | 2 scenes, 4 tests. Integration of `approvedPolicy` with the tower runtime: admit (identity mod) + refuse (non-matching mod), both checking arithmetic preservation afterward. |
| `DESIGN.md` | — | Architectural rationale (the structural-policy half), decisions, scope. |
| `DESIGN_PROOF.md` | — | Proof-based admission design + status. |
| `TUTORIAL.md` | — | Hands-on walkthrough of proof-based admission. |

## Build

```bash
lake build               # library + all three executables
lake exe smoke           # 4 scenes, 8 tests
lake exe demos           # 12 scenes, 29 tests
lake exe proofBasedSmoke # 2 scenes, 4 tests
```

Pinned to `leanprover/lean4:v4.20.0` via `lean-toolchain` (matches lean-green).

```bash
$ grep -c "sorry$" LeanBlack/*.lean
LeanBlack/Bisim.lean:0
LeanBlack/Black.lean:0
LeanBlack/Eval.lean:0
LeanBlack/Frame.lean:0
LeanBlack/Policies.lean:0
LeanBlack/ProofBased.lean:0
LeanBlack/Soundness.lean:0
LeanBlack/Tower.lean:0
```

## What you can do with it

The reflective rewiring of `base-apply` lets you:

- **Redefine function application** at any level, with the redefinition
  taking effect at all lower levels (or specific levels via `(em ...)` chains).
  See `multn` (Smoke Scene 2), `doublingWrapper` (Demos 1), `triplerWrapper`
  (Demos 3).
- **Compose modifications**: each new install captures the prior `base-apply`
  as `orig`. Demos 4-5 show that order matters; the dispatch chain reflects
  the install order.
- **Reach across multiple levels**: an `(em (em ...))` from level 0 affects
  level 1's apply rule via level 2's `base-apply`. Smoke Scene 3 and
  Demos 6.
- **Govern the modifications**: `BlackPolicy` gates `set!` on meta-env cells.
  `multnExactPolicy` admits exactly the multn shape with the correct install
  protocol; `rejectAllPolicy` (the safe default for newly-materialized levels)
  refuses everything. Smoke Scene 4 demonstrates the contrast.
- **Prove your modifications safe**: the `multnExact_soundForCE_first_install_tower`
  headline certifies that any `multnExactPolicy`-admitted modification at
  first install conservatively extends `builtinBaseApply` for CE_weak
  (non-num operators behave identically; num operators get the multn fold).

See [`DESIGN.md`](DESIGN.md) for the full architectural rationale.

## Proof-based admission

A second admission path alongside the structural-policy world above:
extend `.set` admission from "Boolean policy decides on structural
shape" to "Lean term proves per-modification soundness." An
`ApprovedModification` bundles `(level, heap, oldVal, newVal)` with a
`CE_weak_strong` proof; the kernel type-checks the proof at
construction time. The runtime gate `approvedPolicy` is just a
`BlackPolicy` — it slots into a `PolicyTable` and gets installed at a
level via `(installPolicy n)` exactly like any other policy.

Headline addition: `wand_defeated_existential` — the existential
equational-theory defeat. β-equivalent terms remain observationally
equivalent even with proof-based admissions in scope. Proved
sorry-free via `native_decide` on a baseline policy table.

```bash
lake exe proofBasedSmoke   # 4/4 — integration scenes
```

See [`DESIGN_PROOF.md`](DESIGN_PROOF.md) for the design and
[`TUTORIAL.md`](TUTORIAL.md) for a hands-on walkthrough.
