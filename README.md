# lean-sage

A reflective tower of interpreters in Lean 4 where modifications to
the `base-apply` rule carry kernel-checked proofs of conservative
extension (`CE_weak_strong`). Black-faithful (heap + closure +
`set!`), with CakeML-style value bisimulation (Kumar 2016 §3)
underwriting the soundness arguments. Toolchain:
`leanprover/lean4:v4.20.0`. All public theorems are kernel-checked
with no `sorry`, `admit`, or `axiom`.

lean-sage is the Lean artifact for the
[reasonable-reflection](https://github.com/namin/reasonable-reflection)
abstract.

## Quickstart

```bash
lake build                # library + three executables
lake exe smoke            # 4 scenes, 8 tests   — structural-policy
lake exe demos            # 12 scenes, 29 tests — reflection capabilities
lake exe proofBasedSmoke  # 10 scenes, 27 tests — proof-based admission
```

Success criterion:

- `lake build` succeeds.
- Each executable prints only `OK` lines (no line starting with `XX`).
- No uncommented `sorry`, `admit`, or `axiom` in `LeanBlack/`,
  `Smoke.lean`, `Demos.lean`, or `ProofBasedSmoke.lean`.
  The current CI check is `! grep -rn "sorry$" LeanBlack/`.

## What to inspect if you have 10 minutes

1. [`LeanBlack/Public.lean`](LeanBlack/Public.lean) — the public API
   surface; one screen, tables of the six headline theorems and the
   exported types / constructors.
2. [`LeanBlack/ProofBased.lean`](LeanBlack/ProofBased.lean) —
   `CE_weak_strong`, `ApprovedModification`, `approvedPolicy`,
   `approvedPolicy_soundForCE_weak_strong`, `multnApproval`,
   `wand_defeated_existential_gated_beta`.
3. [`LeanBlack/Soundness.lean`](LeanBlack/Soundness.lean) —
   `eval_tower_safe` (multi-level CE preservation through reflective
   programs) and `safeEvolution_necessary` (the without-the-gate
   counterexample).
4. [`LeanBlack/Compose.lean`](LeanBlack/Compose.lean) —
   `CE_weak_strong_trans` (the global guarantee across composed
   admissions).
5. [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) — 10 scenes
   exercising the gate end-to-end, including Scene 4 (a doubling
   wrapper that fails to admit) and Scene 10 (the composed chain
   `bbApply → multn → identity-delegate-on-multn`).

For a hands-on walkthrough that builds approvals from scratch, see
[`TUTORIAL.md`](TUTORIAL.md). For the architectural rationale,
[`DESIGN.md`](DESIGN.md) and [`DESIGN_PROOF.md`](DESIGN_PROOF.md).
For exact scope (what is and is not claimed), [`SCOPE.md`](SCOPE.md).

## Artifact claim map

| Paper-level claim | Files / theorems / demos |
|---|---|
| Proof-carrying admission of `set! base-apply` | `ApprovedModification`, `approvedPolicy`, `approvedPolicy_soundForCE_weak_strong`, `multnApproval` (all in `LeanBlack/ProofBased.lean`) |
| multn as worked example | `multnExact_soundForCE_first_install_tower` (`LeanBlack/Policies.lean`), `multnApproval`, `ProofBasedSmoke` Scenes 3, 8, 9 |
| Bad wrapper refused at the gate | `ProofBasedSmoke` Scene 4 (doubling wrapper refused), and `safeEvolution_necessary` (`LeanBlack/Soundness.lean`) as the ungated counterexample |
| CE preservation under reflective programs | `eval_tower_safe` (`LeanBlack/Soundness.lean`) |
| Composition of admissions | `CE_weak_strong_trans` (`LeanBlack/Compose.lean`), `identityDelegateApproval` (`LeanBlack/IdentityDelegate.lean`), `ProofBasedSmoke` Scene 10 |
| β-equivalence under gated reflection (Wand point) | `wand_defeated_existential_gated_beta` (`LeanBlack/ProofBased.lean`) — **convergent / top-level**, not full contextual equivalence |
| Reflective depth | Multi-level `set! base-apply`: `Smoke` Scene 3, `Demos` Scenes 6 and 11, `ProofBasedSmoke` Scenes 7 and 9. Operational per-level policy via `installPolicy`: `Smoke` Scene 4, `Demos` Scene 11. |

## The six user-facing results

### 1. Substrate stays CE-coherent under any program

```
eval_tower_safe   (LeanBlack/Soundness.lean)
```

For any expression — including reflective ones using `(em ...)` and
`(set! base-apply ...)` at any depth — evaluation against a substrate
satisfying the `SafeEvolution` invariant produces a substrate that
still satisfies it, and the two are related by `TowerCE`. The gate's
per-modification check propagates through any depth of reflection.

### 2. multn conservatively extends the baseline

```
multnExact_soundForCE_first_install_tower   (LeanBlack/Policies.lean)
multnApproval                                (LeanBlack/ProofBased.lean)
```

The kernel-checked approval certifies that installing the multn
wrapper at level 1 preserves baseline behavior on non-numeric
operators and extends it on numeric ones: `(+ 1 2) ⇒ 3` survives,
`(2 3 4) ⇒ 24` is the strict extension. The wrapper's `orig`
fall-through is what makes the CE proof go through, and the bridge
lemma `multnExactPolicy_implies_InstallFacts` lifts the runtime
admission to the propositional facts the soundness theorem needs.

### 3. Without the gate, CE fails

```
safeEvolution_necessary   (LeanBlack/Soundness.lean)
```

Concrete counterexample. Under `acceptAll`, a malicious "constant-zero"
modification breaks `(+ 1 2)`. The gate is genuinely load-bearing —
this is the converse of Theorem 1.

### 4. β-equivalence survives gated reflection (Wand defeat — convergent)

```
wand_defeated_existential_gated_beta   (LeanBlack/ProofBased.lean)
```

`((λx. x) 0)` and `0` evaluate to the same value under
`[approvedPolicy approvals]` for any list of approvals. The β-redex
and its contractum are observationally equivalent **at the top level**
with proof-bearing admissions in scope. Reflection doesn't collapse
equational reasoning the way it does ungated (per Wand 1998). The
full contextual lift is in progress; see "Honest scope" below.

Bridged via `AllPureIndep` (also sorry-free): `eval` is
policy-table-independent for `Pure` expressions.

### 5. Proof-based admission slots into the runtime

```
approvedPolicy_soundForCE_weak_strong   (LeanBlack/ProofBased.lean)
```

`approvedPolicy approvals` is a `BlackPolicy` — the runtime treats it
identically to any other policy. From the outside, a `.set` admitted
under it is no different from one admitted by `multnExactPolicy`. The
difference is *construction*: an approval only exists if the kernel
type-checked its CE proof.

### 6. CE composes — global guarantee across admissions

```
CE_weak_strong_trans   (LeanBlack/Compose.lean)
```

The conservative-extension relation between apply values is
transitive: if `v_a → v_b` and `v_b → v_c` are each `CE_weak_strong`,
then `v_a → v_c` is `CE_weak_strong`. Combined with #5, this gives
the abstract's *global property across composed admissions*: any
chain of approved admissions at a level yields a final apply value
that is CE-related back to `bbApply`. Underlying lemma:
`ValVis_aux_weak_trans` (depth-indexed value-bisim transitivity).

## What this backs (vs. the LICS abstract)

The artifact backs the highlighted instance in the
[reasonable-reflection abstract](https://github.com/namin/reasonable-reflection):

| Dimension          | Realization                                                            |
|--------------------|------------------------------------------------------------------------|
| Substrate kind     | Reflective tower of interpreters (heap + closure + `set! base-apply`)  |
| Modification kind  | `set!` on the `base-apply` heap cell                                   |
| Evidence kind      | Kernel-checked Lean proof (`CE_weak_strong`)                           |
| Policy             | Per-modification conservative extension                                |
| Guarantee          | Substrate is always a conservative extension of the base               |
| Reflective depth   | Multi-level `(em (em (set! ...)))` modifies deeper levels (proved); `installPolicy` is operational at every level |

CakeML-style value bisimulation (Kumar 2016 §3) underwrites the CE
proofs: closures are related pointwise through their captured
environments. `LeanBlack/Bisim.lean` + `LeanBlack/Frame.lean` carry
this infrastructure.

## Honest scope

A confident summary of what is and is not claimed. See
[`SCOPE.md`](SCOPE.md) for the full version.

- **`CE_weak` / `CE_weak_strong`, not strict `CE`.** The headline CE
  conclusion uses bisim-related captured environments on closures
  (per CakeML), not Lean-equal environments. This is the relation
  the multn proof and the composition lemma `CE_weak_strong_trans`
  conclude in.
- **multn proof is first install on `bbApply`.** The structural
  theorem `multnExact_soundForCE_first_install_tower` covers
  `oldVal = .builtinBaseApply`. Composition across admissions is
  supplied separately by `CE_weak_strong_trans` together with the
  concrete second link `identityDelegateApproval`
  (`LeanBlack/IdentityDelegate.lean`). `ProofBasedSmoke` Scene 10
  exercises the full chain `bbApply → multn →
  identity-delegate-on-multn` end-to-end.
- **β result is top-level / convergent.** Full contextual β
  (`∀ context C, evalProgram (C[M]) = evalProgram (C[N])`) is
  partial / in progress. The clean half (`EasyCtx`, `WideCtx`,
  `SimpleCtx`) covers every `Expr`-tree position except `.lam`. See
  `LeanBlack/Ctx.lean`, `LeanBlack/ContextualBeta.lean`,
  `LeanBlack/HeapAgree.lean`, `LeanBlack/EvalFuelMono.lean`, and
  `TUTORIAL.md` §12.
- **No public recursive proof-based policy-installation theorem.**
  lean-sage mechanizes multi-level reflective modification of
  `base-apply` and operationally includes per-level policy
  installation via `installPolicy`. The public theorem surface does
  not currently expose a recursive proof-based theorem for
  installing new gate policies through higher gates — the headline
  theorems quantify over a fixed `verifiedTable`.

## File map

**User-facing.**

| File | Purpose |
|------|---------|
| [`Smoke.lean`](Smoke.lean) | Structural-policy smoke runner |
| [`Demos.lean`](Demos.lean) | 12 reflection capabilities (cross-level cascade, composition, adaptive wrappers) |
| [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) | Proof-based scenes incl. end-to-end multn through the kernel gate |
| [`TUTORIAL.md`](TUTORIAL.md) | Hands-on walkthrough — start here to build your first approval |
| [`DESIGN.md`](DESIGN.md) | Architectural rationale (substrate half) |
| [`DESIGN_PROOF.md`](DESIGN_PROOF.md) | Proof-based admission design |
| [`SCOPE.md`](SCOPE.md) | Precise scope of headline claims |

**Library** (dependency order; internal lemmas live here).

| File | Carries |
|------|---------|
| `LeanBlack/Black.lean` | `Val`/`Expr`/`Env`, heap, primitives, `BlackPolicy` |
| `LeanBlack/Tower.lean` | `Substrate` as `List Level`, materialization |
| `LeanBlack/Eval.lean` | Tower-indexed mutual `eval`/`evalList`/`applyVia`/`applyDirect` |
| `LeanBlack/Bisim.lean` | CakeML-style value bisimulation, shift apparatus |
| `LeanBlack/Frame.lean` | Cross-side framing — the technical engine for CE |
| `LeanBlack/Soundness.lean` | `TowerCE`, `SafeEvolution`, `eval_tower_safe` (#1) + necessity counterexample (#3) |
| `LeanBlack/Policies.lean` | Structural policies + multn soundness (#2's structural half) |
| `LeanBlack/ProofBased.lean` | `ApprovedModification`, proof-based gate, multn approval (#2's proof-bearing half), Wand defeat (#4), proof-based soundness (#5) |
| `LeanBlack/Compose.lean` | `ValVis_weak` / `CE_weak` / `CE_weak_strong` transitivity (#6) — composition across admissions |
| `LeanBlack/IdentityDelegate.lean` | `identityDelegate_CE_of_closure` + `identityDelegateApproval` — concrete second link in a CE chain |
| `LeanBlack/Public.lean` | Single-file entry point exposing the headline API |

**Contextual-β infrastructure** (in progress; supports the scope-extension of #4):

`LeanBlack/EvalFuelMono.lean`, `LeanBlack/Ctx.lean`,
`LeanBlack/ContextualBeta.lean`, `LeanBlack/HeapAgree.lean`.

For the theorem surface, start with
[`LeanBlack/Public.lean`](LeanBlack/Public.lean).

## What you can do with it

The reflective rewiring of `base-apply` lets you:

- **Redefine function application** at any level (`multn` at level 1,
  cross-level via `(em ...)`-chains).
- **Compose modifications** — each new install captures the prior
  `base-apply` as `orig`; install order determines the dispatch chain
  (Demos 4–5 demonstrate).
- **Reach across levels** — `(em (em ...))` from level 0 affects
  level 1's apply rule via level 2's `base-apply` (Smoke Scene 3,
  Demos 6).
- **Govern with proof-bearing admissions** — build an
  `ApprovedModification` whose `proof` field discharges
  `CE_weak_strong`; the kernel type-checks it, the runtime gate uses
  it like any other policy.
- **Verify the modification is safe** — the multn case is fully
  worked-through; identity, closure-identity, and structural-policy
  bridges are also available as approval templates.

See [`TUTORIAL.md`](TUTORIAL.md) for the hands-on path through these.
