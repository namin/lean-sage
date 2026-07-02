# lean-sage

A reflective tower of interpreters in Lean 4 where modifications to
the `base-apply` rule carry kernel-checked proofs of conservative
extension (`CE_weak_strong`). Black-faithful (heap + closure +
`set!`), with CakeML-style value bisimulation (Kumar 2016 §3)
underwriting the soundness arguments.
All public theorems are kernel-checked with no `sorry` or `admit`,
on the standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`) — enforced in CI by
[`LeanBlack/AxiomAudit.lean`](LeanBlack/AxiomAudit.lean). For the
claim-by-claim classification, see [`CLAIMS.md`](CLAIMS.md).

lean-sage is highlighted in
[reasonable-reflection](https://github.com/namin/reasonable-reflection).

## Quickstart

```bash
lake build                # library + axiom audit + all executables
lake exe smoke            # 4 scenes, 8 tests   — structural-policy
lake exe demos            # 12 scenes, 29 tests — reflection capabilities
lake exe proofBasedSmoke  # 11 scenes, 32 tests — proof-based admission
lake exe demoGuarded      # master theorem: two admissions + a provable refusal
lake exe demoStack        # stacking: two modifications live at once
lake exe demoSeq          # a useful admission: applicable sequences, 0/6 -> 6/6 clients
lake exe booth llm "…"    # the LLM proposal booth (needs Bedrock)
```

For the stage demo — the three beats above with a recorded fallback for
the live LLM step — run [`demo/keynote-demo.sh`](demo/keynote-demo.sh)
(`--offline` to replay the recorded run with no network, `--no-pause`
to rehearse straight through).

Success criterion:

- `lake build` succeeds. This includes
  [`LeanBlack/AxiomAudit.lean`](LeanBlack/AxiomAudit.lean), which
  pins the axiom footprint of every headline theorem with
  `#guard_msgs` — the build fails if any theorem acquires an axiom
  beyond `propext` / `Classical.choice` / `Quot.sound`. (A `sorry`
  grep alone cannot see tactic-introduced axioms such as
  `native_decide`'s.)
- Each executable prints only `OK` lines (no line starting with `XX`).
- No uncommented `sorry` or `admit` in `LeanBlack/`, `Smoke.lean`,
  `Demos.lean`, or `ProofBasedSmoke.lean`
  (`! grep -rn "sorry$" LeanBlack/`).

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

## The open proposal surface (guarded-extension family)

Beyond the single worked multn modification, there is now an *open*
family of admissible modifications with a small per-proposal cost:

- **Master theorem** — [`LeanBlack/GuardedExt.lean`](LeanBlack/GuardedExt.lean):
  `guardedExt_soundForCE_first_install_tower` proves, once, that any
  guarded-extension wrapper `(λ (op args). if (g op) ⟨behavior⟩ else
  (orig op args))` conservatively extends the baseline given a
  `GuardSpec g` — two ~20-line lemmas (the guard is total; where it
  fires, the baseline is undefined). multn is the `g := "num?"`
  instance (`multn_admits_guardedExt`). The family's interior boundary
  is provable: `no_guardSpec_primq` / `no_guardSpec_closureq` are
  kernel proofs that no certificate *can* exist for guards that would
  intercept baseline-defined applications. Design:
  [`DESIGN_MASTER_THEOREM.md`](DESIGN_MASTER_THEOREM.md). Demo:
  `lake exe demoGuarded`.
- **Stacking** — [`LeanBlack/GuardedExtStack.lean`](LeanBlack/GuardedExtStack.lean):
  `guardedExt_stack_soundForCE` admits a *second* wrapper over an
  already-installed one when the guards are disjoint
  (`GuardsDisjoint`). Demo: `lake exe demoStack` — multn (`num?`) and
  a bool-selector (`bool?`) live simultaneously, baseline preserved.
- **The proposal booth** — [`Booth.lean`](Booth.lean) (`lake exe booth
  check | llm`): an LLM (Bedrock, via
  [`LeanBlack/Bedrock.lean`](LeanBlack/Bedrock.lean)) proposes a guard,
  a behavior, and — for guards without a pre-proved `GuardSpec` — the
  proof; `lake env lean` checks it (rejecting `sorry`), with
  error-feedback retries. The proposer is entirely outside the trusted
  base. Design and trust story:
  [`DESIGN_LLM.md`](DESIGN_LLM.md).

`native_decide` is confined to the demos (admission shape-checks and
`ValDeep`), matching `Demo.lean`'s practice; every *semantic* theorem
above is kernel-only and pinned in
[`LeanBlack/AxiomAudit.lean`](LeanBlack/AxiomAudit.lean).

## Artifact claim map

| Paper-level claim | Files / theorems / demos |
|---|---|
| Proof-carrying admission of `set! base-apply` | `ApprovedModification`, `approvedPolicy`, `approvedPolicy_soundForCE_weak_strong` (`LeanBlack/ProofBased.lean`); `multnApproval` (`LeanBlack/HeapAgree.lean`, derived from the selective certificate) |
| multn as worked example | `multnExact_soundForCE_first_install_tower` (`LeanBlack/Policies.lean`), `multnApproval`, `ProofBasedSmoke` Scenes 3, 8, 9 |
| Bad wrapper refused at the gate | `ProofBasedSmoke` Scene 4 (doubling wrapper refused), and `safeEvolution_necessary` (`LeanBlack/Soundness.lean`) as the ungated counterexample |
| CE preservation under reflective programs | `eval_tower_safe` (`LeanBlack/Soundness.lean`) |
| Composition of admissions | `CE_weak_strong_trans` (`LeanBlack/Compose.lean`), `identityDelegateApproval` (`LeanBlack/IdentityDelegate.lean`), `ProofBasedSmoke` Scene 10 |
| β-equivalence under gated reflection (Wand point) | `wand_defeated_existential_gated_beta` (`LeanBlack/ProofBased.lean`) — convergent / top-level — and `contextual_beta_pure` (`LeanBlack/ContextualBetaPure.lean`) — **contextual, every `Expr` position except under `.lam`** |
| Reflective depth | Multi-level `set! base-apply`: `Smoke` Scene 3, `Demos` Scenes 6 and 11, `ProofBasedSmoke` Scenes 7 and 9. Operational per-level policy via `installPolicy`: `Smoke` Scene 4, `Demos` Scene 11. Admission-event-level chain composition across kernel-built gate swaps: `LeanBlack/GovChain.lean` (see §6a and `SCOPE.md`). |

## The seven user-facing results

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
equational reasoning the way it does ungated (per Wand 1998).

Bridged via `AllPureIndep` (also sorry-free): `eval` is
policy-table-independent for `Pure` expressions.

### 7. Contextual β — every position except under `.lam`

```
contextual_beta_pure          (LeanBlack/ContextualBetaPure.lean)
contextual_beta_at_start      (program-level, canonical start tower)
wand_beta_ctx_pure_at_start   (the Wand pair, contextually quantified)
```

For any context `C` covering every hole-bearing `Expr` position
except `.lam`'s body — including `.set` value positions, `.letE`
bodies, and `.em`-nesting to any depth within the tower bound — any
binder `x`, any body, and any *pure* operand `v_expr`:

`C[(λx. body) v_expr]` and `C[let x = v_expr in body]` have the same
convergent outcomes, at every state with depth margin, materialized
levels, builtin `base-apply` cells in the relevant window, and a
pure heap (`BuiltinReadyP (emDepth C)`). The context's pre-hole
siblings must be `Pure`; post-hole siblings are unconstrained.

`contextual_beta_at_start` anchors this at the pre-materialized
start tower `buildTower (emDepth C + 2)` (any level-0 policy, any
policy table, any env), closing the lazy-materialization gap. The
engine is `LeanBlack/PureExt.lean`: pure evaluation only *extends*
the tower state (heap appends, env preservation, level growth) — a
joint induction in the style of `AllPureIndep`.

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
then `v_a → v_c` is `CE_weak_strong` — *at a common reference heap*.
Underlying lemma: `ValVis_aux_weak_trans` (depth-indexed value-bisim
transitivity).

The common-reference-heap proviso matters: on a chain of two *real*
installs it is never satisfied, because each admission rewrites the
`base-apply` cell that the previous full-prefix snapshot pins
(`fullPrefix_certs_conflict` in `ProofBasedSmoke.lean` proves this
on the worked chain). The abstract's *global property across
composed admissions* is therefore delivered by the selective layer
in §6a, instantiated on the worked chain by
`chainCertsFire_post_chain` + `chain_CE` and exercised at runtime by
`ProofBasedSmoke` Scene 11.

#### 6a. Composition that survives real admission sequences

```
ApprovedModificationAt / approvedPolicyAt   (LeanBlack/GovChain.lean)
chain_CE                                    (n-link composition)
```

`CE_weak_strong_trans` composes two certificates *at a common
reference heap* — but every admission rewrites the `base-apply`
cell, so full-prefix certificates from two successive real
admissions can never fire at a common test state
(`fullPrefix_certs_conflict`, proved on the worked chain).
`GovChain.lean` closes this with the **selective admission layer**:
approvals whose certificates pin only the cells they read
(`CE_weak_strong_at`), which therefore survive later installs, and
`chain_CE`, which composes any number of them at per-link
snapshots. Concrete links: `multnApprovalAt` and
`identityDelegateApprovalAt`; runtime inversions for the `.set` and
`installPolicy` clauses tie admission steps to the substrate per
step.

Instantiated on the worked chain
`bbApply → multn → identity-delegate`:
`chainCertsFire_post_chain` (`ProofBasedSmoke.lean`) proves the
selective chain's firing condition at the post-chain heap and any
extension, so `chain_CE` yields the composed conservative extension
there. `ProofBasedSmoke` Scene 11 runs the contrast: the selective
gate admits both steps and refuses garbage; the full-prefix
snapshot check is broken post-install while the selective cells
survive. (Scene-level concrete side conditions use `native_decide`,
per that file's house style; the `GovChain.lean` machinery itself is
axiom-clean.)

The packaged corollary `govReach_CE` additionally quantifies over
interleavings of admissions and gate replacements. Cite it with its
assumptions: replacement-gate soundness is a hypothesis (discharged
by construction only for kernel-built `approvedPolicyAt` gates),
the chain's firing condition is a per-instance obligation, and it
is an admission-event-level statement, not a whole-program-trace
theorem — see `SCOPE.md`.

## What this backs (vs. the LICS abstract)

The artifact is the highlighted instance in
[reasonable-reflection abstract](https://github.com/namin/reasonable-reflection):

| Dimension          | Realization                                                            |
|--------------------|------------------------------------------------------------------------|
| Substrate kind     | Reflective tower of interpreters (heap + closure + `set! base-apply`)  |
| Modification kind  | `set!` on the `base-apply` heap cell                                   |
| Evidence kind      | Kernel-checked Lean proof (`CE_weak_strong`)                           |
| Policy             | Per-modification conservative extension                                |
| Guarantee          | Substrate is always a conservative extension of the base               |
| Reflective depth   | Multi-level `(em (em (set! ...)))` modifies deeper levels (proved); `installPolicy` is operational at every level (admission-event-level composition across gate swaps: §6a) |

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
- **Contextual β excludes `.lam` positions.** `contextual_beta_pure`
  covers every `Expr` position except under a binder, for pure
  operands and pure pre-hole siblings (`SCOPE.md` has the precise
  qualifiers). The `.lam` case — congruence under a closure body —
  needs an up-to-bisim equivalence (`ValVis`-style, Howe-flavored)
  rather than outcome equality, threaded through `eval` by the L4
  parallel-bisim induction. That is the one remaining piece of the
  full contextual statement.
- **No strong proof-based gate-modifies-gate theorem.** The
  "gate modifiable through the gate one level up" axis is backed
  operationally, plus admission-event-level chain composition
  (§6a). `govReach_CE` assumes each replacement gate's soundness
  (free only for kernel-built gates) and is not a
  whole-program-trace theorem: the `eval_tower_safe` induction
  threads the strict `CE` relation, which proof-bearing gates
  cannot satisfy (multn itself is the counterexample). A
  weak-relation analog of the full `all_tower_safe` induction is
  the real target and remains future work; see `SCOPE.md`.

## File map

**User-facing.**

| File | Purpose |
|------|---------|
| [`Smoke.lean`](Smoke.lean) | Structural-policy smoke runner |
| [`Demos.lean`](Demos.lean) | 12 reflection capabilities (cross-level cascade, composition, adaptive wrappers) |
| [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) | Proof-based scenes incl. end-to-end multn through the kernel gate |
| [`DemoGuarded.lean`](DemoGuarded.lean) | `lake exe demoGuarded` — two admissions through the master theorem + the provable `closure?` refusal |
| [`DemoStack.lean`](DemoStack.lean) | `lake exe demoStack` — multn ⊕ bool-selector stacked through one gate |
| [`DemoSeq.lean`](DemoSeq.lean) | `lake exe demoSeq` — a useful admission (Clojure-style applicable sequences): 6 stuck clients unlocked, unmodified higher-order library gains reach, baseline certified; currying provably refused |
| [`Booth.lean`](Booth.lean) | `lake exe booth check\|llm` — the proposal booth (LLM proposer + kernel gate) |
| [`DESIGN_MASTER_THEOREM.md`](DESIGN_MASTER_THEOREM.md) | The guarded-extension family: proved-once vs per-proposal, stacking, scope |
| [`DESIGN_LLM.md`](DESIGN_LLM.md) | The proposer contract, booth pipeline, trust story |
| [`TUTORIAL.md`](TUTORIAL.md) | Hands-on walkthrough — start here to build your first approval |
| [`DESIGN.md`](DESIGN.md) | Architectural rationale (substrate half) |
| [`DESIGN_PROOF.md`](DESIGN_PROOF.md) | Proof-based admission design |
| [`SCOPE.md`](SCOPE.md) | Precise scope of headline claims |
| [`CLAIMS.md`](CLAIMS.md) | The ledger: every claim classified (kernel theorem / instantiated / demo / not mechanized) with its qualifiers |
| [`ARCHITECTURE.md`](ARCHITECTURE.md) | The layer map; which dualities are theorem-forced and which are consolidation debt (with plan) |

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
| `LeanBlack/GuardedExt.lean` | The guarded-extension family: master theorem, `GuardSpec`, per-guard instances, the `prim?`/`closure?` impossibility results, multn subsumption |
| `LeanBlack/GuardedExtApproval.lean` | Approval packaging for the family (selective certificate → full-prefix) |
| `LeanBlack/GuardedExtStack.lean` | Disjoint-guard second install (`GuardsDisjoint`, `guardedExt_stack_soundForCE`) + `EnvDeep`/`ValDeep` decidability |
| `LeanBlack/Bedrock.lean` | `aws bedrock-runtime` client for the LLM proposer (ported from lean-green) |
| `LeanBlack/Public.lean` | Single-file entry point exposing the headline API |

**Contextual-β layer** (carries #7; `.lam` positions remain open):

| File | Carries |
|------|---------|
| `LeanBlack/EvalFuelMono.lean` | Fuel monotonicity (joint bump across the four eval functions) |
| `LeanBlack/Ctx.lean` | Term contexts, `EvalEquiv` / `EvalEquivAt`, per-constructor congruences |
| `LeanBlack/ContextualBeta.lean` | β base-case witness (`beta_letE_conv_equiv`), CE→β bridges, `BuiltinReady` |
| `LeanBlack/HeapAgree.lean` | Selective-prefix CE (`CE_weak_strong_at`), post-admission multn certificate |
| `LeanBlack/PureExt.lean` | `StateExtends`: pure evaluation only extends the state (the preservation engine) |
| `LeanBlack/CtxPure.lean` | THE master congruence `Ctx.plug_cong_master` (sibling-class- and predicate-family-parameterized) + tier instantiations (`Ctx.plug_cong`, `Ctx.plug_cong_at_easy`) |
| `LeanBlack/ContextualBetaPure.lean` | #7: `contextual_beta_pure`, `buildTower` readiness, start-state corollaries |

**Chain-composition layer** (supports #6, see §6a):

| File | Carries |
|------|---------|
| `LeanBlack/GovChain.lean` | Selective admission (`ApprovedModificationAt` / `approvedPolicyAt`), chain composition (`chain_CE`), runtime inversions for `.set` / `installPolicy`, concrete links (`multnApprovalAt`, `identityDelegateApprovalAt`), and the packaged `GovReach` corollary (assumptions in §6a) |

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
