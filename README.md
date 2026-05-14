# lean-sage

A reflective tower of interpreters in Lean 4 where modifications to the
`base-apply` rule carry kernel-checked proofs of conservative
extension. Black-faithful (heap + closure + `set!`), with
CakeML-style value bisimulation underwriting the soundness arguments.

**All theorems sorry-free.** Lean toolchain v4.20.0.

## What has been proved

Five user-facing results.

### 1. Substrate stays CE-coherent under any program

```
eval_tower_safe   (Soundness.lean)
```

For any expression — including reflective ones using `(em ...)` and
`(set! base-apply ...)` at any depth — evaluation against a substrate
satisfying the `SafeEvolution` invariant produces a substrate that
still satisfies it, and the two are related by `TowerCE`. The gate's
per-modification check propagates through any depth of reflection.

### 2. multn conservatively extends the baseline

```
multnExact_soundForCE_first_install_tower   (Policies.lean)
multnApproval                               (ProofBased.lean)
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
safeEvolution_necessary   (Soundness.lean)
```

Concrete counterexample. Under `acceptAll`, a malicious "constant-zero"
modification breaks `(+ 1 2)`. The gate is genuinely load-bearing —
this is the converse of Theorem 1.

### 4. β-equivalence survives gated reflection (Wand defeat)

```
wand_defeated_existential_gated_beta   (ProofBased.lean)
```

`((λx. x) 0)` and `0` evaluate to the same value under
`[approvedPolicy approvals]` for any list of approvals. The β-redex
and its contractum are observationally equivalent at the top level,
**with proof-bearing admissions in scope**. Reflection doesn't
collapse equational reasoning the way it does ungated (per Wand 1998).

Bridged via `AllPureIndep` (also sorry-free): `eval` is
policy-table-independent for `Pure` expressions.

### 5. Proof-based admission slots into the runtime

```
approvedPolicy_soundForCE_weak_strong   (ProofBased.lean)
```

`approvedPolicy approvals` is a `BlackPolicy` — the runtime treats it
identically to any other policy. From the outside, a `.set` admitted
under it is no different from one admitted by `multnExactPolicy`. The
difference is *construction*: an approval only exists if the kernel
type-checked its CE proof.

## What this backs (vs. the LICS abstract)

The artifact backs the highlighted instance in the
[reasonable-reflection abstract](https://github.com/namin/reasonable-reflection):

| Dimension          | Realization                                                            |
|--------------------|------------------------------------------------------------------------|
| Substrate kind     | Reflective tower of interpreters (heap + closure + `set! base-apply`)  |
| Modification kind  | `set!` on the `base-apply` heap cell                                   |
| Evidence kind      | Kernel-checked Lean proof (`CE_weak_strong`)                           |
| Policy             | Per-modification conservative extension                                 |
| Guarantee          | Substrate is always a conservative extension of the base               |
| Reflective depth   | Multi-level: `(em (em (set! ...)))` modifies deeper levels             |

CakeML-style value bisimulation (Kumar 2016 §3) underwrites the CE
proofs: closures are related pointwise through their captured
environments. `Bisim.lean` + `Frame.lean` carry this infrastructure.

## Honest scope (what's not claimed)

- **`CE_weak`, not strict `CE`.** The headline CE conclusion is
  `_weak` — closures' captured environments aren't required to be
  Lean-equal, only bisim-related. See [`lean-green/WAND.md`](../lean-green/WAND.md)
  for the technical reason.
- **multn at first install only.** The headline theorem covers
  `oldVal = .builtinBaseApply`. The proof-based gate
  (`approvedPolicy_soundForCE_weak_strong`) supports multi-install at
  the type level — a list of approvals admits sequential `.set`s as
  long as each `(oldVal, newVal)` pair has its own CE proof — but no
  scene currently exercises a concrete multi-install chain
  (`bbApply → multn → some-other-wrapper`), since that would require
  a CE proof of `multn → some-other-wrapper` that isn't in the
  codebase. ProofBasedSmoke Scene 5 ("verified compose") demonstrates
  the related-but-distinct case: one list with multiple approvals,
  each independently admitting a different `.set`.
- **Full contextual β-equivalence is in progress.** The
  `wand_defeated_existential_gated_beta` result is *convergent*
  obs-equivalence (M and N evaluate to the same value at the top
  level). The contextual lift (`∀ context C, eval (C[M]) = eval (C[N])`)
  is covered for an `EasyCtx`/`WideCtx` sub-language of contexts
  (`Ctx.lean`), excluding `.lam`. See `TUTORIAL.md` §11.
- **No installable per-level policy is exposed at the public
  interface.** `installPolicy` exists in the substrate but lean-sage's
  headline theorems quantify over a fixed `verifiedTable`, and the
  "policy at level N is itself reflectively modifiable" axis from the
  abstract is captured only by multi-level `set!`-on-`base-apply`, not
  by recursive policy installation.

## Running it

```bash
lake build               # library + three executables
lake exe smoke           # 4 scenes, 8 tests   — structural-policy
lake exe demos           # 12 scenes, 29 tests — reflection capabilities
lake exe proofBasedSmoke # 7 scenes, 18 tests  — proof-based admission
```

Sample output (multn at level 2 via cross-level reflection):

```
$ lake exe smoke
Scene 3: two-level reflection (the new thing)
  OK  install-2up + (em (2 3 4)): expected num(24), got num(24)
  OK  install-2up + (2 3 4): expected <none>, got <none>
```

```
$ grep -c "sorry$" LeanBlack/*.lean
LeanBlack/Bisim.lean:0       LeanBlack/Black.lean:0
LeanBlack/Eval.lean:0        LeanBlack/Frame.lean:0
LeanBlack/Policies.lean:0    LeanBlack/ProofBased.lean:0
LeanBlack/Soundness.lean:0   LeanBlack/Tower.lean:0
```

## File map

**User-facing.**

| File | Purpose |
|------|---------|
| [`Smoke.lean`](Smoke.lean) | Structural-policy smoke runner |
| [`Demos.lean`](Demos.lean) | 12 reflection capabilities (cross-level cascade, composition, adaptive wrappers) |
| [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) | Proof-based scenes incl. end-to-end multn through the kernel gate |
| [`TUTORIAL.md`](TUTORIAL.md) | Hands-on walkthrough — start here to build your first approval |
| [`DESIGN.md`](DESIGN.md) | Architectural rationale (structural-policy half) |
| [`DESIGN_PROOF.md`](DESIGN_PROOF.md) | Proof-based admission design |

**Library** (dependency order; internal lemmas live here).

| File | Carries |
|------|---------|
| `LeanBlack/Black.lean` | `Val`/`Expr`/`Env`, heap, primitives, `BlackPolicy` |
| `LeanBlack/Tower.lean` | `Substrate` as `List Level`, materialization |
| `LeanBlack/Eval.lean` | Tower-indexed mutual `eval`/`evalList`/`applyVia`/`applyDirect` |
| `LeanBlack/Bisim.lean` | CakeML-style value bisimulation, shift apparatus |
| `LeanBlack/Frame.lean` | Cross-side framing — the technical engine for CE |
| `LeanBlack/Soundness.lean` | `TowerCE`, `SafeEvolution`, `eval_tower_safe` (theorem 1) + necessity counterexample (theorem 3) |
| `LeanBlack/Policies.lean` | Structural policies + multn soundness (theorem 2's structural half) |
| `LeanBlack/ProofBased.lean` | `ApprovedModification`, proof-based gate, multn approval (theorem 2's proof-bearing half), Wand defeat (theorem 4), soundness (theorem 5) |

**Contextual-β infrastructure** (in progress; supports the scope-extension of theorem 4):

`LeanBlack/EvalFuelMono.lean`, `LeanBlack/Ctx.lean`,
`LeanBlack/ContextualBeta.lean`, `LeanBlack/HeapAgree.lean`.

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
