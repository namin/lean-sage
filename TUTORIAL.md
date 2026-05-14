# TUTORIAL — proof-based admission in lean-sage

A hands-on walkthrough. The goal: by the end you can construct
kernel-checked `ApprovedModification`s, install them, and read the
soundness theorems that say what your modifications guarantee.

For the *what's been proved* summary, see [`README.md`](README.md).
For architectural rationale, see [`DESIGN.md`](DESIGN.md) /
[`DESIGN_PROOF.md`](DESIGN_PROOF.md).

## What you'll be able to do by the end

1. **Construct a vacuous identity approval** — verify the kernel
   really type-checks `CE_weak` proofs and pipes them through the
   policy interface (§5).
2. **Construct a closure-identity approval** — non-vacuous, but
   trivial enough to be one screen of Lean (§6).
3. **Construct the multn approval** — the worked example, by invoking
   `multnExact_soundForCE_first_install_tower` inside the proof field
   (§7).
4. **Read the Wand-defeat statement** — `((λx. x) 0)` and `0` evaluate
   to the same value under any gated policy table (§8).
5. **Run the end-to-end pipeline** — gate installed, `(set! base-apply
   multn)` admitted, `(2 3 4) ⇒ 24` returned (§9).
6. **Compose admissions into a CE chain** — install multn, then
   identity-delegate on top of it; both admit, the chain is
   CE-extending (§10).

## 0. Setup

```bash
lake build                    # library + three executables
lake exe smoke                # 4 scenes, 8 tests  — structural-policy
lake exe demos                # 12 scenes, 29 tests — reflection capabilities
lake exe proofBasedSmoke      # 10 scenes, 27 tests — proof-based admission
```

Proof-based admission lives in:

- [`LeanBlack/ProofBased.lean`](LeanBlack/ProofBased.lean) — the
  library: `CE_weak_strong`, `ApprovedModification`, `approvedPolicy`,
  the soundness theorem, the identity / closure-identity / multn
  constructors, Wand-defeat.
- [`LeanBlack/Compose.lean`](LeanBlack/Compose.lean) —
  `ValVis_weak` / `CE_weak` / `CE_weak_strong` transitivity. The
  *global guarantee across composed admissions*: a chain of
  approved admissions yields a final apply value CE-related back to
  `bbApply`.
- [`LeanBlack/IdentityDelegate.lean`](LeanBlack/IdentityDelegate.lean)
  — `identityDelegate_CE_of_closure` + `identityDelegateApproval`.
  The concrete second link in a CE chain (see §10 below).
- [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) — runnable scenes
  showing `approvedPolicy` gating a real `.set` during tower
  evaluation. **This is where you see the integration end-to-end.**

(Four companion files — `HeapAgree.lean`, `ContextualBeta.lean`,
`EvalFuelMono.lean`, `Ctx.lean` — carry the in-progress contextual-β
lift. Deferred to §11.)

Proof-based admission is purely additive on the structural-policy
world; the only change to existing files was dropping a `private`
on a preservation lemma in `Soundness.lean`.

## 1. The idea in two sentences

In the structural-policy world (`multnExactPolicy` and friends), an
admission is a Boolean function deciding whether to admit a
`(set! ...)` based on the modification's *structural shape*. With
proof-based admission, an admission is a Lean term of type
`CE_weak_strong level heap oldVal newVal` — a soundness proof for the
specific modification. The kernel type-checks the proof at
construction time; if it doesn't type-check, no admission value
exists. The two admission paths coexist in the same `PolicyTable`.

## 2. The architecture in three definitions

Read these in order (all in `LeanBlack/ProofBased.lean`):

```lean
-- The proof-bearing certificate.
structure ApprovedModification where
  level   : Nat
  heap    : Heap
  oldVal  : Val
  newVal  : Val
  proof   : CE_weak_strong level heap oldVal newVal
```

A value of this type exists *only if* the kernel accepts the `proof`
field. That's the load-bearing kernel admission point.

```lean
-- The runtime gate. Plugs into the existing BlackPolicy interface.
def approvedPolicy (approvals : List ApprovedModification) : BlackPolicy :=
  fun ctx oldVal newVal =>
    approvals.any fun am => am.matches ctx oldVal newVal
```

A `.set` is admitted iff some approval in the list matches on
`(level, heap-prefix, oldVal, newVal)`. The match is structural
(`Val.beq` for the values, `decide` for the level, length-prefix for
the heap).

```lean
-- The headline soundness theorem.
theorem approvedPolicy_soundForCE_weak_strong
    (approvals : List ApprovedModification) (level : Nat)
    (h_levels : ∀ am ∈ approvals, am.level = level) :
    BlackPolicy.SoundForCE_weak_strong level (approvedPolicy approvals)
```

For any list of approvals all bound to the same level, the runtime
gate is sound for `CE_weak_strong` at that level: every admission has
a `CE_weak_strong` witness derivable from the matching approval's
`proof` field.

## 3. How it slots into the existing runtime

The part easiest to miss reading `ProofBased.lean` in isolation:
**`approvedPolicy` is just a `BlackPolicy`**. Nothing in the rest of
lean-sage changes; the new file extends the *construction* of
policies, not the runtime.

```text
                     (existing infrastructure)
                              │
   PolicyTable : List BlackPolicy
                              │
        ┌─────────────────────┼────────────────────┐
        ↓                     ↓                    ↓
    acceptAllPolicy     multnExactPolicy     approvedPolicy ←─── NEW
                        (structural)         (proof-bearing)
                                                   │
                                                   ↑
                            ┌──────────────────────┘
                            │
                    List ApprovedModification
                            │
                            ↑
                  each carries a CE_weak_strong proof
                  (kernel type-checks at construction time)
```

`approvedPolicy approvals` has the same type as `acceptAllPolicy` and
`multnExactPolicy`. From the runtime's perspective, all three are
interchangeable. The difference is *construction*: an approval can
only be built if the kernel accepts a `CE_weak_strong` proof. So the
boolean the runtime sees is *backed by* a proof, even though the
runtime itself doesn't consult the proof.

[`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) Scenes 1–2 show the
integration: an identity approval is installed at level 1, a matching
`.set` admits, a non-matching `.set` refuses, arithmetic is preserved
in both cases.

## 4. Why `CE_weak_strong`?

`Policies.lean` already defines `CE_weak` — a per-level
conservative-extension predicate. But it quantifies over test states
`T` with only `HeapValid` / `ValValid` shape. The multn soundness
theorem `multnExact_soundForCE_first_install_tower` requires *Deep*
validity (`HeapDeep T.heap`, etc.) and Shift-respect on the test
state. So `CE_weak`-shaped approvals cannot be constructed by
invoking that theorem.

`CE_weak_strong` extends `CE_weak`'s hypothesis chain with the
missing Deep + Shift premises, matching exactly what the multn
theorem's proof needs. Same conclusion shape; more hypotheses on the
test state.

```lean
def CE_weak_strong (level : Nat) (h_ref : Heap) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    h_ref.length ≤ T.heap.length →
    HeapValid T.heap → ... →                    -- (CE_weak's premises)
    HeapDeep T.heap → ValDeep op T.heap → ... → -- (new: Deep)
    PolicyTableRespectsShift ... → ... →        -- (new: Shift)
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r', ...                         -- (same conclusion)
```

A trivial weakening `CE_weak_to_strong : CE_weak → CE_weak_strong`
(discard the extra hypotheses) lets the existing identity and
structural-policy machinery feed into the new predicate.

## 5. Your first approval — vacuous identity

The simplest possible `CE_weak_strong` proof: the identity
modification at a `.num n` value. Calling `.num n` as base-apply hits
`applyDirect_num_returns_none`, so the
`callAsBaseApply ... = some (r, T')` premise is unsatisfiable and the
conclusion follows vacuously.

```lean
theorem CE_weak_num_identity (level : Nat) (h_ref : Heap) (n : Int) :
    CE_weak level h_ref (.num n) (.num n) := by
  intro fuel ptable op operands T r T'
    _h_T_len _h_heap _h_op _h_operands _h_old _h_new
    _h_ptable _h_lvl_pol _h_env _h_pol _h_env_bisim h_call
  unfold callAsBaseApply at h_call
  rw [applyDirect_num_returns_none] at h_call
  exact Option.noConfusion h_call
```

Wrap it:

```lean
def numIdentityApproval (level : Nat) (heap : Heap) (n : Int) :
    ApprovedModification :=
  identityApproval level heap (.num n)
```

And demo through `approvedPolicy`:

```lean
def smokeIdentityCtx : MutationCtx :=
  { target := "x", heap := [], env := .nil, metaEnv := .nil,
    index := 0, level := 0 }

def smokeIdentityApprovals : List ApprovedModification :=
  [numIdentityApproval 0 [] 42]

example : approvedPolicy smokeIdentityApprovals
              smokeIdentityCtx (.num 42) (.num 42) = true := by decide

example : approvedPolicy smokeIdentityApprovals
              smokeIdentityCtx (.num 42) (.num 7)  = false := by decide
```

This is the "plumbing smoke" — it validates that the kernel really
does accept a hand-built `CE_weak` term and pipe it through the
policy.

## 6. A substantive approval — closure identity

`CE_weak_refl` generalizes the identity case to any value `v` — but
the proof is no longer vacuous. The proof picks `(fuel', T'', r') :=
(fuel, T', r)` (the new call IS the old call), then needs:

- `ValVis_weak r r T'.heap T'.heap` — bisim of the result with itself.
- `HeapValid T'.heap` — preservation of heap validity.
- `T.heap.length ≤ T'.heap.length` — monotonicity.

These come from `callAsBaseApply_preserves` plus `ValVis_aux_self_extend` +
`ValVis_aux_to_weak`.

```lean
theorem CE_weak_refl (level : Nat) (h_ref : Heap) (v : Val) :
    CE_weak level h_ref v v := by
  intro fuel ptable op operands T r T'
    _h_T_len h_heap h_op h_operands h_old _h_new
    h_ptable h_lvl_pol h_env h_pol h_env_bisim h_call
  obtain ⟨h_heap', h_r', h_mono⟩ :=
    callAsBaseApply_preserves ... h_call
  refine ⟨fuel, T', r, h_call, ?_, rfl, h_heap', h_mono⟩
  intro n
  have h_strong := ValVis_aux_self_extend n r T'.heap [] h_heap' h_r'
  exact ValVis_aux_to_weak _ _ _ _ _ (by simpa using h_strong)
```

The approval:

```lean
def identityApproval (level : Nat) (heap : Heap) (v : Val) :
    ApprovedModification :=
  { level := level, heap := heap, oldVal := v, newVal := v,
    proof := CE_weak_to_strong (CE_weak_refl level heap v) }
```

And demo:

```lean
def trivialClosure : Val :=
  .closure ["op", "args"] (.var "op") .nil

example : approvedPolicy [identityApproval 0 [] trivialClosure]
              smokeIdentityCtx trivialClosure trivialClosure = true := by
  decide
```

This exercises the *operator-wrap* branch of `callAsBaseApply`.

## 7. The multn approval — the worked example

The headline. An `ApprovedModification` for the multn closure,
constructed by invoking `multnExact_soundForCE_first_install_tower`
inside the `CE_weak_strong` proof:

```lean
def multnApproval
    (level : Nat) (heap : Heap) (env metaEnv : Env) (index : Nat)
    (newClosure : Val)
    (h_admit : multnExactPolicy
                 { target := "base-apply", heap := heap, env := env,
                   metaEnv := metaEnv, index := index, level := level }
                 .builtinBaseApply newClosure = true) :
    ApprovedModification := ...
```

Two pieces of machinery made this work:

1. **`InstallFacts.heap_extend`** — `OrigBoundIn` and `NumQBoundIn`
   are about specific heap-cell lookups, so they transport across a
   content-preserving `HeapPrefix` extension. This is why
   `ApprovedModification.matches` checks **content-prefix** (not just
   length) and `CE_weak_strong` carries `HeapPrefix h_ref T.heap`.

2. **Fuel split.** `multnExact_soundForCE_first_install_tower`
   requires `fuel ≥ 2`. `CE_weak_strong` quantifies over arbitrary
   `fuel`. The proof case-analyzes:
   - `fuel = 0`: vacuous (`applyDirect 0` returns `none`).
   - `fuel = 1`: by case on `op`, succeeds only for `op = .prim p`.
     For the prim subcase, "bump" fuel to 2 via
     `applyDirect_prim_fuel_bump`, then invoke the multn theorem.
   - `fuel ≥ 2`: invoke directly.

[`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) Scene 3 builds a sample
admission state, constructs the approval, and verifies the gate
admits/refuses correctly:

```
Scene 3: multn approval constructs + matches
  OK  multnApproval admits multn ctx: expected true, got true
  OK  multnApproval refuses non-multn newVal: expected false, got false
```

The "admits" line is the evidence the abstract names: the kernel
type-checked the `CE_weak_strong` proof, the runtime gate accepts
the admission.

## 8. Wand defeat — β-equivalence under gated reflection

The convergent existential statement: under proof-bearing admission,
the β-redex `((λx. x) 0)` and the contractum `0` are observationally
equivalent at the top level.

```lean
def ObsEquivConvergesGated (approvals : List ApprovedModification)
    (M N : Expr) : Prop :=
  ∃ fuel v,
    evalProgram fuel [approvedPolicy approvals] M = some v ∧
    evalProgram fuel [approvedPolicy approvals] N = some v

theorem wand_defeated_existential_gated_beta
    (approvals : List ApprovedModification) :
    ∃ M N : Expr, M ≠ N ∧ ObsEquivConvergesGated approvals M N
```

Read: for any list of proof-bearing approvals, the β-redex and its
contractum are non-equal as `Expr` constructors but converge to the
same value under any gated policy table. **The existence of
admissions doesn't disturb β.**

The bridge is `AllPureIndep` (also sorry-free): `eval` is
policy-table-independent for `Pure` expressions (no `.set`, no
`.installPolicy`). The β-redex is `Pure`, so the choice of policy
table doesn't affect its evaluation.

This is the convergent form; full contextual obs-equivalence (∀
context C) is in progress — see §11.

## 9. End-to-end through the gate

Scenes 8 and 9 in `ProofBasedSmoke.lean` run the full pipeline:
gate installed, gated `set!` admitted by the kernel-checked approval,
post-admission application returns 24 (level 1 directly, level 2 via
`(em (2 3 4))` dispatched through level-2's now-multn base-apply).

The trick is making the approval's `newVal` byte-equal what `eval`
constructs at the `.lam` rule: since `freshLevelEnv` is a
deterministic Lean function, re-running it in pure code yields the
same cenv the evaluator captures, so `Val.beq` byte-equality falls
out of definitional equality — no runtime instrumentation needed.

## 10. Composing admissions — the chain `bbApply → multn → identity-delegate`

The abstract's *global guarantee across composed admissions* is
mechanized via the composition theorem `CE_weak_strong_trans` in
[`LeanBlack/Compose.lean`](LeanBlack/Compose.lean). Given two
CE-extending admissions at the same level, the chain is itself
CE-extending end-to-end:

```lean
theorem CE_weak_strong_trans
    {level : Nat} {h_ref : Heap} {v_a v_b v_c : Val}
    (h1 : CE_weak_strong level h_ref v_a v_b)
    (h2 : CE_weak_strong level h_ref v_b v_c) :
    -- ... (full premises threading)
    -- ∃ chained admission with v_c CE-related to v_a.
```

The composition uses `ValVis_aux_weak_trans` (depth-indexed value-
bisim transitivity, also in `Compose.lean`) to compose the two
`ValVis_weak`-related results into one.

### A concrete second link: `identity-delegate-on-closure`

[`LeanBlack/IdentityDelegate.lean`](LeanBlack/IdentityDelegate.lean)
builds the simplest non-trivial second link in a CE chain: a wrapper
whose body is `(orig op args)` — pure delegation to the captured
`orig`. As an admission on top of any closure (e.g., a multn already
installed), it's a CE of that closure: every call falls through to
`orig` and returns the same result, modulo the heap allocation the
wrapper-form invocation incurs.

```lean
theorem identityDelegate_CE_of_closure
    (level : Nat) (h_ref : Heap) (origVal : Val) (cenv : Env) (idx_o : Nat)
    (h_not_bbApply : origVal ≠ .builtinBaseApply)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_heap_o : h_ref[idx_o]? = some origVal) :
    CE_weak_strong level h_ref origVal
      (.closure ["op", "args"] identityDelegateBody cenv)
```

The proof bridges (a) the wrapper's body trace (which unfolds to
`applyDirect origVal [op, listToVal operands]` at the alloc'd state)
and (b) `applyDirect_heap_extend_weak` (which lifts the
hypothesis-side direct call from `T` to `T_alloc`). The `Deep`
validity premises that the heap-extend lemma needs are derived from
the `HeapDeep T.heap` premise via the fact that `origVal` sits at
`idx_o` in `T.heap`.

The companion constructor `identityDelegateApproval` packages this
into an `ApprovedModification` you can drop into an `approvedPolicy`
list.

### Running the chain

[`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) Scene 10 exercises the
chain end-to-end at the gate level:

```
Scene 10: composed admission chain bbApply → multn → identity-delegate
  OK  step 1 (bbApply → multn): expected true, got true
  OK  step 2 (multn → identity-delegate): expected true, got true
  OK  step 2 refuses doubling (no matching approval): expected false, got false
```

The composed approvals list `[runtimeMultnApprovalLevel1,
runtimeIdentityDelegateApproval]` admits both `.set` operations on
the same `base-apply` cell sequentially. A wrong-shape
modification at step 2 is refused — the gate doesn't just admit
anything once multn is installed.

This is the abstract's "admissions compose at a single gate" claim
backed by a concrete chain.

## 11. Recap — what you can now state

You can write Lean code that produces:

- An `ApprovedModification` whose `proof` field discharges
  `CE_weak_strong` (via `numIdentityApproval`, `identityApproval`,
  `multnApproval`, or `identityDelegateApproval`).
- A `BlackPolicy` from a list of approvals (`approvedPolicy`).
- A soundness invocation `approvedPolicy_soundForCE_weak_strong` that
  gives you a `CE_weak_strong` witness for every admitted
  modification at runtime.
- A `CE_weak_strong_trans` invocation composing two admissions at the
  same level into a chained CE-extending substrate.
- A `wand_defeated_existential_gated_beta` instance — β-equivalence
  survives under the gated policy table.

And run `lake exe proofBasedSmoke` to see the full pipeline (10
scenes, 27 tests) admitting / refusing / composing in real time.

That's the proof-based half of lean-sage. The structural-policy half
(`multnExactPolicy` + `multnExact_soundForCE_first_install_tower`) is
covered in [`DESIGN.md`](DESIGN.md) and exercised by
`lake exe smoke` + `lake exe demos`.

For a single entry-point exposing just the public API, see
[`LeanBlack/Public.lean`](LeanBlack/Public.lean).

## 12. Beyond the basics — contextual β (in progress)

The W1 statement in §8 is *convergent* obs-equivalence (M and N
evaluate to the same value at the top level). Full *contextual*
obs-equivalence — `∀ C : Expr → Expr, evalProgram (C[M]) =
evalProgram (C[N])` — is in progress. The pieces:

- [`LeanBlack/EvalFuelMono.lean`](LeanBlack/EvalFuelMono.lean) — fuel
  monotonicity for all four mutually-recursive eval functions. The
  arithmetic enabler for fuel-juggling inside the cross-side bisim
  and the contextual β bridges.
- [`LeanBlack/Ctx.lean`](LeanBlack/Ctx.lean) — term contexts +
  `EvalEquiv` observational equivalence + per-constructor
  congruence lemmas. The clean half (`EasyCtx`, `WideCtx`,
  `SimpleCtx`) covers every `Expr`-tree position except `.lam`,
  which is deferred because of closure-syntactic refinement.
- [`LeanBlack/ContextualBeta.lean`](LeanBlack/ContextualBeta.lean) —
  operational β-redex factoring (`eval_beta_builtin`) and CE→β
  bridges (`ce_apply_bisim_builtin`,
  `admission_applyVia_bisim_builtin`). The first place where
  `approvedPolicy` admission flows into a β-equivalence statement
  with CE consumed (rather than the policy-irrelevant `AllPureIndep`
  path).
- [`LeanBlack/HeapAgree.lean`](LeanBlack/HeapAgree.lean) — selective
  heap-prefix relation `HeapAgreeAt` and `CE_weak_strong_at`
  predicate, weakening the CE premise from full-prefix to
  agreement-at-specific-cells. Lets the CE certificate survive past
  the admission moment (where the full-prefix premise breaks because
  the base-apply cell changes).

The headline near-result: **`contextual_beta_easy`** (in `Ctx.lean`)
— for any `EasyCtx` and any `(x, body, v_expr)`, `C.plug (β-redex)`
and `C.plug (.letE)` are observationally equivalent at every state
satisfying `BetaLetEReady v_expr`. This is the contextually-quantified
β statement for the easy-context sub-language. What remains is
threading the L4 parallel-bisim invariant through `eval` to lift to
arbitrary contexts.

## 13. Reading order for the source

If you want to dig into `LeanBlack/ProofBased.lean`, it's structured
top-to-bottom for sequential reading:

1. `DecidableEq` machinery (mutual `*_beq_self` + instances).
2. `HeapPrefix` + helpers.
3. `CE_weak_strong` predicate + `CE_weak_to_strong` weakening.
4. `BlackPolicy.SoundForCE_weak_strong` abbrev.
5. `ApprovedModification` structure.
6. `ApprovedModification.matches` + `approvedPolicy` runtime gate.
7. `structural_policy_yields_approval` (bridge from existing
   `SoundForCE_weak`).
8. `CE_weak_strong_heap_mono` + `approvedPolicy_soundForCE_weak_strong`
   (the headline soundness).
9. Identity (vacuous + reflexive) approvals + plumbing smoke.
10. Wand defeat (W1 baseline, gated, gated-β via `AllPureIndep`).
11. Multn approval (the worked example), exercised in Scene 3.

Cross-references to `Policies.lean` are throughout — they show how
the existing structural-policy machinery feeds into the proof-based
reading.
