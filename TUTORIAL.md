# TUTORIAL — proof-based admission in lean-sage

A hands-on walkthrough of proof-based admission. By the end, you'll
understand:

- What an `ApprovedModification` is and why its `proof` field is
  load-bearing.
- How `approvedPolicy` plugs proof-bearing admission into the existing
  `BlackPolicy` interface.
- What `CE_weak_strong` is and why we needed it.
- How to construct an approval (the identity case, two flavors).
- The W1 convergence statements and what they actually claim.
- What's still open and where to start.

If you want the architectural rationale instead, read
[`DESIGN_PROOF.md`](DESIGN_PROOF.md).

## 0. Setup

```bash
lake build                    # builds the library + all three exes
lake exe smoke                # 8/8  — structural-policy smoke
lake exe demos                # 29/29 — reflection demos
lake exe proofBasedSmoke      # 18/18 — proof-based integration scenes
```

Proof-based admission lives in four files:

- [`LeanBlack/ProofBased.lean`](LeanBlack/ProofBased.lean) — the
  library: `CE_weak_strong`, `ApprovedModification`, `approvedPolicy`,
  the soundness theorem, the identity constructors, W1.
- [`LeanBlack/HeapAgree.lean`](LeanBlack/HeapAgree.lean) —
  `HeapAgreeAt` (selective heap-prefix relation),
  `CE_weak_strong_at` (selective-premise CE predicate), and
  `multnApproval_at_proof` — the multn approval under the
  weakened premise, consumable post-mutation. See §11.6.
- [`LeanBlack/ContextualBeta.lean`](LeanBlack/ContextualBeta.lean) —
  operational β-redex factoring and the CE→β bridges (full-prefix
  + selective). Connects an `approvedPolicy` admission to a
  runtime β-equivalence statement. See §11.5.
- [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) — runnable scenes
  showing `approvedPolicy` installed at a level and gating a real
  `.set` during tower evaluation. **This is where you see the
  integration with the rest of lean-sage.**

Proof-based admission is purely additive on top of the structural-
policy world; the only change to existing files was dropping a
`private` on a preservation lemma in `Soundness.lean`.

## 1. The idea in two sentences

In the structural-policy world (`multnExactPolicy` and friends), an
admission is a Boolean function deciding whether to admit a
`(set! ...)` based on the modification's *structural shape*. With
proof-based admission, an admission is a Lean term of type
`CE_weak_strong level heap oldVal newVal` — a soundness proof for the
specific modification. The kernel type-checks the proof at construction
time; if it doesn't type-check, no admission value exists. The two
admission paths coexist in the same `PolicyTable`.

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

At runtime, a `.set` is admitted iff some approval in the list matches
on `(level, heap-prefix, oldVal, newVal)`. The match is structural
(`Val.beq` for the values, `decide` for the level, length-prefix for
the heap).

```lean
-- The headline soundness theorem.
theorem approvedPolicy_soundForCE_weak_strong
    (approvals : List ApprovedModification) (level : Nat)
    (h_levels : ∀ am ∈ approvals, am.level = level) :
    BlackPolicy.SoundForCE_weak_strong level (approvedPolicy approvals)
```

For any list of approvals all bound to the same level, the
runtime gate is sound for `CE_weak_strong` at that level. Every
admission has a `CE_weak_strong` witness derivable from the matching
approval's `proof` field.

## 3. How it slots into the existing runtime

This is the part of the story easiest to miss reading
`ProofBased.lean` in isolation: **`approvedPolicy` is just a
`BlackPolicy`**. Nothing in the rest of lean-sage changes; the new
file extends the *construction* of policies, not the runtime.

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

A `BlackPolicy` is just a function `MutationCtx → Val → Val → Bool`.
The runtime gate fires inside `eval`'s `.set` rule (see
[`LeanBlack/Eval.lean`](LeanBlack/Eval.lean):87, `gate := T.policyAt?
level`). `approvedPolicy approvals` is a `BlackPolicy` — it takes the
same arguments, returns a `Bool`. From the runtime's perspective,
it's interchangeable with `acceptAllPolicy` or `multnExactPolicy`.

What's different is *construction*: an approval can only be built if
the kernel accepts a `CE_weak_strong` proof. So the boolean the
runtime sees is *backed by* a proof, even though the runtime itself
doesn't consult the proof.

[`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) demonstrates the
integration end-to-end. Scene 1 installs
`approvedPolicy [identityApproval 1 [] .builtinBaseApply]` at level 1
via `(em (installPolicy 0))`, runs `(em (set! base-apply base-apply))`,
and watches the `.set` go through the gate, find a match, and admit.
Scene 2 attempts a non-matching mutation; the gate finds no match
and refuses. Both scenes also check that arithmetic is preserved
afterward.

```bash
$ lake exe proofBasedSmoke
Scene 1: proof-bearing admission — identity mod ADMITTED
  OK  (em (set! base-apply base-apply)) ⇒ bool(true): ...
  OK  post-admit, (+ 1 2) still 3: ...

Scene 2: proof-bearing admission — non-matching mod REFUSED
  OK  (em (set! base-apply (lam … 42))) ⇒ bool(false): ...
  OK  post-refuse, (+ 1 2) still 3 (no mod in effect): ...
```

That's the full integration. The next sections explain how the proof
field is constructed.

## 4. Why `CE_weak_strong`?

`Policies.lean` already defines `CE_weak` — a per-level
conservative-extension predicate. But it quantifies over test states
`T` with only `HeapValid` / `ValValid` shape. The headline soundness
theorem in `Policies.lean` —
`multnExact_soundForCE_first_install_tower` — requires Deep validity
(`HeapDeep T.heap`, etc.) and Shift-respect on the test state. So
`CE_weak`-shaped approvals cannot be constructed by invoking that
theorem.

`CE_weak_strong` extends `CE_weak`'s hypothesis chain with the missing
Deep + Shift premises, matching exactly what the multn theorem's proof
needs. Same conclusion shape; more hypotheses on the test state.

```lean
def CE_weak_strong (level : Nat) (h_ref : Heap) (old new : Val) : Prop :=
  ∀ fuel ptable op operands T r T',
    h_ref.length ≤ T.heap.length →
    HeapValid T.heap → ... →                    -- (CE_weak's premises)
    HeapDeep T.heap → ValDeep op T.heap → ... → -- (new: Deep)
    PolicyTableRespectsShift ... → ... →        -- (new: Shift)
    callAsBaseApply fuel ptable level old op operands T = some (r, T') →
    ∃ fuel' T'' r', ...                          -- (same conclusion)
```

There's a trivial weakening `CE_weak_to_strong : CE_weak → CE_weak_strong`
(discard the extra hypotheses), which lets the existing identity and
structural-policy machinery feed into the new predicate without
rework.

## 5. Constructing your first approval (vacuous)

The simplest possible `CE_weak_strong` proof: the identity modification
at a `.num n` value. Calling `.num n` as base-apply hits
`applyDirect_num_returns_none`, so the `callAsBaseApply ... = some
(r, T')` premise is unsatisfiable and the conclusion follows vacuously.

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

We wrap it into an approval:

```lean
def numIdentityApproval (level : Nat) (heap : Heap) (n : Int) :
    ApprovedModification :=
  identityApproval level heap (.num n)
```

And demo it through `approvedPolicy`:

```lean
def smokeIdentityCtx : MutationCtx :=
  { target := "x", heap := [], env := .nil, metaEnv := .nil,
    index := 0, level := 0 }

def smokeIdentityApprovals : List ApprovedModification :=
  [numIdentityApproval 0 [] 42]

-- The policy admits a matching .set; refuses a non-matching one.
example : approvedPolicy smokeIdentityApprovals
              smokeIdentityCtx (.num 42) (.num 42) = true := by decide

example : approvedPolicy smokeIdentityApprovals
              smokeIdentityCtx (.num 42) (.num 7)  = false := by decide
```

This is the "plumbing smoke" — it validates that the kernel really does
accept a hand-built `CE_weak` term and pipe it through the policy.

## 6. A more substantive approval (closure identity)

`CE_weak_refl` generalizes the identity case to any value `v` — but
the proof is no longer vacuous. The proof picks `(fuel', T'', r') :=
(fuel, T', r)` (i.e., the new call IS the old call), then needs:

- `ValVis_weak r r T'.heap T'.heap` — bisim of the result with itself.
- `HeapValid T'.heap` — preservation of heap validity.
- `T.heap.length ≤ T'.heap.length` — monotonicity.

These come from `callAsBaseApply_preserves` (a wrapper around the
public `applyDirect_preserves_self_invariants` in `Soundness.lean`)
plus `ValVis_aux_self_extend` + `ValVis_aux_to_weak`.

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

The approval, with `CE_weak.to_strong` to widen to `CE_weak_strong`:

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

def smokeClosureApprovals : List ApprovedModification :=
  [identityApproval 0 [] trivialClosure]

example : approvedPolicy smokeClosureApprovals
              smokeIdentityCtx trivialClosure trivialClosure = true := by
  decide
```

This exercises the *operator-wrap* branch of `callAsBaseApply` (the
non-`.builtinBaseApply` case). The arity check, foldl alloc, and body
eval all run — but since `new = old = v`, the call is its own
conservative extension.

## 7. W1: convergent obs-equivalence under proof-bearing admission

A weak existential observational equivalence: under proof-bearing
admission, there exist syntactically-distinct expressions that
converge to the same value. This is a convergent form (same eval
result at some fuel), not full contextual equivalence over all
eval contexts. It is the easiest piece of the Wand-defeat story
to mechanize directly; the contextual lift is informal but
substantive (see "What's still open").

```lean
def ObsEquivConverges (M N : Expr) : Prop :=
  ∃ fuel v,
    evalProgram fuel [acceptAllPolicy] M = some v ∧
    evalProgram fuel [acceptAllPolicy] N = some v

theorem wand_defeated_existential (_approvals : List ApprovedModification) :
    ∃ M N : Expr, M ≠ N ∧ ObsEquivConverges M N := by
  refine ⟨.app [.lam ["x"] (.var "x"), .num 0], .num 0, ?_, ?_⟩
  · intro h; cases h
  · refine ⟨100, .num 0, ?_, ?_⟩ <;> native_decide
```

**Reading**: for any list of proof-bearing approvals in scope, the
β-redex `((λx. x) 0)` and its contractum `.num 0` are non-equal as
`Expr` constructors but converge to the same value at fuel 100. The
existence of admissions doesn't disturb β.

**Why `_approvals` is unused**: the witness pair contains no `.set`,
so the policy gate isn't consulted during eval. The theorem documents
that admissions are non-disturbing; it doesn't claim the admissions
participate in the computation.

**Why `[acceptAllPolicy]` and not `[approvedPolicy approvals]`**:
`native_decide` needs a closed term to compile. The strengthening to
the gated form, with the β-redex witness preserved, is
`wand_defeated_existential_gated_beta` in §9 below, bridged through
the `AllPureIndep` policy-independence lemma.

**The DecidableEq machinery**: `native_decide` for `Option Val`
equality requires `DecidableEq Val`. Lean 4 doesn't auto-derive
`DecidableEq` for mutually-recursive inductives (`Val`/`Expr`/`Env`),
so `ProofBased.lean` builds the instance manually from the existing
`Val.beq` + `val_beq_eq` (in `Black.lean`) plus a freshly-proved
mutual reflexivity (`val_beq_self`, `expr_beq_self`, `env_beq_self`).

## 8. The multn approval

The headline worked example: an `ApprovedModification` for the multn
closure, constructed by invoking
`multnExact_soundForCE_first_install_tower` inside the
`CE_weak_strong` proof.

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
   - `fuel = 0`: `applyDirect 0` returns `none`, vacuous.
   - `fuel = 1`: by case on `op`, the call succeeds only for
     `op = .prim p` (other constructors give `none`). For the prim
     subcase, we "bump" fuel to 2 (`applyDirect_prim_fuel_bump` —
     `applyDirect ≥ 1` on `.prim` is fuel-independent), then invoke
     the multn theorem.
   - `fuel ≥ 2`: invoke directly.

[`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) Scene 3 builds a
sample admission state (`sampleAdmitHeap`, `sampleAdmitCenv`,
`sampleMultnClosure`), constructs the approval via `multnApproval`,
and verifies `approvedPolicy` admits/refuses correctly:

```
Scene 3: multn approval constructs + matches
  OK  multnApproval admits multn ctx: expected true, got true
  OK  multnApproval refuses non-multn newVal: expected false, got false
```

The "admits" line is the evidence the abstract names: the kernel
type-checked the `CE_weak_strong` proof (which threads through
fuel splits and the existing multn soundness theorem), and the
runtime gate accepts the admission.

For the end-to-end runtime — actually firing this approval through
`evalProgram` and observing `(2 3 4) ⇒ 24` — see Scenes 8 (level 1)
and 9 (level 2) below.

## 9. The `Pure` policy-independence lemma + strengthened β-redex W1

The `AllPureIndep` lemma — proved sorry-free — establishes that
`eval` (and the mutually-recursive `evalList`/`applyVia`/`applyDirect`)
are policy-table-independent for `Pure` expressions in a `PureHeap`
context. `Pure` rules out `.set` and `.installPolicy`; everything
else (including `.em`/`.app`/`.letE`/`.primApp`/`.seq`) thread the
policy without consulting it.

```lean
def Pure : Expr → Bool := ...        -- no .set, no .installPolicy
def PureVal : Val → Bool := ...      -- closures have Pure bodies; .cons recurses
def PureHeap (h : Heap) : Prop := ∀ i v, h[i]? = some v → PureVal v = true

theorem allPureIndep : ∀ fuel, AllPureIndep fuel  -- joint induction on fuel
```

The proof is ~1000 LOC of joint induction with auxiliary preservation
lemmas (`PureHeap_append`, `materialize_preserves_PureHeap`,
`Heap_alloc_preserves_PureHeap`, `foldl_allocStep_preserves_PureHeap`,
`PureVal_listToVal`, `valToList_PureValList`, `applyPrim_PureVal`).
With it in hand, **β-redex W1 strengthens**:

```lean
theorem wand_defeated_existential_gated_beta
    (approvals : List ApprovedModification) :
    ∃ M N : Expr, M ≠ N ∧ ObsEquivConvergesGated approvals M N := by
  refine ⟨.app [.lam ["x"] (.var "x"), .num 0], .num 0, ?_, ?_⟩
  · intro h; cases h
  · refine ⟨100, .num 0, ?_, ?_⟩
    · rw [evalProgram_pure_indep _ (by decide) 100
            [approvedPolicy approvals] [acceptAllPolicy]]
      native_decide
    · simp [evalProgram, eval]; rfl
```

The β-redex narrative is now formal in the convergent sense: the
β-redex `(λx. x) 0` and its contractum `.num 0` evaluate to the
same value under any gated policy table, proved sorry-free. The
full contextual lift (∀ context C, evalProgram (C[M]) = evalProgram
(C[N])) is not formalized — see "What's still open".

## 10. End-to-end multn through the proof-based gate

Scenes 8 and 9 in [`ProofBasedSmoke.lean`](ProofBasedSmoke.lean) run
the full pipeline through `evalProgram`: gate installed, gated
`set!` fires and is admitted by the kernel-checked approval, and
the post-admission application returns `24` (level 1 directly,
level 2 via `(em (2 3 4))` dispatched through level-2's now-multn
base-apply). The trick is making the approval's `newVal` byte-equal
what `eval` constructs at the `.lam` rule: since `freshLevelEnv` is
a deterministic Lean function, re-running it in pure code yields
the same cenv the evaluator captures, so `Val.beq` byte-equality
falls out of definitional equality — no runtime instrumentation
needed.

## 11. What's still open

**The contextual obs-equivalence lift.** The W1 statements in §7 and
§9 are about convergent obs-equivalence (M and N evaluate to the
same value at the top level). Full contextual obs-equivalence —
`∀ C : Expr → Expr, evalProgram (C[M]) = evalProgram (C[N])` — is
not in Lean. The informal argument lifts cleanly (any admitted
modification preserves call-trace bisim, so no context can
distinguish β-equivalent pairs through the gated runtime), but the
universal quantification over `C` is not yet a theorem.

`LeanBlack/ContextualBeta.lean` is a first step toward this lift —
see §11.5.

## 11.5. ContextualBeta — operational β and the CE→β bridge

[`LeanBlack/ContextualBeta.lean`](LeanBlack/ContextualBeta.lean) adds
three sorry-free theorems that connect the kernel infrastructure to
β-equivalence statements directly (rather than going through
`allPureIndep`).

**`eval_beta_builtin`** (L1). At sufficient fuel, with level+1's
`base-apply` cell still bound to `.builtinBaseApply` and level+1
materialized below `Tower.maxDepth`:

```lean
eval (n + 3) ptable level (.app [.lam [x] body, v_expr]) env T
  = eval n ptable level body
      (Env.cons x T'.heap.length env)
      { T' with heap := T'.heap ++ [v_val] }
```

— provided `v_expr` evaluates to `(v_val, T')` at fuel `n+1`. Pure
operational unfolding through `.app` / `.lam` / `applyVia`-builtin /
`applyDirect`-closure. No CE consumed.

**`ce_apply_bisim_builtin`** (CE→β bridge). Given a `CE_weak_strong`
certificate for the user-installed `base-apply` over the current heap,
the apply path produces a bisim-equivalent result to the
counterfactual builtin apply. Threads the full 16-condition CE
premise stack and consumes the certificate once.

**`admission_applyVia_bisim_builtin`** (admission corollary). Same
conclusion as above, but with the CE certificate replaced by
`approvedPolicy approvals ctx .builtinBaseApply bc = true` + an
`am.level = level` invariant on `approvals`. This is the first place
in the repo where `approvedPolicy`-admission flows into a β-equivalence
statement at the runtime.

### What this changes vs. the prior W1 story

- `wand_defeated_existential_gated_beta` (§9) proves β for one
  fixed pair `((λx. x) 0)` ≡ `0`, via `allPureIndep` — the policy is
  never actually consulted because the redex is pure.
- The bridge proves β-equivalence for **any** closure call going
  through an admitted user `base-apply`, with CE actually flowing
  into the conclusion. It just fires at one specific moment.

### Why "one specific moment"

The bridge fires where `HeapPrefix am.heap T.heap` holds. By
construction this holds at the admission moment (the `.set` step
itself, before the heap update commits — `ctx.heap = T.heap` and
`am.heap` content-prefix-matches `ctx.heap`).

After the `.set` commits, `T_post.heap = T.heap.update idx_ba bc`.
Since `idx_ba < am.heap.length`, the content-prefix property breaks
on the base-apply cell:

```text
am.heap[idx_ba]    = .builtinBaseApply   -- (in am's snapshot)
T_post.heap[idx_ba] = bc                  -- (after the .set commits)
```

`CE_weak_strong_heap_mono` cannot lift the certificate to
`T_post.heap`. So future β-equivalence questions — the kind a
contextual lift would ask — sit outside the bridge's reach.

### What the contextual lift requires

The multn proof's actual cell lookups (via `multnExactPolicy_implies_InstallFacts`
in `Policies.lean`) only read the closure's captured `orig` and
`num?` indices — never the base-apply cell. The `HeapPrefix`
premise is **stronger than necessary** — it demands content-equality
on cells the proof doesn't read.

### §11.6. Selective-premise CE — `HeapAgree.lean` (the unblock)

[`LeanBlack/HeapAgree.lean`](LeanBlack/HeapAgree.lean) implements
the weakening, sorry-free. Key definitions and theorems:

- `HeapAgreeAt indices h₁ h₂` — content-equality at the specified
  indices, no constraint on other cells.
- `HeapAgreeAt.update_disjoint` — heap-update at index `j ∉ indices`
  preserves agreement. The lemma that makes post-mutation lifting
  work.
- `CE_weak_strong_at level indices h_ref old new` — the
  selective-premise CE predicate. Same conclusion as
  `CE_weak_strong`, but premise is `HeapAgreeAt indices` +
  `length_le` instead of `HeapPrefix`.
- `InstallFacts_heap_agree_cells` — transports `InstallFacts`
  across `HeapAgreeAt` at the closure's `orig` and `num?` indices.
- **`multnApproval_at_proof`** — the multn approval re-proved
  under `CE_weak_strong_at`. Mirrors `multnApproval`'s proof body
  almost verbatim; only the `InstallFacts` transport line changes
  (from `InstallFacts_heap_extend` to `InstallFacts_heap_agree_cells`).

[`LeanBlack/ContextualBeta.lean`](LeanBlack/ContextualBeta.lean)
adds the matching bridge:

- **`ce_apply_bisim_builtin_at`** — same as `ce_apply_bisim_builtin`
  but consumes `CE_weak_strong_at indices` with a `HeapAgreeAt
  indices h_ref T.heap` witness. Usable post-admission: the .set
  mutates `idx_ba`; under the `installMultnOneUp` pattern (which
  allocates `orig` via `.letE`), `idx_ba ∉ [idx_o, idx_n]`, so
  `update_disjoint` keeps the agreement intact and the bridge
  fires.

Net effect: the CE certificate now flows past admission. What
remains for full contextual β is L4's parallel-bisim invariant
threaded through eval — the pieces it consumes are now in place.

## 12. Reading order for the source

If you want to dig into `LeanBlack/ProofBased.lean`, the file is
already structured top-to-bottom for sequential reading:

1. `DecidableEq` machinery (mutual `*_beq_self` + instances).
2. `HeapPrefix` + helpers (`length_le`, `refl`, `trans`, `getElem?`).
3. `CE_weak_strong` predicate + `CE_weak_to_strong` weakening.
4. `BlackPolicy.SoundForCE_weak_strong` abbrev.
5. `ApprovedModification` structure.
6. `ApprovedModification.matches` (content-prefix check) +
   `approvedPolicy` runtime gate.
7. `structural_policy_yields_approval` (bridge from existing
   `SoundForCE_weak` to the new predicate).
8. `CE_weak_strong_heap_mono` + `approvedPolicy_soundForCE_weak_strong`
   (the headline soundness).
9. `CE_weak_num_identity` + `numIdentityApproval` (vacuous identity).
10. Plumbing smoke (`smokeIdentityCtx`, `smokeIdentityApprovals`, the
    `example`s).
11. `callAsBaseApply_preserves` + `CE_weak_refl` + `identityApproval`
    (closure-identity).
12. Closure-identity demo (`trivialClosure`, `smokeClosureApprovals`).
13. `ObsEquivConverges` + `wand_defeated_existential` (W1, baseline).
14. `ObsEquivConvergesGated` + `wand_defeated_existential_gated`
    (W1, gated, `.ifte` witness).
15. **`Pure` policy-independence**: `Pure`/`PureVal`/`PureHeap`
    predicates, auxiliary preservation lemmas
    (`PureHeap_append`, `freshLevelEnv_preserves_PureHeap`,
    `materialize_preserves_PureHeap`, `Heap_alloc_preserves_PureHeap`,
    `foldl_allocStep_preserves_PureHeap`, `PureVal_listToVal`,
    `valToList_PureValList`, `applyPrim_PureVal`), `AllPureIndep`
    statement, `allPureIndep_zero` (base), `allPureIndep_succ`
    (inductive step), `allPureIndep` (wrapper),
    `evalProgram_pure_indep`, and
    `wand_defeated_existential_gated_beta` (β-redex witness under
    `[approvedPolicy approvals]`).
16. **Multn approval**: `InstallFacts.heap_extend` (via
    `OrigBoundIn_heap_extend` and `NumQBoundIn_heap_extend`),
    `applyDirect_prim_fuel_bump`,
    `callAsBaseApply_one_builtin_succeeds_implies_prim`, and
    `multnApproval` itself. Exercised in
    `ProofBasedSmoke.lean` Scene 3.

Cross-references to `Policies.lean` are throughout — they show how the
existing structural-policy machinery feeds into the proof-based
reading.
