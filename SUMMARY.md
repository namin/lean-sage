# lean-sage — what it shows (and what it shows is false)

lean-sage (Lean 4, `LeanBlack/`) studies one question: **does equational reasoning
survive reflection?** The classical pessimism is Wand's *"the theory of fexprs is
trivial"* — sufficiently powerful reflection collapses the contextual-equivalence
theory to syntactic identity, so no nontrivial program equations survive. lean-sage
draws the precise dividing line that pessimism misses, for the most basic equation:
β-reduction `(λx.B) V ≡ let x = V in B` in a Black-style reflective tower with a
standard `base-apply` **gate** on reflection.

All theorems named below are `sorry`-free and axiom-clean (axioms ⊆ `{propext,
Classical.choice, Quot.sound}`); the headline names are CI-audited in
`LeanBlack/AxiomAudit.lean`, and `lake build` is green.

## Headline message

**Reflection need not destroy equational reasoning — but β survives only
*conditionally*, at a precisely-characterized cost, and that cost is provably
necessary, not a proof artifact.** β-reduction in the tower is **directional**:
contraction (`redex → contractum`) preserves convergence, but the contractum can be
*strictly more defined* than the redex — it sidesteps the gate at the top of the tower
— so the two coincide as a contextual equivalence only under a **gate + purity + depth
budget**. Not "reflection is fine," not "reflection ruins everything," but the exact
boundary: the surviving side proved, the failing side proved to fail.

## What is shown true (machine-checked)

Conditions throughout: the standard `base-apply` **gate**, a **pure** operand and pure
pre-hole siblings, and (where a binder/`em`-nesting is involved) a **depth budget**
within the tower bound (`Tower.maxDepth`).

- **`contextual_beta_pure`** — β *is* a full contextual equivalence
  (`redex ≡ contractum`, `CtxEquiv`, **both directions**) in **every `Expr` position
  except under `.lam`** (all twelve non-binder constructors), under the conditions
  above. Program-level forms: `contextual_beta_at_start` (run from the canonical
  pre-materialized start tower) and the specific Wand pair
  `wand_defeated_existential_gated_beta` surviving gated reflection.
- **`obsConv_refine_forward`** — the **forward direction of the conditional ground
  `.lam` congruence**, for an *arbitrary* context `C` (binder contexts included):
  under the gate + purity, on ground observation,
  `ObsConv (C.plug redex) → ObsConv (C.plug contractum)`. (The redex refines its
  contractum — under a binder.)
- **`frameβ_redex_letE_evalRevB`** — the crux of the *backward* `.lam` direction for
  the literal redex: the conditional reverse simulation of `(λx.B) V` against
  `let x = V in B` under the depth budget. Proved as down payment toward the `.lam`
  congruence — not yet assembled into a headline (see *What is open*).

## What is shown not true (machine-checked impossibilities)

Three impossibilities pin why the `.lam` equivalence is not closable in any naive
frame — i.e., why each condition above is forced.

- **A — the fine congruence fails** (`lam_EvalEquiv_congruence_fails`).
  Outcome-equality congruence is false under `.lam`: closures freeze their bodies
  verbatim, so equivalent-but-syntactically-different bodies are distinguished.
  ⟹ observation must coarsen to **ground / up-to-bisimulation**.
- **B — even ground equivalence fails *unconditionally*** (`beta_not_unconditional_CtxEquiv`).
  At the top of the tower the redex's gate-mediated apply cannot fire, so the
  contractum converges where the redex diverges. ⟹ the equivalence must carry the
  **gate + depth** side conditions; it is not unconditional.
- **C — the gate alone is insufficient for the reverse** (`reverseSimβ_false`).
  The backward `.lam` simulation `ReverseSimβ`, stated with the all-levels gate but
  **no depth margin**, is false. ⟹ a **depth budget** is genuinely required, beyond
  the gate. (This corrected the project's earlier belief that the reverse was "a
  mechanical mirror — the math is done.")

## The dividing line, in one sentence

Under reflection, β-contraction preserves convergence (`obsConv_refine_forward`,
proved, under a binder), but the contractum can be strictly more defined than the
redex (Obstruction B), so β is a **refinement everywhere and an equivalence exactly
under gate + purity + depth budget** — conditions shown necessary by A, B, C, not
artifacts of the proof.

## What is open

The **full** conditional `.lam` congruence — the backward direction assembled for an
arbitrary context, completing `obsConv_refine_forward` to a two-sided `CtxEquiv` under
`.lam` — is unproved. The redex-proper crux is in hand
(`frameβ_redex_letE_evalRevB`); the remaining open core is a value-level **em-bound
invariant** (a heap/env predicate bounding closure-body em-depth, plus its
preservation through `eval`), after which the budgeted mutual tower, the discharge of
the budgeted reverse obligation, and the lift to `Ctx.plug_cong_master`-to-`.lam`
follow. Detailed scope: `REVERSE.md`. The binder case is thus settled as a **dividing
line** (forward congruence + three obstructions + the redex-proper crux), not yet as a
closed equivalence.

## Scope

This is one specific reflective calculus (the artifact's Black-style tower) under
specific conditions — a statement about *its* β, not a universal claim over all
reflective languages. For the complementary half of the artifact — the
safety/governance layer, where the gate keeps the substrate conservatively-extending
(CE-coherent) under reflective programs (`eval_tower_safe`,
`approvedPolicy_soundForCE_weak_strong`, `CE_weak_strong_trans`, the `multn` worked
example) — see `LeanBlack/Public.lean`.
