# The reverse simulation: `ReverseSimβ` is false (Obstruction C), and the conditional path

**Status (2026-06-14): `ReverseSimβ` as stated is false — now machine-checked
(`reverseSimβ_false`) — and the conditional path to the `.lam` equivalence is scoped
and de-risked.** This file was originally written as if `ReverseSimβ` were "the one
remaining obligation, a mechanical mirror of `frameβ_tower` — the math is done." That
framing was wrong. The same depth/gate obstruction that makes β only a *conditional*
equivalence (`beta_not_unconditional_CtxEquiv`, `CtxEquiv.lean` §4) is **fatal** to
`ReverseSimβ`, because the reverse simulation is b-side-driven. The recursive reverse
eval cases are proved (the down payment); the `.app`-root case is blocked under the
*current* statement by a missing depth-budget side condition — but that condition is
the known one (`CtxEquiv.lean` §5), and "The path to the prize" below shows the root
closes under it without new machinery.

## Why `ReverseSimβ` is false as stated

```lean
def ReverseSimβ : Prop :=
  ∀ (k : Nat) (pt : PolicyTable) (lvl : Nat) (ea eb : Expr)
    (va vb : Env) (Sa Sb : TowerState) (rb : Val) (Sb' : TowerState),
    BetaRel ea eb → Pure ea = true → PolicyTableRespectsBisimT pt →
    WFCtxTβ va vb Sa Sb lvl → BReady Sb →
    eval k pt lvl eb vb Sb = some (rb, Sb') →
    ∃ (k' : Nat) (ra : Val) (Sa' : TowerState),
      eval k' pt lvl ea va Sa = some (ra, Sa') ∧ ValVisβ ra rb Sa'.heap Sb'.heap
```

It quantifies over the eval level `lvl` with premises `WFCtxTβ … lvl` and
`BReady Sb` only, and **neither bounds `lvl`**:
- `WFCtxTβ` (`LamBetaReflect.lean`) has no field constraining `level`.
- `BReady := BuiltinReadyAll ∧ PureHeap`, and
  `BuiltinReadyAll T := maxDepth ≤ T.levels.length ∧ ∀ L, L+1 < maxDepth →
  builtinBaseApplyAt L T` — it forces a full (≥ `maxDepth = 16`) tower with gates
  at levels `0…14`, but says **nothing** about the eval level `lvl`.

So instantiate at `lvl = maxDepth - 1 = 15`, with the Wand pair of
`beta_not_unconditional_CtxEquiv`:
```
ea = .app [.lam ["x"] (.var "x"), .num 0]    -- redex (Pure, BetaRel-related to eb)
eb = .letE "x" (.num 0) (.var "x")           -- its contractum
```
- **b-side converges.** `eval … eb …` reduces by `.letE` (alloc `0`, look up `x`);
  it never materializes, so it returns `(.num 0, …)` at `lvl = 15`.
- **a-side cannot.** `eval … ea …` routes the apply through `applyVia`, whose first
  act is `materialize (lvl+1) = materialize 16 = none` (`16 ≥ maxDepth`,
  *independent of `levels.length`*). So the redex returns `none` for **every** fuel
  `k'` (`eval_app_depth_none` / `applyVia_depth_none` / `app_lam_redex_depth`).

The premises hold at `lvl = 15` for a 16-level `BReady` tower while the
conclusion's a-side existential cannot — so `ReverseSimβ` is false. This is exactly
`beta_not_unconditional_CtxEquiv` (same pair distinguished at `level 15`) lifted to
the `BReady` setting; adding levels does not let the redex fire, because
`materialize 16 = none` regardless. **This is now machine-checked:
`reverseSimβ_false : ¬ ReverseSimβ` (`LamBetaReflect.lean`), the witness above on a
full `buildTower 16`, axiom-clean and CI-audited in `AxiomAudit.lean`.** It is the
**third impossibility result**, alongside Obstructions A and B.

**Why the forward FL escapes.** `frameβ_eval_FL` carries the *same* premises yet is
proved, because it is **a-side-driven**: when the a-side redex converges it
*supplies* the depth margin (`app_lam_redex_depth : … → level+1 < maxDepth`). The
reverse is b-side-driven by the contractum, which supplies no margin. The asymmetry
is precise: `.em` materializes `(level+1)` on *both* sides (so at bad depth both
diverge — the reverse `.em` case is then vacuous, and is proved), whereas the
redex/contractum `.app` pair materializes on the a-side only.

## What is proved (sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound})

Every reverse clause's machinery **except the `.app` root**:
- Leaves: `frameβ_{num,bool,lam,quote,var,set,installPolicy}_caseRev`.
- Reverse `evalList`: `frameβ_evalList_evalRev`.
- Reverse `applyDirect`: `frameβ_applyDirect_evalRev` (+ `rev_applyDirect_upgrade`).
- Reverse `applyVia`: `frameβ_applyVia_evalRev` (+ `rev_applyVia_upgrade`).
- Recursive eval cases: `frameβ_{ifte,seq,letE,em,primApp}_evalRev`, and the
  structural `.app` sub-case `frameβ_app_structural_evalRev`.
- Determinism `eval/evalList/applyVia/applyDirect_det`; the reverse `ValVisβ`
  inversions and value foundations.

These are the genuine recursive reverse work and carry over unchanged to any
corrected statement (except the `.app` root).

## What is blocked

- The `.app` **root** case (redex ↦ `.letE` contractum): not provable as a clause
  of the current `FrameβEvalStmtRev` (no depth margin). `gate_letE_to_redex_anyfuel`
  needs `level+1 < maxDepth`, which the driving b-side `.letE` does not supply.
- Hence the eval assembler `frameβ_eval_stepRev`, the mutual tower
  `frameβ_tower_rev`, and the discharge of `ReverseSimβ` cannot be written.
- Consequently `obsConv_refine_backward` / `obsConv_iff_beta` (which take
  `ReverseSimβ` as a *hypothesis*) stay un-instantiable, and the `.lam` headline via
  this route is not reached.

## The path to the prize (the conditional `.lam` equivalence)

The obstruction is now pinned (Obstruction C, machine-checked). The reverse is **not**
a dead end — it is conditional, and the condition is the one `CtxEquiv.lean` §5 and
`contextual_beta_pure` already name. Concretely:

**1. The right side condition is a depth *budget*, not a flat margin.** Add to
`FrameβEvalStmtRev` a premise of the form `level + emDepth exp_a < Tower.maxDepth`
(an `Expr.emDepth`, mirroring the existing `Ctx.emDepth`). The quantity
`level + emDepth` is **invariant under `.em`** — `.em` recurses at `level+1` on a body
of `emDepth - 1`, so the sub-call's budget equals the parent's. A flat
`level+1 < maxDepth` does *not* thread (it would need `level+2 < maxDepth` under `.em`);
the budget does. This is exactly `contextual_beta_at_start`'s `C.emDepth + 1 < maxDepth`
premise, now carried into the reflective (`.lam`) frame.

**2. The `.app` root closes under the budget without the `+2` problem.** The earlier
worry — `gate_letE_to_redex` raises the redex's fuel `+2` over the contractum, so a
tower-mirror reverse would need IHs at `n+2` while the induction gives `n` — is
**avoidable**. Don't convert contractum↦redex via `gate_letE_to_redex`. Instead
reconstruct the a-side redex *directly* from the IHs the mutual tower already provides:
the b-side contractum `let x=V_b in B_b` (fuel `n+1`) internally evaluates `V_b`
(fuel `≤ n`) and `B_b` (fuel `n`) in the alloc-extended context; the **reverse `eval`
IH on the operand** gives the a-side `V_a` (+`ValVisβ`), the **reverse `eval` IH on the
body** gives the a-side `B_a` run in the matching alloc-extended context, and the redex
is then *assembled* — `applyVia` on the closure (its `materialize (level+1)` succeeds
**because of the budget**) → `applyDirect` closure case → that same body run. Both the
alloc-context plumbing (`frameβ_letE_evalRev`) and the closure application
(`frameβ_applyDirect_evalRev`) are **already proved**; the redex's extra steps are
absorbed by the conclusion's `∃ k`. No `gate_letE_to_redex`, no `+2`, IHs at `n`.

**3. The down payment is in hand.** Everything in "What is proved" transfers to the
budgeted statement unchanged except the `.app` root (the recursive cases just thread
the budget to their sub-calls; the budget invariant makes that mechanical, and `.em`
is already vacuous-or-fine). So the remaining work is: define `Expr.emDepth`; add the
budget premise; prove the `.app` root by §2; thread the budget through the assembler;
re-run the mutual tower and discharge the (now true) budgeted `ReverseSimβ⁺`; lift to
`obsConv_iff_beta` and `Ctx.plug_cong_master`-to-`.lam`.

## Status summary

- **Salvage (done):** the dividing line is fully machine-checked — forward `.lam`
  refinement (`obsConv_refine_forward`) + three axiom-audited impossibilities
  (`lam_EvalEquiv_congruence_fails`, `beta_not_unconditional_CtxEquiv`,
  `reverseSimβ_false`). β under a reflective binder is a *strict refinement*, an
  equivalence only under the gate + pure + depth budget.
- **Prize (scoped, de-risked):** the conditional `.lam` equivalence under the budget,
  via §1–§3 above. No longer "mechanical mirror" and no longer "false" — a bounded,
  reuse-heavy effort whose one genuinely new lemma (the `.app` root, §2) has a clear
  proof plan that needs no machinery the reverse build doesn't already have.
