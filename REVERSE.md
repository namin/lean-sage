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

**Foundations (done, in `LamBetaReflect.lean`, `lake build` green):** `Expr.emDepth`
(+ `Expr.emDepthList`) — the reflective analog of `Ctx.emDepth`, max over sub-terms;
and `FrameβEvalStmtRevB`, the budgeted reverse eval clause = `FrameβEvalStmtRev` plus
the premise `level + exp_a.emDepth + 1 < Tower.maxDepth`.

**1. The budget threads.** `level + e.emDepth + 1 < maxDepth` is **invariant under
`.em`** (`.em` recurses at `level+1` on a body of `emDepth − 1`, keeping the sum), and
at the `.app` root it gives the margin `level + 1 < maxDepth` even when the redex has
`emDepth 0` (the `+1`). A flat `level+1 < maxDepth` does *not* thread (it would need
`level+2 < maxDepth` under `.em`). At `level 0` this is exactly
`contextual_beta_at_start`'s `C.emDepth + 1 < maxDepth`.

**2. The `.app` root, by direct reconstruction (no `gate_letE_to_redex`, no `+2`).**
The b-side drives with the contractum `let x = V_b in B_b` (fuel `n+1`); unfolding it
gives the b-side `V_b` (fuel `≤ n`) and `B_b` (fuel `n`) runs. Reconstruct the a-side
redex `(.app [f, a])` (where `f ~β λx.body'`, `a ~β V_b`) thus:
- **function `f`:** *form* the b-side λ-value `L_b := .lam [x] body'` (`body'` is in hand
  from the contractum) — its eval is **free at any fuel ≥ 1** (`eval n L_b = closure`),
  so the **reverse `eval` IH on `(f, L_b)` at b-side fuel `n`** reconstructs the a-side
  `eval f → fv_a` with `ValVisβ fv_a (closure x body' env_b)`; `ValVisβ_closure_inv`
  then gives `fv_a = .closure [x] B_a cenv_a`, `B_a ~β body'`, `cenv_a ~ env_b`. *This
  is what dissolves the `+2`* — exposing the b-side λ needs **no** `gate_letE_to_redex`
  (which would `+2` the fuel), because a λ is a value;
- **operand `a` / body `B_a`:** reverse `eval` IH on `(a, V_b)` and on `(B_a, body')` in
  the matching alloc-extended context (reusing `frameβ_letE_evalRev`'s context plumbing
  and `frameβ_applyDirect_evalRev`'s closure case);
- **assemble:** `eval (.app [f,a])` = eval `f` → `fv_a`, `evalList [a]`, then `applyVia`
  whose `materialize (level+1)` succeeds **by the budget** → `applyDirect` closure case
  → the `B_a` run; the redex's extra steps are absorbed by the conclusion's `∃ k`.

**Open subtlety (the one genuinely new lemma):** the body IH on `(B_a, body')` needs
`level + B_a.emDepth + 1 < maxDepth`, but `B_a` is the *closure's* body, not a syntactic
sub-term of the source `exp_a`. It is bounded — `B_a.emDepth ≤ f.emDepth` because
closures freeze bodies verbatim and `f ~β λx.body'` forces the λ to occur in `f`
syntactically (a var cannot β-reduce to a λ; β-reduction only rearranges existing
syntax, never raising `emDepth`). Turning that into a lemma (`eval`-produced closure
bodies have `emDepth ≤` the source's) is the crux's real content — Obstruction A
("closures freeze bodies") working *for* us. This may instead motivate a **runtime**
budget (a `BuiltinReadyN`-style state invariant that closures in scope are em-budgeted),
the form the forward `contextual_beta_pure` already uses; which representation is
cleanest is the open design call.

**3. The down payment is in hand.** Everything in "What is proved" transfers to the
budgeted clause unchanged except the `.app` root (recursive cases thread the budget to
sub-calls; the invariant makes that mechanical; `.em` stays vacuous-or-fine). Remaining
work: prove the `.app` root by §2 (+ the closure-body-`emDepth` lemma); thread the
budget through the assembler; re-run the mutual tower; discharge the budgeted
`ReverseSimβ⁺`; lift to `obsConv_iff_beta` and `Ctx.plug_cong_master`-to-`.lam`.

## Status summary

- **Salvage (done):** the dividing line is fully machine-checked — forward `.lam`
  refinement (`obsConv_refine_forward`) + three axiom-audited impossibilities
  (`lam_EvalEquiv_congruence_fails`, `beta_not_unconditional_CtxEquiv`,
  `reverseSimβ_false`). β under a reflective binder is a *strict refinement*, an
  equivalence only under the gate + pure + depth budget.
- **Prize (foundations coded, crux scoped):** `Expr.emDepth` and the budgeted clause
  `FrameβEvalStmtRevB` are in and build green. The `.app` root has a worked proof plan
  (§2) that **dissolves the `+2`** (reverse-simulate the redex function against a
  free fuel-1 λ-value, no `gate_letE_to_redex`). The one genuinely new lemma left is
  the closure-body `emDepth` bound (or its runtime-budget alternative) — the real
  remaining content, then the mechanical thread-through + tower + discharge + lift.
