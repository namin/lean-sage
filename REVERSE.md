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

**2. The `.app` root — redex-proper case PROVED** (`frameβ_redex_letE_evalRevB`,
`LamBetaReflect.lean`, sorry-free, axioms ⊆ {propext, Classical.choice, Quot.sound}).
For a *literal*-λ redex `(λx.body_a) v_a` against its contractum `let x = v_b in body_b`
(`body_a ~β body_b`, `v_a ~β v_b`), b-side-driven, under the budget:
- unfold the b-side `.letE` (operand + body run at fuel `≤ n`), mirroring
  `frameβ_letE_evalRev`'s alloc-context construction;
- **operand**/**body** via the budgeted IH `ih_eval` (`v_a` from `v_b`; `body_a` from
  `body_b` in the alloc-extended context) — the body budget is **trivial** here because
  `body_a` is a *syntactic sub-term* of the redex (`body_a.emDepth ≤
  max body_a.emDepth v_a.emDepth`);
- **assemble** with `eval_beta_builtin` — the equation `eval (m+3) (.app [.lam x B, V])
  = eval m B (alloc-extended)` under the standard gate — which **sidesteps the raw
  `applyVia`/`applyDirect`/`allocStep` plumbing** and makes the apply's alloc *literally*
  the context built for the body IH (no `EnvVisβ_allocStep_chain` reconciliation);
- the a-side gate `builtinBaseApplyAt level T_a1` that `eval_beta_builtin` needs is **not**
  on the b-side path (the contractum skips the gate), so it is recovered **cross-side**
  from `BReady T_b` through the operand-output `WFCtxTβ` — the new helper
  `builtinBaseApplyAt_cross_of_WFCtxTβ` (`level_count_eq` + `level_envs_visβ` +
  `ValVisβ_builtinBaseApply_iff`);
- the margin `level+1 < maxDepth` + `T_a1.levels.length > level+1` come from the budget;
  fuel is `max k_v k_body + 3`. **No `gate_letE_to_redex`, no `+2`.**

This is the actual content of the `.lam` headline's backward root: the contracted redex
in `C.plug ((λx.B) V)` is **always a literal λ**, so the redex-proper case covers it.

**Remaining generality (not needed for the headline):** the *non-literal* function case
(`f ~β λ` but `f` not literally a λ) would additionally need `f` reverse-simulated
against a constructed free λ-value, plus a closure-body bound `B_a.emDepth ≤ f.emDepth`
(true because closures freeze bodies and `f ~β λ` forces the λ syntactic in `f`; or via
a `BuiltinReadyN`-style runtime budget). This is extra generality for the fully general
clause, orthogonal to the headline.

**3. Down payment + the genuine open core.** Proved: the structural/recursive reverse
eval cases, `evalList`/`applyDirect`/`applyVia`, and now the **redex-proper root**.

The remaining assembly is **not** mechanical (an earlier draft of this file said it was
— that was wrong). The budgeted eval tower must also budget the apply machinery: eval's
`.app`-structural and `.primApp` cases dispatch through `applyVia`/`applyDirect`, whose
closure case runs the **closure's body** via the eval IH. To invoke the *budgeted* eval
IH there, the body's `emDepth` must be bounded — but a closure body is **not a syntactic
sub-term of the source**, so the static `exp.emDepth` budget cannot bound it (it came
from an earlier `.lam`, possibly via the environment). For the redex-proper root this was
free (literal λ ⟹ body is a sub-term); for the general apply machinery it is not.

The clean fix is a **value-level em-bound invariant** — a heap/env predicate (à la
`PureHeap` / `BuiltinReadyN`: "every closure in scope has a body within the depth
budget") **plus its preservation through `eval`** (a lemma family across all 13 eval
cases, mirroring `allPureIndep` / `PureHeap` preservation). That invariant is the genuine
remaining content — exactly why §5 calls `.lam` the open core; it bottoms out here. After
it: the budgeted mutual tower, discharge of `ReverseSimβ⁺`, and lift to
`obsConv_iff_beta` / `Ctx.plug_cong_master`-to-`.lam`.

## Status summary

- **Salvage (done):** the dividing line is fully machine-checked — forward `.lam`
  refinement (`obsConv_refine_forward`) + three axiom-audited impossibilities
  (`lam_EvalEquiv_congruence_fails`, `beta_not_unconditional_CtxEquiv`,
  `reverseSimβ_false`). β under a reflective binder is a *strict refinement*, an
  equivalence only under the gate + pure + depth budget.
- **Prize (crux PROVED, open core scoped):** `Expr.emDepth`, the budgeted clause
  `FrameβEvalStmtRevB`, and — the hard part — the **redex-proper reverse `.app` root**
  `frameβ_redex_letE_evalRevB` are all in and build green (sorry-free, axiom-clean). The
  `+2` is dissolved (assemble via `eval_beta_builtin`, gate recovered cross-side by
  `builtinBaseApplyAt_cross_of_WFCtxTβ`), and this is exactly the case the `.lam`
  headline's backward root needs (the contracted redex is always a literal λ). The
  remaining open core (§3) is the **value-level em-bound invariant + its `eval`
  preservation** — needed to budget the apply machinery's closure bodies — then the
  budgeted tower, discharge of `ReverseSimβ⁺`, and lift to `Ctx.plug_cong_master`-to-`.lam`.
