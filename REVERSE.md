# The reverse simulation: the `.lam` headline is blocked on `ReverseSimβ`

**Status (2026-06-14): `ReverseSimβ` as currently stated is false.** This file was
originally written as if `ReverseSimβ` were "the one remaining obligation, a
mechanical mirror of `frameβ_tower` — the math is done." That framing is wrong.
The same depth/gate obstruction that makes β only a *conditional* equivalence
(`beta_not_unconditional_CtxEquiv`, `CtxEquiv.lean` §4) is **fatal** to
`ReverseSimβ`, because the reverse simulation is b-side-driven. The recursive
reverse eval cases are proved; the `.app`-root case, the assembler, the mutual
tower, and the discharge are blocked — not by bookkeeping, but by a missing
depth-budget side condition (the genuine open core, `CtxEquiv.lean` §5).

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
`materialize 16 = none` regardless. *(The argument is rigorous and reuses the
machine-checked `beta_not_unconditional_CtxEquiv` mechanism, but is not yet itself a
machine-checked `¬ ReverseSimβ`; see “Definitive next step”.)*

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

## The real open core (= `CtxEquiv.lean` §5)

Closing the reverse is **not** a mechanical mirror. It needs the depth-budget side
condition §5 already identifies ("standard gate **with depth margin** + pure"):
- A naive `level+1 < maxDepth` premise on `FrameβEvalStmtRev` does **not** thread
  through `.em`, which recurses at `level+1` (and would then need `level+2 <
  maxDepth`). The condition must be a *budget* that decreases through reflective
  nesting — exactly the "em-nesting to any depth in the tower bound" that
  `contextual_beta_pure` carries for the lam-free cases.
- So the reverse's completion is coupled to the same reflective depth-budget problem
  that makes β conditional in the first place — it is open core, not packaging.

## Definitive next step

Either:
- **(a)** machine-check `¬ ReverseSimβ` — a third impossibility result alongside
  `lam_EvalEquivAt_forces_empty` and `beta_not_unconditional_CtxEquiv`; needs a
  16-level `BReady` witness tower at `level 15` (the redex/contractum pair above); or
- **(b)** restate `ReverseSimβ` / `FrameβEvalStmtRev` with the §5 depth-budget side
  condition and complete the `.app` root + assembler + tower + discharge under it.
  Everything in “What is proved” transfers to (b) unchanged except the `.app` root.
