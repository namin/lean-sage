/-
  lean-sage: Axiom audit — CI-enforced axiom footprint of the
  public theorem surface.

  The `sorry` grep in the success criterion cannot see axioms
  introduced by tactics (`native_decide` injects a trusted-compiler
  axiom, found in exactly this way during an audit). Each
  `#guard_msgs` below pins a headline theorem's axiom list: if a
  future change introduces any axiom beyond the three standard ones
  (`propext`, `Classical.choice`, `Quot.sound`), the build of this
  module fails.

  Run via `lake build LeanBlack.AxiomAudit` (included in the root
  build).
-/

import LeanBlack.Soundness
import LeanBlack.Policies
import LeanBlack.ProofBased
import LeanBlack.Compose
import LeanBlack.ContextualBetaPure
import LeanBlack.CtxEquiv
import LeanBlack.LamBetaReflect
import LeanBlack.GovChain
import LeanBlack.GuardedExt
import LeanBlack.GuardedExtApproval
import LeanBlack.GuardedExtStack
import LeanBlack.SyntaxObserver

open LeanBlack

/-- info: 'eval_tower_safe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eval_tower_safe

/-- info: 'multnExact_soundForCE_first_install_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multnExact_soundForCE_first_install_tower

/-- info: 'safeEvolution_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms safeEvolution_necessary

/-- info: 'LeanBlack.wand_defeated_existential_gated_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.wand_defeated_existential_gated_beta

/-- info: 'LeanBlack.approvedPolicy_soundForCE_weak_strong' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.approvedPolicy_soundForCE_weak_strong

/-- info: 'LeanBlack.CE_weak_strong_trans' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.CE_weak_strong_trans

/-- info: 'contextual_beta_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms contextual_beta_pure

/-- info: 'contextual_beta_at_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms contextual_beta_at_start

-- `.lam` dividing line. Positive half: the forward refinement holds — under the gate,
-- the redex refines its contractum (`obsConv_refine_forward`, `LamBetaReflect.lean`).
-- Negative half: three impossibilities pin why the converse is *not* closable in any
-- naive frame. A and B (`CtxEquiv.lean`) force the ground coarsening and the side
-- conditions; C (`LamBetaReflect.lean`) shows the backward `.lam` simulation
-- `ReverseSimβ`, stated with the all-levels gate but no depth margin, is false — so the
-- gate alone is insufficient for the reverse. Together: β under a reflective binder is a
-- strict refinement, an equivalence only under the gate + pure + depth budget.
/-- info: 'LeanBlack.obsConv_refine_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.obsConv_refine_forward

/-- info: 'LeanBlack.lam_EvalEquiv_congruence_fails' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.lam_EvalEquiv_congruence_fails

/-- info: 'LeanBlack.beta_not_unconditional_CtxEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.beta_not_unconditional_CtxEquiv

/-- info: 'LeanBlack.reverseSimβ_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.reverseSimβ_false

/-- info: 'LeanBlack.chain_CE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.chain_CE

/-- info: 'LeanBlack.govReach_CE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.govReach_CE

/-- info: 'LeanBlack.pureEvalExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.pureEvalExt

/-- info: 'LeanBlack.wand_defeated_existential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.wand_defeated_existential

/-! ## Guarded-extension family (`GuardedExt.lean`, `GuardedExtApproval.lean`)

The master theorem, the per-guard obligations' instances, the
family-level impossibility results, and the approval packaging are
all kernel-only. (`DemoGuarded.lean`'s two *admission facts* use
`native_decide`, matching `Demo.lean`'s practice — they are structural
Bool checks on concrete probe values, outside this audited surface.) -/

/-- info: 'guardedExt_soundForCE_first_install_tower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardedExt_soundForCE_first_install_tower

/-- info: 'guardSpec_numq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardSpec_numq

/-- info: 'guardSpec_boolq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardSpec_boolq

/-- info: 'no_guardSpec_primq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_guardSpec_primq

/-- info: 'no_guardSpec_closureq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms no_guardSpec_closureq

/-- info: 'multn_admits_guardedExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms multn_admits_guardedExt

/-- info: 'LeanBlack.guardedExtApproval_at_proof' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanBlack.guardedExtApproval_at_proof

/-! ## Stacking (`GuardedExtStack.lean`)

The second-install conservative-extension theorem for disjoint guards,
and its demo-facing front end, are kernel-only. -/

/-- info: 'LeanBlack.guardedExt_stack_soundForCE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardedExt_stack_soundForCE

/-- info: 'LeanBlack.guardedExt_stack_soundForCE_weak_strong_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardedExt_stack_soundForCE_weak_strong_at

/-- info: 'LeanBlack.guardsDisjoint_num_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guardsDisjoint_num_bool

/-! ## Syntax-observer experiment — the syntax-observation / β dividing line

A top-level syntax-sensitive observation extension. The *same* lam-free,
pure-sided `Ctx` equates the β pair under the base evaluator
(`base_equates_in_syntaxTagCtx`, from `wand_beta_ctx_pure_at_start`) yet
separates it — with distinct ground observations — under `evalF`: the
**semantic index** is load-bearing, not any restriction on `Ctx`. A
Wand-style counterexample; it proves nothing about `CE_weak_strong`. See
`LeanBlack/SyntaxObserver.lean` for the precise (deliberately modest)
scope. -/

-- The two halves of `syntaxTagCtx_equated_by_eval_but_separated_by_evalF`
-- (whose own long name wraps the `#print axioms` message); together they
-- pin the bundle's footprint.
/-- info: 'LeanBlack.base_equates_in_syntaxTagCtx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms base_equates_in_syntaxTagCtx

/-- info: 'LeanBlack.syntaxObserver_separates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms syntaxObserver_separates

/-- info: 'LeanBlack.evalF_agrees_off_operative_root' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms evalF_agrees_off_operative_root
