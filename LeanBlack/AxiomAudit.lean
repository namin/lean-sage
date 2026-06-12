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
import LeanBlack.GovChain

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
