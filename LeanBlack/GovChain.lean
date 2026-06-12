/-
  lean-sage: GovChain — selective proof-bearing admission, and
  composition of admission chains.

  This file strengthens the composition story (headline #6,
  `CE_weak_strong_trans`) so it applies to *real* admission
  sequences, and packages a corollary about sequences that
  interleave gate replacements. Read the scope notes below — the
  packaged corollary is deliberately modest.

  What is substantive here:

  - the **selective admission layer**
    (`ApprovedModificationAt` / `approvedPolicyAt`): approvals whose
    certificates pin only the cells they read, so they remain
    matchable and consumable after later admissions rewrite the
    `base-apply` cell;
  - **`chain_CE`**: n-link composition of selective certificates at
    per-link snapshots;
  - the **runtime inversions** of the `.set` and `installPolicy`
    clauses.

  What is packaging: `GovReach` / `govReach_CE` quantify over
  interleavings of admissions and gate replacements and thread the
  above. The `regate` rule *assumes* the incoming gate is sound;
  that assumption is discharged by construction only for
  kernel-built `approvedPolicyAt` gates
  (`approvedPolicyAt_SoundForCEAt` — no admissible gate exists
  without kernel-checked certificates). The chain's firing
  condition at a test state (`CertsFire`) is a per-instance
  obligation (discharged by the fresh-cells discipline for the
  concrete links here). None of this is a whole-program-trace
  theorem in the style of `eval_tower_safe` — see `SCOPE.md` for
  the dividing line and why it is principled.

  ## Why the chain currency is the *selective* certificate

  `CE_weak_strong` certificates carry a `HeapPrefix` premise bound
  to their admission-moment heap. Two successive admissions write
  the same `base-apply` cell, so no later test state can content-
  extend *both* snapshots — full-prefix certificates from different
  admission moments can never fire together, and
  `CE_weak_strong_trans` (which composes at a *common* reference
  heap) cannot bridge them. The selective predicate
  `CE_weak_strong_at` (`HeapAgree.lean`) only pins the cells a
  certificate actually reads; under the `installMultnOneUp`-style
  discipline (captured cells allocated fresh, disjoint from the
  `base-apply` cell), every link's cells survive all later
  admissions, and the whole chain fires at the real post-chain
  states. So:

  1. `AdmissionCert` / `ChainOk` / `chain_CE` — n-link composition
     of selective certificates at *per-link* reference snapshots.
  2. `ApprovedModificationAt` / `approvedPolicyAt` — proof-bearing
     admission in selective form: the gate's constructor demands a
     `CE_weak_strong_at` proof, so gate soundness
     (`approvedPolicyAt_SoundForCEAt`) costs nothing.
  3. `GovReach` / `govReach_sound` / `govReach_CE` — the governed
     evolution: any reachable `(gate, apply)` configuration, through
     any number of admissions and proof-bearing gate swaps, has its
     apply value certificate-chained back to the original.

  The runtime tie-in: a `.set "base-apply"` admitted under
  `approvedPolicyAt` is a `GovReach.modify` step (the runtime's
  `MutationCtx` instantiates `ctx`); an `installPolicy` that swaps
  in another `approvedPolicyAt ...` gate is a `GovReach.regate`
  step whose soundness obligation is discharged by
  `approvedPolicyAt_SoundForCEAt` — i.e., by the kernel having
  checked the new gate's approvals.
-/

import LeanBlack.Compose
import LeanBlack.HeapAgree
import LeanBlack.IdentityDelegate

namespace LeanBlack

/-! ## Reference-heap monotonicity for the selective predicate -/

/-- `CE_weak_strong_at` is monotone in the reference heap: a
    certificate at snapshot `h₁` lifts to any longer heap that
    agrees with `h₁` on the certificate's cells. -/
theorem CE_weak_strong_at_mono
    {level : Nat} {indices : List Nat} {h₁ h₂ : Heap} {old new : Val}
    (h_len : h₁.length ≤ h₂.length)
    (h_agree : HeapAgreeAt indices h₁ h₂)
    (h : CE_weak_strong_at level indices h₁ old new) :
    CE_weak_strong_at level indices h₂ old new := by
  intro fuel ptable op operands T r T' h_len' h_agree'
  exact h fuel ptable op operands T r T'
    (Nat.le_trans h_len h_len') (h_agree.trans h_agree')

/-! ## Layer 1 — chains of selective certificates -/

/-- One link of an admission chain: a kernel-checked selective
    conservative-extension certificate, together with the cells and
    heap snapshot it is bound to. -/
structure AdmissionCert (level : Nat) where
  indices : List Nat
  heap    : Heap
  oldVal  : Val
  newVal  : Val
  proof   : CE_weak_strong_at level indices heap oldVal newVal

/-- The links form a chain from `a` to `c`: each link's `oldVal` is
    the previous link's `newVal`. -/
def ChainOk (level : Nat) : List (AdmissionCert level) → Val → Val → Prop
  | [],           a, c => c = a
  | cert :: rest, a, c => cert.oldVal = a ∧ ChainOk level rest cert.newVal c

/-- A chain extends by one link at the end. -/
theorem ChainOk.snoc {level : Nat} {certs : List (AdmissionCert level)}
    {a b : Val} (h : ChainOk level certs a b)
    (cert : AdmissionCert level) (h_old : cert.oldVal = b) :
    ChainOk level (certs ++ [cert]) a cert.newVal := by
  induction certs generalizing a with
  | nil =>
      simp only [ChainOk] at h
      subst h
      exact ⟨h_old, rfl⟩
  | cons c cs ih =>
      obtain ⟨h_head, h_rest⟩ := h
      exact ⟨h_head, ih h_rest⟩

/-- The firing condition for a chain at a test state: every link's
    snapshot is within bounds, its cells agree, and its installed
    value is valid. -/
def CertsFire (level : Nat) (certs : List (AdmissionCert level))
    (T : TowerState) : Prop :=
  ∀ cert ∈ certs,
    cert.heap.length ≤ T.heap.length ∧
    HeapAgreeAt cert.indices cert.heap T.heap ∧
    ValValid cert.newVal T.heap

/-- **Chain composition.** A chain of selective certificates from
    `a` to `c` composes: at any test state where every link fires,
    every successful call through `a` is matched by a call through
    `c` with a weakly-bisimilar result. Generalizes
    `CE_weak_strong_trans` from two links at a common reference
    heap to any number of links at per-link snapshots. -/
theorem chain_CE (level : Nat) :
    ∀ (certs : List (AdmissionCert level)) (a c : Val),
    ChainOk level certs a c →
    ∀ (fuel : Nat) (ptable : PolicyTable) (op : Val) (operands : List Val)
      (T : TowerState) (r : Val) (T' : TowerState),
      CertsFire level certs T →
      HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
      ValValid a T.heap →
      PolicyTableRespectsBisimT ptable →
      (∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p) →
      (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
      (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
      (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
      HeapDeep T.heap → ValDeep op T.heap → ListValDeep operands T.heap →
      (∀ n env, T.envAt? n = some env → EnvDeep env T.heap) →
      PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable →
      (∀ n p, T.policyAt? n = some p →
         PolicyRespectsShift T.heap.length [op, listToVal operands] p) →
      callAsBaseApply fuel ptable level a op operands T = some (r, T') →
      ∃ fuel' T'' r',
        callAsBaseApply fuel' ptable level c op operands T = some (r', T'') ∧
        ValVis_weak r r' T'.heap T''.heap ∧
        T'.policyAt? level = T''.policyAt? level ∧
        HeapValid T''.heap ∧
        T.heap.length ≤ T''.heap.length := by
  intro certs
  induction certs with
  | nil =>
      intro a c h_chain fuel ptable op operands T r T'
        _h_fire h_heap h_op h_operands h_va h_pt h_pol h_envs h_pols h_envvis
        _h_heap_deep _h_op_deep _h_operands_deep _h_levels_deep
        _h_pt_shift _h_pol_shift h_call
      simp only [ChainOk] at h_chain
      subst h_chain
      obtain ⟨h_heap', h_r', h_mono⟩ :=
        callAsBaseApply_preserves
          (hh := h_heap) (h_levs := h_envs) (h_resp_all := h_pols)
          (h_bisim := h_envvis) (h_pt := h_pt) (h_pol_resp_at := h_pol)
          (hv_base := h_va) (hv_op := h_op) (hv_operands := h_operands)
          (h_call := h_call)
      refine ⟨fuel, T', r, h_call, ?_, rfl, h_heap', h_mono⟩
      intro n
      have h_strong := ValVis_aux_self_extend n r T'.heap [] h_heap' h_r'
      have h_strong' : ValVis_aux n r r T'.heap T'.heap := by simpa using h_strong
      exact ValVis_aux_to_weak n r r T'.heap T'.heap h_strong'
  | cons cert rest ih =>
      intro a c h_chain fuel ptable op operands T r T'
        h_fire h_heap h_op h_operands h_va h_pt h_pol h_envs h_pols h_envvis
        h_heap_deep h_op_deep h_operands_deep h_levels_deep
        h_pt_shift h_pol_shift h_call
      obtain ⟨h_old_eq, h_chain_rest⟩ := h_chain
      obtain ⟨h_len_cert, h_agree_cert, h_new_valid⟩ := h_fire cert (by simp)
      have h_fire_rest : CertsFire level rest T :=
        fun cert' h_mem => h_fire cert' (by simp [h_mem])
      -- Fire the head certificate at T.
      have h_va' : ValValid cert.oldVal T.heap := h_old_eq ▸ h_va
      obtain ⟨fuel_b, T_b, r_b, h_call_b, h_vis_ab, h_pol_eq_ab, h_heap_b, h_len_b⟩ :=
        cert.proof fuel ptable op operands T r T'
          h_len_cert h_agree_cert
          h_heap h_op h_operands h_va' h_new_valid h_pt h_pol h_envs h_pols h_envvis
          h_heap_deep h_op_deep h_operands_deep h_levels_deep
          h_pt_shift h_pol_shift (h_old_eq ▸ h_call)
      -- Chain the rest from cert.newVal, at the same test state T.
      obtain ⟨fuel_c, T_c, r_c, h_call_c, h_vis_bc, h_pol_eq_bc, h_heap_c, h_len_c⟩ :=
        ih cert.newVal c h_chain_rest fuel_b ptable op operands T r_b T_b
          h_fire_rest h_heap h_op h_operands h_new_valid h_pt h_pol h_envs h_pols
          h_envvis h_heap_deep h_op_deep h_operands_deep h_levels_deep
          h_pt_shift h_pol_shift h_call_b
      exact ⟨fuel_c, T_c, r_c, h_call_c,
             ValVis_weak_trans h_vis_ab h_vis_bc,
             h_pol_eq_ab.trans h_pol_eq_bc, h_heap_c, h_len_c⟩

/-! ## Layer 2 — proof-bearing admission, selective form -/

/-- Decidable single-cell agreement between two heaps. -/
def cellAgreesB (h₁ h₂ : Heap) (i : Nat) : Bool :=
  match h₁[i]?, h₂[i]? with
  | some v₁, some v₂ => Val.beq v₁ v₂
  | none,    none    => true
  | _,       _       => false

theorem cellAgreesB_eq {h₁ h₂ : Heap} {i : Nat}
    (h : cellAgreesB h₁ h₂ i = true) : h₁[i]? = h₂[i]? := by
  revert h
  unfold cellAgreesB
  cases h₁[i]? <;> cases h₂[i]? <;> intro h
  · rfl
  · exact (Bool.false_ne_true h).elim
  · exact (Bool.false_ne_true h).elim
  · rename_i v₁ v₂
    rw [val_beq_eq v₁ v₂ h]

/-- A modification approved in selective form. As with
    `ApprovedModification`, the `proof` field is the load-bearing
    certificate — Lean's kernel refuses construction without it —
    but the certificate here is the chain-surviving
    `CE_weak_strong_at`. -/
structure ApprovedModificationAt where
  level   : Nat
  indices : List Nat
  heap    : Heap
  oldVal  : Val
  newVal  : Val
  proof   : CE_weak_strong_at level indices heap oldVal newVal

/-- Boolean match against a runtime mutation context: level match,
    snapshot within bounds, agreement at exactly the certificate's
    cells, and value match. Where `ApprovedModification.matches`
    demands a full content-prefix, this only pins the cells the
    proof reads — so an approval stays matchable after unrelated
    cells (including the `base-apply` cell itself) have changed. -/
def ApprovedModificationAt.matches
    (am : ApprovedModificationAt) (ctx : MutationCtx)
    (oldVal newVal : Val) : Bool :=
  decide (am.level = ctx.level) &&
  decide (am.heap.length ≤ ctx.heap.length) &&
  am.indices.all (cellAgreesB am.heap ctx.heap) &&
  Val.beq am.oldVal oldVal &&
  Val.beq am.newVal newVal

/-- The selective proof-bearing gate. -/
def approvedPolicyAt (approvals : List ApprovedModificationAt) : BlackPolicy :=
  fun ctx oldVal newVal =>
    approvals.any fun am => am.matches ctx oldVal newVal

/-- View a selective approval as a chain link. -/
def ApprovedModificationAt.toCert (am : ApprovedModificationAt) :
    AdmissionCert am.level :=
  { indices := am.indices, heap := am.heap,
    oldVal := am.oldVal, newVal := am.newVal, proof := am.proof }

/-- Soundness notion for gates in the selective discipline: every
    admission is backed by a selective certificate whose cells agree
    with the admission-moment heap. -/
abbrev BlackPolicy.SoundForCEAt (level : Nat) (p : BlackPolicy) : Prop :=
  ∀ ctx old new, p ctx old new = true →
    ∃ indices h_ref,
      CE_weak_strong_at level indices h_ref old new ∧
      h_ref.length ≤ ctx.heap.length ∧
      HeapAgreeAt indices h_ref ctx.heap

/-- **The selective gate is sound by construction.** Mirror of
    `approvedPolicy_soundForCE_weak_strong`: an admission only
    happens when some approval matches, and the approval carries its
    own kernel-checked certificate. No per-gate proof obligations
    remain — this is what makes gate *swaps* free below. -/
theorem approvedPolicyAt_SoundForCEAt
    (approvals : List ApprovedModificationAt) (level : Nat)
    (h_levels : ∀ am ∈ approvals, am.level = level) :
    BlackPolicy.SoundForCEAt level (approvedPolicyAt approvals) := by
  intro ctx old new h_admit
  unfold approvedPolicyAt at h_admit
  rw [List.any_eq_true] at h_admit
  obtain ⟨am, h_mem, h_match⟩ := h_admit
  unfold ApprovedModificationAt.matches at h_match
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h_match
  obtain ⟨⟨⟨⟨_h_lvl, h_len⟩, h_cells⟩, h_old_beq⟩, h_new_beq⟩ := h_match
  have h_old_eq : am.oldVal = old := val_beq_eq _ _ h_old_beq
  have h_new_eq : am.newVal = new := val_beq_eq _ _ h_new_beq
  have h_level : am.level = level := h_levels am h_mem
  subst h_old_eq; subst h_new_eq; subst h_level
  refine ⟨am.indices, am.heap, am.proof, h_len, ?_⟩
  intro i h_i
  exact cellAgreesB_eq (h_cells i h_i)

/-! ## Layer 3 — governed gate evolution

A `GovState` is a gate together with the apply value it governs.
`GovReach` is the reflexive-transitive evolution relation: at each
step, either the *current* gate admits a modification of the apply
value, or the gate itself is replaced — and the replacement must be
sound in the selective discipline, an obligation that
`approvedPolicyAt_SoundForCEAt` discharges for free when the new
gate is proof-bearing. -/

structure GovState where
  gate     : BlackPolicy
  applyVal : Val

inductive GovReach (level : Nat) : GovState → GovState → Prop
  /-- The starting configuration is reachable. -/
  | refl (s : GovState) : GovReach level s s
  /-- The current gate admits a modification of the apply value. -/
  | modify {s₀ s : GovState} (ctx : MutationCtx) (new : Val)
      (h_prev  : GovReach level s₀ s)
      (h_admit : s.gate ctx s.applyVal new = true) :
      GovReach level s₀ ⟨s.gate, new⟩
  /-- The gate itself is replaced by a new sound gate. For
      proof-bearing replacements (`approvedPolicyAt approvals`),
      the soundness obligation is discharged by
      `approvedPolicyAt_SoundForCEAt` — the kernel already checked
      the new gate's approvals. -/
  | regate {s₀ s : GovState} (g' : BlackPolicy)
      (h_prev  : GovReach level s₀ s)
      (h_sound : BlackPolicy.SoundForCEAt level g') :
      GovReach level s₀ ⟨g', s.applyVal⟩

/-- **Evolution invariant.** From a sound initial gate, every
    reachable configuration has a sound gate, and its apply value is
    connected to the original by a chain of kernel-checked
    certificates — one per admission, regardless of how often the
    gate was swapped in between. -/
theorem govReach_sound (level : Nat) {s₀ s : GovState}
    (h_sound₀ : BlackPolicy.SoundForCEAt level s₀.gate)
    (h_reach : GovReach level s₀ s) :
    BlackPolicy.SoundForCEAt level s.gate ∧
    ∃ certs : List (AdmissionCert level),
      ChainOk level certs s₀.applyVal s.applyVal := by
  induction h_reach with
  | refl =>
      exact ⟨h_sound₀, [], rfl⟩
  | modify ctx new _h_prev h_admit ih =>
      obtain ⟨h_gate_sound, certs, h_chain⟩ := ih
      obtain ⟨indices, h_ref, h_cert, _, _⟩ :=
        h_gate_sound ctx _ new h_admit
      exact ⟨h_gate_sound,
             certs ++ [⟨indices, h_ref, _, new, h_cert⟩],
             h_chain.snoc _ rfl⟩
  | regate g' _h_prev h_sound ih =>
      obtain ⟨_, certs, h_chain⟩ := ih
      exact ⟨h_sound, certs, h_chain⟩

/-- Packaged corollary of `govReach_sound` + `chain_CE`: from a
    sound initial gate, any evolved configuration — through any
    interleaving of admissions and gate swaps — comes with a finite
    list of certificates chaining its apply value back to the
    original, and at every test state where those certificates fire
    (`CertsFire`, a per-instance obligation), every call through the
    original apply value is matched by a call through the evolved
    one with a weakly-bisimilar result.

    Scope: the `regate` steps' soundness is assumed (free only for
    kernel-built `approvedPolicyAt` gates); this is an
    admission-event-level statement, not a whole-program-trace
    theorem. -/
theorem govReach_CE (level : Nat) {s₀ s : GovState}
    (h_sound₀ : BlackPolicy.SoundForCEAt level s₀.gate)
    (h_reach : GovReach level s₀ s) :
    ∃ certs : List (AdmissionCert level),
      ChainOk level certs s₀.applyVal s.applyVal ∧
      ∀ (fuel : Nat) (ptable : PolicyTable) (op : Val) (operands : List Val)
        (T : TowerState) (r : Val) (T' : TowerState),
        CertsFire level certs T →
        HeapValid T.heap → ValValid op T.heap → ListValValid operands T.heap →
        ValValid s₀.applyVal T.heap →
        PolicyTableRespectsBisimT ptable →
        (∀ p, T.policyAt? level = some p → PolicyRespectsBisimT p) →
        (∀ n env, T.envAt? n = some env → EnvValid env T.heap) →
        (∀ n p, T.policyAt? n = some p → PolicyRespectsBisimT p) →
        (∀ n env, T.envAt? n = some env → EnvVis env env T.heap T.heap) →
        HeapDeep T.heap → ValDeep op T.heap → ListValDeep operands T.heap →
        (∀ n env, T.envAt? n = some env → EnvDeep env T.heap) →
        PolicyTableRespectsShift T.heap.length [op, listToVal operands] ptable →
        (∀ n p, T.policyAt? n = some p →
           PolicyRespectsShift T.heap.length [op, listToVal operands] p) →
        callAsBaseApply fuel ptable level s₀.applyVal op operands T = some (r, T') →
        ∃ fuel' T'' r',
          callAsBaseApply fuel' ptable level s.applyVal op operands T
            = some (r', T'') ∧
          ValVis_weak r r' T'.heap T''.heap ∧
          T'.policyAt? level = T''.policyAt? level ∧
          HeapValid T''.heap ∧
          T.heap.length ≤ T''.heap.length := by
  obtain ⟨_, certs, h_chain⟩ := govReach_sound level h_sound₀ h_reach
  exact ⟨certs, h_chain,
         fun fuel ptable op operands T r T' =>
           chain_CE level certs s₀.applyVal s.applyVal h_chain
             fuel ptable op operands T r T'⟩

/-! ## The shape, demonstrated

Admit through gate 1, swap to gate 2 (proof-bearing, so the swap
obligation is free), admit through gate 2. Every step of the
evolution is gated; the composed guarantee follows from
`govReach_CE`. -/

example (level : Nat)
    (approvals₁ approvals₂ : List ApprovedModificationAt)
    (h₂ : ∀ am ∈ approvals₂, am.level = level)
    (ctx₁ ctx₂ : MutationCtx) (new₁ new₂ : Val)
    (h_admit₁ : approvedPolicyAt approvals₁ ctx₁ .builtinBaseApply new₁ = true)
    (h_admit₂ : approvedPolicyAt approvals₂ ctx₂ new₁ new₂ = true) :
    GovReach level
      ⟨approvedPolicyAt approvals₁, .builtinBaseApply⟩
      ⟨approvedPolicyAt approvals₂, new₂⟩ :=
  .modify ctx₂ new₂
    (.regate (approvedPolicyAt approvals₂)
      (.modify ctx₁ new₁ (.refl _) h_admit₁)
      (approvedPolicyAt_SoundForCEAt approvals₂ level h₂))
    h_admit₂

/-! ## Concrete selective approvals

The chain links that actually inhabit the new gates: the multn
worked example (its selective certificate is
`multnApproval_at_proof`, `HeapAgree.lean`) and the
identity-delegate second link, re-proved here in selective form. -/

/-- The multn approval, selective edition. Where `multnApproval`
    (`ProofBased.lean`) pins the full admission-heap prefix, this
    pins only the closure's captured `orig` and `num?` cells — so
    the approval stays matchable, and its certificate consumable,
    after the `base-apply` cell itself has been rewritten by
    later admissions. -/
def multnApprovalAt
    (level : Nat) (heap : Heap) (env metaEnv : Env) (index : Nat)
    (newClosure : Val)
    (h_admit : multnExactPolicy
                 { target := "base-apply", heap := heap, env := env,
                   metaEnv := metaEnv, index := index, level := level }
                 .builtinBaseApply newClosure = true)
    (idx_o idx_n : Nat)
    (h_shape_o : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup "orig" = some idx_o)
    (h_shape_n : ∃ ps body cenv, newClosure = .closure ps body cenv ∧
                  cenv.lookup "num?" = some idx_n) :
    ApprovedModificationAt :=
  { level   := level
    indices := [idx_o, idx_n]
    heap    := heap
    oldVal  := .builtinBaseApply
    newVal  := newClosure
    proof   := multnApproval_at_proof level heap env metaEnv index newClosure
                 h_admit idx_o idx_n h_shape_o h_shape_n }

/-- The identity-delegate approval, selective edition. The
    certificate is `identityDelegate_CE_at`
    (`IdentityDelegate.lean`) — the selective primitive from which
    the full-prefix `identityDelegate_CE_of_closure` is derived. -/
def identityDelegateApprovalAt
    (level : Nat) (heap : Heap) (cenv : Env) (idx_o : Nat) (origVal : Val)
    (h_not_bbApply : origVal ≠ .builtinBaseApply)
    (h_lookup_o : cenv.lookup "orig" = some idx_o)
    (h_heap_o : heap[idx_o]? = some origVal) :
    ApprovedModificationAt :=
  { level   := level
    indices := [idx_o]
    heap    := heap
    oldVal  := origVal
    newVal  := .closure ["op", "args"] identityDelegateBody cenv
    proof   := identityDelegate_CE_at level heap origVal cenv idx_o
                 h_not_bbApply h_lookup_o h_heap_o }

/-! ## Runtime bridge

`GovReach.modify` quantifies over an abstract `MutationCtx`; the
runtime's `.set` clause supplies a concrete one. The inversion lemma
reads the `.set` clause of `eval`, and the corollary shows every
*committed* runtime `.set` is exactly one `GovReach.modify` step on
the (gate, apply-value) projection. -/

/-- Inversion of the `.set` clause: a successful `.set` evaluation
    factors into the RHS evaluation, the meta-mutation check, the
    cell read, the frozen gate, and either a commit (gate said yes;
    heap cell updated) or a refusal (gate said no; state unchanged). -/
theorem eval_set_inverts
    {n : Nat} {ptable : PolicyTable} {level : Nat} {x : String} {e : Expr}
    {env : Env} {T : TowerState} {v : Val} {T_out : TowerState}
    (h : eval (n + 1) ptable level (.set x e) env T = some (v, T_out)) :
    ∃ newv T' idx oldv gate,
      eval n ptable level e env T = some (newv, T') ∧
      env.lookup x = some idx ∧
      isMetaMutation x env T' level = true ∧
      T'.heap[idx]? = some oldv ∧
      T.policyAt? level = some gate ∧
      (let ctx : MutationCtx :=
        { target := x, heap := T'.heap, env := env,
          metaEnv := (T'.envAt? level).getD .nil, index := idx, level := level }
       (gate ctx oldv newv = true ∧ v = .bool true ∧
          T_out = T'.updateHeap idx newv) ∨
       (gate ctx oldv newv = false ∧ v = .bool false ∧ T_out = T')) := by
  simp only [eval] at h
  cases h_e : eval n ptable level e env T with
  | none => rw [h_e] at h; exact absurd h (by simp)
  | some pr =>
      obtain ⟨newv, T'⟩ := pr
      rw [h_e] at h
      simp only at h
      cases h_lk : env.lookup x with
      | none => rw [h_lk] at h; exact absurd h (by simp)
      | some idx =>
          rw [h_lk] at h
          simp only at h
          cases h_meta : isMetaMutation x env T' level with
          | false => rw [h_meta] at h; exact absurd h (by simp)
          | true =>
              rw [h_meta] at h
              simp only [if_true] at h
              cases h_cell : T'.heap[idx]? with
              | none => rw [h_cell] at h; exact absurd h (by simp)
              | some oldv =>
                  rw [h_cell] at h
                  cases h_gate : T.policyAt? level with
                  | none => rw [h_gate] at h; exact absurd h (by simp)
                  | some gate =>
                      rw [h_gate] at h
                      simp only at h
                      refine ⟨newv, T', idx, oldv, gate, rfl, rfl, h_meta,
                              h_cell, rfl, ?_⟩
                      cases h_admit : gate
                          { target := x, heap := T'.heap, env := env,
                            metaEnv := (T'.envAt? level).getD .nil,
                            index := idx, level := level } oldv newv with
                      | true =>
                          rw [h_admit] at h
                          simp only [if_true, Option.some.injEq, Prod.mk.injEq] at h
                          exact Or.inl ⟨h_admit, h.1.symm, h.2.symm⟩
                      | false =>
                          rw [h_admit] at h
                          simp only [Bool.false_eq_true, if_false,
                                     Option.some.injEq, Prod.mk.injEq] at h
                          exact Or.inr ⟨h_admit, h.1.symm, h.2.symm⟩

/-- **Every committed runtime `.set` is one `GovReach.modify`
    step.** The runtime's own `MutationCtx` instantiates the step;
    the resulting evolution is from the cell's old value to the
    admitted new value, under the frozen gate. -/
theorem eval_set_commit_govStep
    {n : Nat} {ptable : PolicyTable} {level : Nat} {x : String} {e : Expr}
    {env : Env} {T : TowerState} {T_out : TowerState}
    (h : eval (n + 1) ptable level (.set x e) env T
          = some (.bool true, T_out)) :
    ∃ (gate : BlackPolicy) (newv : Val) (T' : TowerState) (idx : Nat) (oldv : Val),
      T.policyAt? level = some gate ∧
      T'.heap[idx]? = some oldv ∧
      T_out = T'.updateHeap idx newv ∧
      GovReach level ⟨gate, oldv⟩ ⟨gate, newv⟩ := by
  obtain ⟨newv, T', idx, oldv, gate, _h_e, _h_lk, _h_meta, h_cell, h_gate, h_split⟩ :=
    eval_set_inverts h
  simp only at h_split
  cases h_split with
  | inl h_commit =>
      obtain ⟨h_admit, _, h_T⟩ := h_commit
      exact ⟨gate, newv, T', idx, oldv, h_gate, h_cell, h_T,
             .modify _ newv (.refl _) h_admit⟩
  | inr h_refuse =>
      obtain ⟨_, h_v, _⟩ := h_refuse
      exact absurd h_v (by simp)

/-- Inversion of the `installPolicy` clause: a successful policy
    swap selects an entry of the (static) policy table and installs
    it at the current level. -/
theorem eval_installPolicy_inverts
    {n : Nat} {ptable : PolicyTable} {level : Nat} {i : Nat}
    {env : Env} {T : TowerState} {T_out : TowerState}
    (h : eval (n + 1) ptable level (.installPolicy i) env T
          = some (.bool true, T_out)) :
    ∃ p, ptable[i]? = some p ∧ T_out = T.setPolicyAt level p := by
  simp only [eval] at h
  cases h_pt : ptable[i]? with
  | none =>
      rw [h_pt] at h
      simp at h
  | some p =>
      rw [h_pt] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨p, rfl, h.2.symm⟩

/-- **Every committed runtime `installPolicy` is one
    `GovReach.regate` step**, provided the policy table's entries
    are sound in the selective discipline — which holds for free
    when every entry is an `approvedPolicyAt` gate
    (`approvedPolicyAt_SoundForCEAt`). -/
theorem eval_installPolicy_regate_govStep
    {n : Nat} {ptable : PolicyTable} {level : Nat} {i : Nat}
    {env : Env} {T : TowerState} {T_out : TowerState}
    (h_table : ∀ p ∈ ptable, BlackPolicy.SoundForCEAt level p)
    (h : eval (n + 1) ptable level (.installPolicy i) env T
          = some (.bool true, T_out)) :
    ∃ p, T_out = T.setPolicyAt level p ∧
      ∀ gate applyVal,
        GovReach level ⟨gate, applyVal⟩ ⟨p, applyVal⟩ := by
  obtain ⟨p, h_pt, h_T⟩ := eval_installPolicy_inverts h
  exact ⟨p, h_T, fun gate applyVal =>
    .regate p (.refl _) (h_table p (List.mem_of_getElem? h_pt))⟩

end LeanBlack
