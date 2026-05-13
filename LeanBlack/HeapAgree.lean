/-
  lean-sage: HeapAgreeAt — selective heap-prefix relation.

  `HeapPrefix h₁ h₂` (in `ProofBased.lean`) demands content-equality
  at *every* index < `h₁.length`. The multn-style CE proofs only
  read specific cells (the closure's captured `orig` and `num?`
  indices). After a `.set "base-apply"` commits, the base-apply
  cell's content changes — breaking `HeapPrefix` even though the
  cells the proof reads are unchanged.

  `HeapAgreeAt indices h₁ h₂` demands content-equality at exactly
  the specified indices. With length-extension carried separately,
  this is the right premise for "the proof's cell lookups
  transport to a later heap." Preserved by heap appends and by
  heap-updates at any index not in `indices`.

  This file provides the predicate + foundational lemmas. The
  multn proof refactor that consumes them is a separate step.
-/

import LeanBlack.Black
import LeanBlack.Tower
import LeanBlack.ProofBased

open LeanBlack

namespace LeanBlack

/-- `HeapAgreeAt indices h₁ h₂` iff for every `i ∈ indices`,
    `h₁[i]? = h₂[i]?`. Note: no length constraint on either side;
    out-of-bounds on either side both yield `none`, which trivially
    agree. -/
def HeapAgreeAt (indices : List Nat) (h₁ h₂ : Heap) : Prop :=
  ∀ i ∈ indices, h₁[i]? = h₂[i]?

/-- Reflexivity. -/
theorem HeapAgreeAt.refl (indices : List Nat) (h : Heap) :
    HeapAgreeAt indices h h := by
  intro _ _; rfl

/-- Symmetry. -/
theorem HeapAgreeAt.symm {indices : List Nat} {h₁ h₂ : Heap}
    (hab : HeapAgreeAt indices h₁ h₂) :
    HeapAgreeAt indices h₂ h₁ := by
  intro i hi; exact (hab i hi).symm

/-- Transitivity. -/
theorem HeapAgreeAt.trans {indices : List Nat} {h₁ h₂ h₃ : Heap}
    (h12 : HeapAgreeAt indices h₁ h₂) (h23 : HeapAgreeAt indices h₂ h₃) :
    HeapAgreeAt indices h₁ h₃ := by
  intro i hi; exact (h12 i hi).trans (h23 i hi)

/-- `HeapPrefix h₁ h₂` (full content prefix) implies `HeapAgreeAt`
    on any list of indices < `h₁.length`. The wider relation
    discards information; the lemma confirms the implication is
    in the safe direction. -/
theorem HeapPrefix.toHeapAgreeAt
    {h₁ h₂ : Heap} {indices : List Nat}
    (hp : HeapPrefix h₁ h₂)
    (h_bounds : ∀ i ∈ indices, i < h₁.length) :
    HeapAgreeAt indices h₁ h₂ := by
  intro i hi
  have h_lt : i < h₁.length := h_bounds i hi
  have h_take : h₁ = h₂.take h₁.length := hp
  rw [h_take]
  rw [List.getElem?_take]
  split
  · rfl
  · omega

/-- `HeapAgreeAt` survives appending cells beyond the indices' max.
    Specifically, if all indices < `h₁.length` (so within the
    pre-append portion), then appending preserves agreement on
    those indices.

    This is the bread-and-butter monotonicity: heap allocation only
    grows the heap, never disturbs existing cells. -/
theorem HeapAgreeAt.append_right
    {indices : List Nat} {h₁ h₂ : Heap} (extras : List Val)
    (h_agree : HeapAgreeAt indices h₁ h₂)
    (h_bounds : ∀ i ∈ indices, i < h₂.length) :
    HeapAgreeAt indices h₁ (h₂ ++ extras) := by
  intro i hi
  have h_lt : i < h₂.length := h_bounds i hi
  rw [h_agree i hi, List.getElem?_append_left h_lt]

/-- Helper: heap-update at index `j` leaves all other indices
    unchanged. (List.set-like behavior on the custom Heap.update.) -/
theorem heap_update_get_ne (h : Heap) (j : Nat) (v : Val) (i : Nat)
    (h_ne : i ≠ j) :
    (h.update j v)[i]? = h[i]? := by
  induction h generalizing i j with
  | nil => simp [Heap.update]
  | cons x t ih =>
    cases j with
    | zero =>
      cases i with
      | zero => exact absurd rfl h_ne
      | succ i' => simp [Heap.update]
    | succ j' =>
      cases i with
      | zero => simp [Heap.update]
      | succ i' =>
        simp only [Heap.update, List.getElem?_cons_succ]
        have h_ne' : i' ≠ j' := fun h_eq => h_ne (congrArg Nat.succ h_eq)
        exact ih j' i' h_ne'

/-- `HeapAgreeAt` survives heap-update at any index *not* in the
    agreement set. This is the key lemma for post-mutation lifting:
    a `.set "base-apply"` mutates the level's base-apply cell;
    if that cell's index is not among the indices the CE proof
    reads, the agreement on those indices is preserved. -/
theorem HeapAgreeAt.update_disjoint
    {indices : List Nat} {h₁ h₂ : Heap} (j : Nat) (v : Val)
    (h_agree : HeapAgreeAt indices h₁ h₂)
    (h_disjoint : j ∉ indices) :
    HeapAgreeAt indices h₁ (h₂.update j v) := by
  intro i hi
  rw [h_agree i hi]
  have h_ne : i ≠ j := fun h_eq => h_disjoint (h_eq ▸ hi)
  exact (heap_update_get_ne h₂ j v i h_ne).symm

end LeanBlack
