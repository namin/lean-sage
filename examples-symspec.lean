⟨by decide, by decide,
 by intro op
    show ∃ b, applyPrim_symQ [op] = some (.bool b)
    cases op <;> exact ⟨_, rfl⟩,
 by intro op h_true fuel ptable level operands T
    have : ∃ s, op = .sym s := by
      cases op with
      | sym s => exact ⟨s, rfl⟩
      | num _ => simp [applyPrim, applyPrim_symQ] at h_true
      | bool _ => simp [applyPrim, applyPrim_symQ] at h_true
      | nilV => simp [applyPrim, applyPrim_symQ] at h_true
      | cons _ _ => simp [applyPrim, applyPrim_symQ] at h_true
      | closure _ _ _ => simp [applyPrim, applyPrim_symQ] at h_true
      | prim _ => simp [applyPrim, applyPrim_symQ] at h_true
      | builtinBaseApply => simp [applyPrim, applyPrim_symQ] at h_true
    obtain ⟨s, rfl⟩ := this
    cases fuel with
    | zero => simp [applyDirect]
    | succ k => simp [applyDirect]⟩
