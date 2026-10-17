import SRWTightness.SRWFourierInversion

namespace SRWTightness

theorem position_binomial_coordinates (ω : Sample) (n : ℕ) :
    ∃ j ≤ n, ∃ l ≤ n, position ω n = ((j : ℤ) + l - n, (j : ℤ) - l) := by
  induction n with
  | zero => exact ⟨0, le_rfl, 0, le_rfl, rfl⟩
  | succ n ih =>
    obtain ⟨j, hj, l, hl, he⟩ := ih
    rw [position, he]
    generalize hd : ω n = d
    fin_cases d
    · refine ⟨j + 1, by omega, l + 1, by omega, ?_⟩
      apply Prod.ext <;> norm_num [step] <;> push_cast <;> omega
    · refine ⟨j, by omega, l, by omega, ?_⟩
      apply Prod.ext <;> norm_num [step] <;> push_cast <;> omega
    · refine ⟨j + 1, by omega, l, by omega, ?_⟩
      apply Prod.ext <;> norm_num [step] <;> push_cast <;> omega
    · refine ⟨j, by omega, l + 1, by omega, ?_⟩
      apply Prod.ext <;> norm_num [step] <;> push_cast <;> omega

theorem transitionProbability_eq_zero_of_unreachable (n : ℕ) (z : Site)
    (hz : ¬ ∃ j ≤ n, ∃ l ≤ n, z = ((j : ℤ) + l - n, (j : ℤ) - l)) :
    transitionProbability n z = 0 := by
  unfold transitionProbability
  have he : {ω | position ω n = z} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    apply hz
    obtain ⟨j, hj, l, hl, he⟩ := position_binomial_coordinates ω n
    exact ⟨j, hj, l, hl, (show position ω n = z from hω).symm.trans he⟩
  rw [he]
  simp

end SRWTightness
