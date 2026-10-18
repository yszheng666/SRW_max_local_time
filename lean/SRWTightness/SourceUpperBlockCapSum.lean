import SRWTightness.SourceUpperRootCap

open Filter MeasureTheory

namespace SRWTightness

/-- The sum of individual block root-cap probabilities has the same vanishing majorant. -/
theorem source_upper_block_cap_sum (hinput : PotentialKernelAsymptoticInput) :
    ∀ᶠ t : ℝ in atTop,
      (∑ b ∈ sourceUpperBlockCenters t,
        pathLaw.real {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)}) ≤
      25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t)) := by
  filter_upwards [source_upper_block_root_cap_tail hinput, source_upper_block_total_count]
    with t ht hc
  calc
    _ ≤ ∑ b ∈ sourceUpperBlockCenters t, Real.exp (-t ^ 2 / (4 * Real.log t)) :=
      Finset.sum_le_sum (fun b hb ↦ ht b hb)
    _ = ((sourceUpperBlockCenters t).card : ℝ) *
        Real.exp (-t ^ 2 / (4 * Real.log t)) := by simp
    _ ≤ (25 * (Real.exp t) ^ 2) * Real.exp (-t ^ 2 / (4 * Real.log t)) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by
      rw [show 2 * t - t ^ 2 / (4 * Real.log t) =
        (t + t) + (-t ^ 2 / (4 * Real.log t)) by ring, Real.exp_add, Real.exp_add]
      ring

/-- The individual cap-tail sum in ENNReal retains the explicit spatial majorant. -/
theorem source_upper_block_cap_sum_ennreal (hinput : PotentialKernelAsymptoticInput) :
    ∀ᶠ t : ℝ in atTop,
      (∑ b ∈ sourceUpperBlockCenters t,
        pathLaw {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)}) ≤
      ENNReal.ofReal (25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t))) := by
  filter_upwards [source_upper_block_cap_sum hinput] with t ht
  have heq : (∑ b ∈ sourceUpperBlockCenters t,
      pathLaw {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)}) =
      ENNReal.ofReal (∑ b ∈ sourceUpperBlockCenters t,
        pathLaw.real {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)}) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ ↦ measureReal_nonneg)]
    apply Finset.sum_congr rfl
    intro b hb
    exact (ofReal_measureReal (measure_ne_top _ _)).symm
  rw [heq]
  exact ENNReal.ofReal_le_ofReal ht

end SRWTightness
