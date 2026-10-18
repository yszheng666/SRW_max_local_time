import SRWTightness.AnnularEntranceChain
import SRWTightness.AxisChainOrientation

open MeasureTheory
namespace SRWTightness

/-- Axis segments in a fixed box give uniform entrance-atom comparisons in either orientation. -/
theorem annular_axis_entrance (hinput : PositiveHarmonicRelativeInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m a R M : ℝ), 128 ≤ m → 32 * C ≤ m →
      0 ≤ a → a ≤ m / 2 → 2 * m ≤ R → M ≤ 5 * m / 4 →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ (w : Site), w ∈ K → ∀ (t : Bool) (u v c : ℤ),
      |(u : ℝ)| ≤ M → |(v : ℝ)| ≤ M → |(c : ℝ)| ≤ M →
      ((3 * m / 4) ^ 2 ≤ (c : ℝ) ^ 2 ∨
        (((0 ≤ u ∧ u ≤ v) ∨ (v ≤ u ∧ u ≤ 0)) ∧
          (3 * m / 4) ^ 2 ≤ normSq (u, c))) →
      Real.exp (-(80 * C)) *
          (competingEntranceLaw (translateFinset b (diskFinset R)) K
            (b + axisSite t u c)).real {w} ≤
        (competingEntranceLaw (translateFinset b (diskFinset R)) K
          (b + axisSite t v c)).real {w} ∧
      (competingEntranceLaw (translateFinset b (diskFinset R)) K
          (b + axisSite t v c)).real {w} ≤
        Real.exp (80 * C) *
          (competingEntranceLaw (translateFinset b (diskFinset R)) K
            (b + axisSite t u c)).real {w} := by
  obtain ⟨C, hC, hh⟩ := annular_entrance_chain hinput
  refine ⟨C, hC, ?_⟩
  intro m a R M hm hCm ha ham hmR hM b K hK w hw t u v c hu hv hc hroute
  have hM0 : 0 ≤ M := (abs_nonneg (u : ℝ)).trans hu
  have hn := axisUnitChain_length_bound u v M hu hv
  have hp := hh m a R hm hCm ha ham hmR b K hK w hw
    (axisUnitChain t u v c) (v - u).natAbs (by linarith) ?_ ?_
  · simpa only [(axisUnitChain_endpoints t u v c).1,
      (axisUnitChain_endpoints t u v c).2] using hp
  · intro i hi
    exact axisUnitChain_step t u v c i
  · intro i hi
    rw [axisUnitChain_normSq]
    constructor
    · rcases hroute with h | ⟨hdir, h⟩
      · exact h.trans (horizontalUnitChain_fixed_lower u v c i)
      · exact h.trans (horizontalUnitChain_outward u v c hdir i)
    · have hb := horizontalUnitChain_box u v c M hu hv hc i
      have hs := (sq_le_sq₀ hM0 (by linarith : 0 ≤ 5 * m / 4)).mpr hM
      nlinarith

end SRWTightness
