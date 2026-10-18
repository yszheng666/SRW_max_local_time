import SRWTightness.UpperBarrierSpatialSum
import SRWTightness.SourceUpperBarrierSlopeFactor
import SRWTightness.SourceUpperBarrierDefinition

open Filter
namespace SRWTightness

/-- Source barrier summation from local tails and mesh weights; those two inputs remain to be bound
 to the actual SRW mesh before certifying the manuscript spatial probability estimate. -/
theorem source_upper_barrier_spatial_sum (hScale : ExponentialFloorScaleInput)
    (C₁ C₂ K : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ j : ℕ, 1 ≤ j → j ≤ sourceUpperCoarseDepth t → ∀ v : ℝ, 0 ≤ v →
      ∀ (Z : Finset Site) (p ψ : Site → ℝ),
      (∀ z ∈ Z, p z ≤ C₁ * ψ z / ((j : ℝ) + 1) *
        Real.exp (-(sourceUpperBarrier t s j + v) ^ 2 / (2 * ((j : ℝ) + K)))) →
      (∑ z ∈ Z, ψ z) ≤ C₂ * ((j : ℝ) + 1) ^ 2 * Real.exp (2 * (j : ℝ)) →
      (∑ z ∈ Z, p z) ≤ C * ((j : ℝ) + 1) ^ 3 *
        Real.exp (-3 * ((4 + s) + sourceUpperBarrierCurvature t j + v) / 2) := by
  obtain ⟨C₃, hC₃, hslope⟩ := source_upper_barrier_slope_factor hScale
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  refine ⟨C₁ * C₂ * C₃ * Real.exp (9 * K / 2), by positivity, ?_⟩
  filter_upwards [hslope, source_upper_barrier_slope_bounds hScale, hcond]
    with t hsl hθ ht
  intro s hs hslog j hj hjN v hv Z p ψ hlocal hmesh
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hjT : (j : ℝ) ≤ sourceUpperTotalDepth t := by
    have hj' : (j : ℝ) ≤ (sourceUpperCoarseDepth t : ℝ) := by exact_mod_cast hjN
    have hd := ht.2.2.2.2.2.2.1
    unfold sourceUpperTotalDepth
    linarith
  have hw : 0 ≤ sourceUpperBarrierCurvature t j := by
    unfold sourceUpperBarrierCurvature
    exact Real.rpow_nonneg (le_min hj0 (sub_nonneg.mpr hjT)) _
  have hU : 0 ≤ (4 + s) + sourceUpperBarrierCurvature t j + v := by linarith
  have hid : sourceUpperSlope t s * (j : ℝ) +
      ((4 + s) + sourceUpperBarrierCurvature t j + v) = sourceUpperBarrier t s j + v := by
    unfold sourceUpperBarrier
    ring
  apply upper_barrier_spatial_sum Z p ψ (sourceUpperSlope t s) j
    ((4 + s) + sourceUpperBarrierCurvature t j + v) K C₁ C₂ C₃
    hj0 hK.le (by linarith) (hθ s hs hslog).1 (hθ s hs hslog).2 hU
    hC₁.le hC₂.le hC₃.le
  · simpa only [hid] using hlocal
  · exact hmesh
  · exact hsl s hs j hjN

end SRWTightness
