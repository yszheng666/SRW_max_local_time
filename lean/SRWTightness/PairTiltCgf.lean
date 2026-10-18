import SRWTightness.PairTiltWeights
import SRWTightness.ObservationCovarianceCgf

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Cubic cgf error for the actual signed two-site tilt, with the fixed coefficient budget six. -/
theorem pair_tilt_cgf_half_variance (D K : Finset Site) (hKD : K ⊆ D)
    (z y : K) (w : K → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1) (L : ℝ) (hL : 0 < L)
    (hαL : α ≤ L) (hG : ∀ x : K, killedGreen D x x ≤ L)
    (hsmall : 6 ≤ (u * Real.sqrt (α * g)) / (8 * L))
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let X := (2 : ℝ) • (normalizedMarkSum K k α g u z + normalizedMarkSum K k α g u y -
      normalizedWeightedSum K k α g u w)
    let μ := markProductLaw D K α k
    |cgf X μ 1 - covariance X X μ / 2| ≤
      23592976 * L ^ 3 * 6 ^ 3 / (12 * u * (Real.sqrt (α * g)) ^ 3) := by
  classical
  have hv := pairTiltWeight_l1 z y w hw hw1
  have ht := normalizedWeightedSum_cgf_taylor_scaled D K hKD α g u hα hg hu hcap
    (pairTiltWeight z y w) L hL hαL hG (hv.trans hsmall) k hk
  have hq := normalized_green_quadratic_eq_covariance D K hKD α g u hα hg hu hcap
    (pairTiltWeight z y w) k hk
  dsimp only at ht hq ⊢
  rw [hq] at ht
  have hf : normalizedWeightedSum K k α g u (pairTiltWeight z y w) =
      (2 : ℝ) • (normalizedMarkSum K k α g u z + normalizedMarkSum K k α g u y -
        normalizedWeightedSum K k α g u w) := by
    funext Y
    exact pairTiltWeight_sum z y w (fun x ↦ normalizedMarkSum K k α g u x Y)
  rw [hf] at ht
  refine ht.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) hv 3) (by positivity)

end SRWTightness
