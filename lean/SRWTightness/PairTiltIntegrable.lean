import SRWTightness.PairTiltWeights
import SRWTightness.NormalizedMarkTilt

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Exponential integrability of the signed pair statistic uses only the mark moment bound. -/
theorem pair_tilt_integrable (D K : Finset Site) (hKD : K ⊆ D)
    (z y : K) (w : K → ℝ) (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1) (L : ℝ) (hL : 0 < L)
    (hG : ∀ x : K, killedGreen D x x ≤ L)
    (hsmall : 6 ≤ (u * Real.sqrt (α * g)) / (8 * L)) (k : ℕ) :
    Integrable (fun Y ↦ Real.exp (2 * (normalizedMarkSum K k α g u z Y +
      normalizedMarkSum K k α g u y Y - normalizedWeightedSum K k α g u w Y)))
      (markProductLaw D K α k) := by
  classical
  have hr : 0 < u * Real.sqrt (α * g) := by positivity
  have hs : (∑ x, |pairTiltWeight z y w x / (u * Real.sqrt (α * g))|) ≤
      1 / (4 * L) := by
    simp only [abs_div, abs_of_pos hr, ← Finset.sum_div]
    apply (div_le_iff₀ hr).mpr
    have hb := (le_div_iff₀ (by positivity : 0 < 8 * L)).mp hsmall
    have hc : 6 ≤ 1 / (4 * L) * (u * Real.sqrt (α * g)) := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity : 0 < 4 * L)]
      nlinarith
    exact (pairTiltWeight_l1 z y w hw hw1).trans hc
  let μ := markProductLaw D K α k
  let X := normalizedWeightedSum K k α g u (pairTiltWeight z y w)
  letI : IsProbabilityMeasure μ := markProductLaw_isProbabilityMeasure D K α hα.le hcap k
  letI : IsProbabilityMeasure (μ.tilted X) :=
    (normalizedWeightedSum_product_tilt D K hKD α g u hα.le hcap
      (pairTiltWeight z y w) L hL hG hs k).1
  have hi : Integrable (fun Y ↦ Real.exp (X Y)) μ := by
    by_contra hn
    have hh := congrArg (fun ν : Measure (MarkSamples K k) ↦ ν Set.univ)
      (tilted_of_not_integrable hn)
    simpa using hh
  have he : X = fun Y ↦ 2 * (normalizedMarkSum K k α g u z Y +
      normalizedMarkSum K k α g u y Y - normalizedWeightedSum K k α g u w Y) := by
    funext Y
    exact pairTiltWeight_sum z y w (fun x ↦ normalizedMarkSum K k α g u x Y)
  rwa [he] at hi

end SRWTightness
