import SRWTightness.NormalizedCgfTaylor
import SRWTightness.ObservationCoefficientContraction

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual vector of probability-weighted observations has a dimension-free directional
cgf error, expressed with its exact physical Green-energy quadratic term. -/
theorem observationFamily_cgf_taylor {ι : Type*} [Fintype ι]
    (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1)
    (w : ι → K → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (b : ι → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ i, |b i|) ≤ (u * Real.sqrt (α * g)) / (8 * L))
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) :
    let β := fun z ↦ (∑ i, b i * w i z) / (u * Real.sqrt (α * g))
    |cgf (fun Y : MarkSamples K k ↦ ∑ i, b i * normalizedWeightedSum K k α g u (w i) Y)
      (markProductLaw D K α k) 1 -
        k * (2 * α * (∑ y : K, ∑ z : K, β y * killedGreen D y z * β z) -
          α * (∑ z, β z ^ 2) - (α * ∑ z, β z) ^ 2) / 2| ≤
            23592976 * L ^ 3 * (∑ i, |b i|) ^ 3 /
              (12 * u * (Real.sqrt (α * g)) ^ 3) := by
  let v := fun z ↦ ∑ i, b i * w i z
  have hv : (∑ z, |v z|) ≤ ∑ i, |b i| := observation_coefficients_l1 w hw hw1 b
  have hf : (fun Y : MarkSamples K k ↦ ∑ i, b i * normalizedWeightedSum K k α g u (w i) Y) =
      normalizedWeightedSum K k α g u v := by
    funext Y
    exact observation_linear_combination w b (fun z ↦ normalizedMarkSum K k α g u z Y)
  dsimp only
  rw [hf]
  have ht := normalizedWeightedSum_cgf_taylor_scaled D K hKD α g u hα hg hu hcap v
    L hL hαL hG (hv.trans hsmall) k hk
  refine ht.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) hv 3) (by positivity)

end SRWTightness
