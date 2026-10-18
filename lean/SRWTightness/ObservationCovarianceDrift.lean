import SRWTightness.NormalizedCovarianceDrift
import SRWTightness.ObservationCoefficientContraction

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Entrywise covariance error for the actual normalized observation family under signed tilting. -/
theorem observationFamily_covariance_drift {ι : Type*} [Fintype ι]
    (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D K ≤ 1)
    (w : ι → K → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (b : ι → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ i, |b i|) < (u * Real.sqrt (α * g)) / (8 * L))
    (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ)) (i j : ι) :
    let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
    let μ := markProductLaw D K α k
    |covariance (F i) (F j) (μ.tilted (fun Y ↦ ∑ l, b l * F l Y)) -
      covariance (F i) (F j) μ| ≤
        35389464 * L ^ 3 * (∑ l, |b l|) / (2 * u * (Real.sqrt (α * g)) ^ 3) := by
  let v := fun z ↦ ∑ l, b l * w l z
  let c := u * Real.sqrt (α * g)
  have hc : 0 < c := by dsimp [c]; positivity
  have hv : (∑ z, |v z / c|) ≤ (∑ l, |b l|) / c :=
    normalized_observation_coefficients_l1 w hw hw1 b c hc
  have hs : (∑ z, |v z / c|) < 1 / (8 * L) := by
    apply hv.trans_lt
    apply (div_lt_iff₀ hc).mpr
    simpa only [c, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsmall
  have hf : (fun Y : MarkSamples K k ↦ ∑ l, b l * normalizedWeightedSum K k α g u (w l) Y) =
      normalizedWeightedSum K k α g u v := by
    funext Y
    exact observation_linear_combination w b (fun z ↦ normalizedMarkSum K k α g u z Y)
  dsimp only
  rw [hf]
  have hh := normalizedWeightedSum_covariance_drift D K hKD α g u hα hg hu hcap
    (w i) (w j) (hw i) (hw j) (hw1 i) (hw1 j) v L hL hαL hG hs k
  refine hh.trans ?_
  calc
    _ ≤ k * (35389464 * L ^ 3 * ((∑ l, |b l|) / c)) / c / c := by
      apply div_le_div_of_nonneg_right _ hc.le
      apply div_le_div_of_nonneg_right _ hc.le
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hv (by positivity)) (Nat.cast_nonneg k)
    _ = _ := by
      rw [← hk]
      dsimp [c]
      have hr : Real.sqrt (α * g) ≠ 0 := ne_of_gt (by positivity)
      field_simp
      <;> ring

end SRWTightness
