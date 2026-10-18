import SRWTightness.ReferenceWhitenedLyapunov
import SRWTightness.NormalizedMarkTilt
import SRWTightness.ObservationCoefficientContraction

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- Each whitened summand has an integrable third moment under the actual observation tilt. -/
theorem observationFamily_whitened_third_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D K : Finset Site) (hKD : K ⊆ D) (α g u : ℝ)
    (hα : 0 < α) (hg : 0 < g) (hu : 0 < u) (hcap : α * capacity D K ≤ 1)
    (w : ι → K → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (b : ι → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ i, |b i|) ≤ (u * Real.sqrt (α * g)) / (8 * L))
    (k : ℕ)
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (a : ℝ) (ha : 0 < a)
    (hlo : ∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x)) :
    let c := u * Real.sqrt (α * g)
    let β := fun z ↦ (∑ i, b i * w i z) / c
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
    let ρ := (markProductLaw D K α k).tilted (fun Y ↦ ∑ i, b i * F i Y)
    let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
    let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
    let W := fun Y ↦ c⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) (V Y)
    ∀ j : Fin k, Integrable (fun Y : MarkSamples K k ↦ ‖W (Y j)‖ ^ 3) ρ := by
  let c := u * Real.sqrt (α * g)
  let v := fun z ↦ ∑ i, b i * w i z
  let β := fun z ↦ v z / c
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
  let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
  let W := fun Y ↦ c⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) (V Y)
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : Measurable W := by dsimp [W, V, U]; fun_prop
  have hv := normalized_observation_coefficients_l1 w hw hw1 b c hc
  have hs : (∑ z, |β z|) ≤ 1 / (8 * L) := by
    apply hv.trans
    apply (div_le_iff₀ hc).mpr
    simpa only [c, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsmall
  have hs4 : (∑ z, |β z|) ≤ 1 / (4 * L) :=
    hs.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  letI : IsProbabilityMeasure ν :=
    referenceMark_linear_tilt_probability D K hKD α hα.le hcap β L hL hG hs4
  have hf : (fun Y : MarkSamples K k ↦ ∑ i, b i * normalizedWeightedSum K k α g u (w i) Y) =
      normalizedWeightedSum K k α g u v := by
    funext Y
    exact observation_linear_combination w b (fun z ↦ normalizedMarkSum K k α g u z Y)
  have he := (normalizedWeightedSum_product_tilt D K hKD α g u hα.le hcap v L hL hG hs4 k).2.1
  have hb := (referenceMark_whitened_third_moment D K hKD α hα.le hcap w hw hw1
    β L hL hαL hG hs A hA a c ha hc hlo).1
  dsimp only
  rw [hf, he]
  intro j
  exact (measurePreserving_eval (fun _ : Fin k ↦ ν) j).integrable_comp_of_integrable hb

end SRWTightness
