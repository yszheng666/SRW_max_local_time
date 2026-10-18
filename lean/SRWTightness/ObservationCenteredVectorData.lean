import SRWTightness.IidCenteredVectors
import SRWTightness.NormalizedCenteredVectorSum
import SRWTightness.NormalizedIidL2
import SRWTightness.NormalizedMarkTilt
import SRWTightness.ReferenceTiltedWeightedL2
import SRWTightness.ObservationCoefficientContraction

open MeasureTheory ProbabilityTheory WithLp

namespace SRWTightness

/-- The actual normalized tilt supplies independent zero-mean summands and their exact vector sum. -/
theorem observationFamily_centered_vector_data {ι : Type*} [Fintype ι]
    (D K : Finset Site) (hKD : K ⊆ D) (α g u : ℝ)
    (hα : 0 < α) (hg : 0 < g) (hu : 0 < u) (hcap : α * capacity D K ≤ 1)
    (w : ι → K → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (b : ι → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ i, |b i|) < (u * Real.sqrt (α * g)) / (8 * L)) (k : ℕ)
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    let c := u * Real.sqrt (α * g)
    let β := fun z ↦ (∑ i, b i * w i z) / c
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
    let ρ := (markProductLaw D K α k).tilted (fun Y ↦ ∑ i, b i * F i Y)
    let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
    let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
    let W := fun Y ↦ c⁻¹ • T (V Y)
    IsProbabilityMeasure ρ ∧
      iIndepFun (fun j (Y : MarkSamples K k) ↦ W (Y j)) ρ ∧
      (∀ j : Fin k, Integrable (fun Y : MarkSamples K k ↦ W (Y j)) ρ ∧
        (∫ Y : MarkSamples K k, W (Y j) ∂ρ) = 0 ∧
        MemLp (fun Y : MarkSamples K k ↦ W (Y j)) 2 ρ) ∧
      (∀ Y : MarkSamples K k, (∑ j, W (Y j)) =
        T (toLp 2 (fun i ↦ F i Y - ∫ Z, F i Z ∂ρ))) ∧
      (∀ i, MemLp (F i) 2 ρ) := by
  let c := u * Real.sqrt (α * g)
  let v := fun z ↦ ∑ i, b i * w i z
  let β := fun z ↦ v z / c
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hv := normalized_observation_coefficients_l1 w hw hw1 b c hc
  have hs : (∑ z, |β z|) < 1 / (8 * L) := by
    apply hv.trans_lt
    apply (div_lt_iff₀ hc).mpr
    simpa only [c, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsmall
  have hs4 : (∑ z, |β z|) ≤ 1 / (4 * L) :=
    (hs.trans (one_div_lt_one_div_of_lt (by positivity) (by linarith))).le
  letI : IsProbabilityMeasure ν :=
    referenceMark_linear_tilt_probability D K hKD α hα.le hcap β L hL hG hs4
  have hmU (i : ι) : Measurable (U i) := by dsimp [U]; fun_prop
  have hU (i : ι) : MemLp (U i) 2 ν := by
    simpa only [one_mul] using referenceMark_tilted_weighted_memLp_two
      D K hKD α hα.le hcap (w i) (hw i) (hw1 i) β L hL hG 1 (by simpa using hs)
  have hf : (fun Y : MarkSamples K k ↦ ∑ i, b i * normalizedWeightedSum K k α g u (w i) Y) =
      normalizedWeightedSum K k α g u v := by
    funext Y
    exact observation_linear_combination w b (fun z ↦ normalizedMarkSum K k α g u z Y)
  have he := (normalizedWeightedSum_product_tilt D K hKD α g u hα.le hcap v L hL hG hs4 k).2.1
  have hh := iid_centered_linear_vectors ν U hmU
    (fun i ↦ (hU i).integrable (by norm_num)) T c⁻¹ k
  have hW := (c⁻¹ • T).comp_memLp' (centered_vector_memLp_two ν U hU)
  dsimp only
  rw [hf, he]
  refine ⟨inferInstance, hh.1, ?_, normalized_centered_vector_sum K k α g u ν w hU T,
    fun i ↦ normalizedWeightedSum_memLp_two_iid K k α g u ν (w i) (hU i)⟩
  intro j
  exact ⟨(hh.2 j).1, (hh.2 j).2,
    hW.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k ↦ ν) j)⟩

end SRWTightness
