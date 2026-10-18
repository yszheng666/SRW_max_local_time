import SRWTightness.ObservationCenteredVectorData
import SRWTightness.IndependentVectorCovariance

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- The actual whitened mark summands satisfy the centering, independence and covariance CLT inputs. -/
theorem observationFamily_whitened_vector_inputs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D K : Finset Site) (hKD : K ⊆ D) (α g u : ℝ)
    (hα : 0 < α) (hg : 0 < g) (hu : 0 < u) (hcap : α * capacity D K ≤ 1)
    (w : ι → K → ℝ) (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (b : ι → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ i, |b i|) < (u * Real.sqrt (α * g)) / (8 * L)) (k : ℕ) :
    let c := u * Real.sqrt (α * g)
    let β := fun z ↦ (∑ i, b i * w i z) / c
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
    let ρ := (markProductLaw D K α k).tilted (fun Y ↦ ∑ i, b i * F i Y)
    let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
    let T := toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt Gamma)⁻¹)
    let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
    let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
    let W := fun Y ↦ c⁻¹ • T (V Y)
    Gamma.PosDef → IsProbabilityMeasure ρ ∧
      iIndepFun (fun j (Y : MarkSamples K k) ↦ W (Y j)) ρ ∧
      (∀ j : Fin k, Integrable (fun Y : MarkSamples K k ↦ W (Y j)) ρ ∧
        (∫ Y : MarkSamples K k, W (Y j) ∂ρ) = 0 ∧
        MemLp (fun Y : MarkSamples K k ↦ W (Y j)) 2 ρ) ∧
      (∀ Y : MarkSamples K k, (∑ j, W (Y j)) =
        T (toLp 2 (fun i ↦ F i Y - ∫ Z, F i Z ∂ρ))) ∧
      (∀ r s : ι, (∑ j : Fin k, covariance (fun Y ↦ W (Y j) r)
        (fun Y ↦ W (Y j) s) ρ) = if r = s then 1 else 0) := by
  dsimp only
  intro hGamma
  let c := u * Real.sqrt (α * g)
  let β := fun z ↦ (∑ i, b i * w i z) / c
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
  let ρ := (markProductLaw D K α k).tilted (fun Y ↦ ∑ i, b i * F i Y)
  let Gamma : Matrix ι ι ℝ := fun i j ↦ covariance (F i) (F j) ρ
  let T := toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt Gamma)⁻¹)
  let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
  let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
  let W := fun Y ↦ c⁻¹ • T (V Y)
  have hh := observationFamily_centered_vector_data D K hKD α g u hα hg hu hcap
    w hw hw1 b L hL hG hsmall k T
  letI : IsProbabilityMeasure ρ := hh.1
  have hsum := hh.2.2.2.1
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hsum, ?_⟩
  intro r s
  have hc := independent_vector_covariance_sum ρ
    (fun j (Y : MarkSamples K k) ↦ W (Y j)) hh.2.1
    (fun j ↦ (hh.2.2.1 j).2.2) r s
  have he (i : ι) : (fun Y : MarkSamples K k ↦ ∑ j, W (Y j) i) =
      (fun Y ↦ (T (toLp 2 (fun l ↦ F l Y - ∫ Z, F l Z ∂ρ))) i) := by
    funext Y
    have hcoord := congrArg (fun x : EuclideanSpace ℝ ι ↦ x i) (hsum Y)
    change (ofLp (∑ j : Fin k, W (Y j))) i = _ at hcoord
    simpa only [ofLp_sum, Finset.sum_apply] using hcoord
  rw [← hc, he r, he s]
  exact whitened_observation_covariance ρ F hh.2.2.2.2 hGamma r s

end SRWTightness
