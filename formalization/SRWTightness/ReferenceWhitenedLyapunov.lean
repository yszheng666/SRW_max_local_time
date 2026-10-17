import SRWTightness.ReferenceWhitenedThirdMoment
import SRWTightness.ReferenceProductTilt

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

/-- The Lyapunov sum of iid vector summands is exactly the sample size times one third moment. -/
theorem iid_sum_third_moments {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → EuclideanSpace ℝ ι)
    (hW : Measurable W) (k : ℕ) :
    (∑ i : Fin k, ∫ Y : Fin k → Ω, ‖W (Y i)‖ ^ 3 ∂Measure.pi (fun _ : Fin k ↦ μ)) =
      k * ∫ Y, ‖W Y‖ ^ 3 ∂μ := by
  have hm : Measurable (fun Y ↦ ‖W Y‖ ^ 3) := by fun_prop
  have he (i : Fin k) :
      (∫ Y : Fin k → Ω, ‖W (Y i)‖ ^ 3 ∂Measure.pi (fun _ : Fin k ↦ μ)) =
        ∫ Y, ‖W Y‖ ^ 3 ∂μ := by
    have hh := integral_map (μ := Measure.pi (fun _ : Fin k ↦ μ))
      (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin k ↦ μ) i).map_eq] at hh
    exact hh.symm
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Lyapunov third-moment sum for the actual product-tilted, whitened mark summands. -/
theorem referenceMark_whitened_lyapunov {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (w : ι → K → ℝ)
    (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L))
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x)) (k : ℕ) :
    let f := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let ν := (referenceMarkLaw D K α).tilted f
    let ρ := (markProductLaw D K α k).tilted (fun Y ↦ ∑ i, f (Y i))
    let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
    let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
    let W := fun Y ↦ c⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) (V Y)
    (∑ i : Fin k, ∫ Y, ‖W (Y i)‖ ^ 3 ∂ρ) ≤
      k * (5898244 * L ^ 3 * Fintype.card ι * Real.sqrt (Fintype.card ι)) /
        (c * Real.sqrt a) ^ 3 := by
  let f := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let ν := (referenceMarkLaw D K α).tilted f
  let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
  let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
  let W := fun Y ↦ c⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) (V Y)
  have hm : Measurable W := by dsimp [W, V, U]; fun_prop
  have hs4 : (∑ z, |β z|) ≤ 1 / (4 * L) :=
    hsmall.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  letI : IsProbabilityMeasure ν :=
    referenceMark_linear_tilt_probability D K hKD α hα hcap β L hL hG hs4
  have he := (referenceMark_product_tilt D K hKD α hα hcap β L hL hG hs4 k).2.1
  have hb := (referenceMark_whitened_third_moment D K hKD α hα hcap w hw hw1
    β L hL hαL hG hsmall A hA a c ha hc hlo).2
  dsimp only
  rw [he, iid_sum_third_moments ν W hm k]
  have hh := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg k)
  simpa only [mul_div_assoc] using hh

end SRWTightness
