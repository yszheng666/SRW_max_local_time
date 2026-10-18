import SRWTightness.WhiteningMatrixBound
import SRWTightness.ScaledThirdMoment
import SRWTightness.ReferenceTiltedVectorThird

open MeasureTheory Matrix WithLp

open scoped MatrixOrder

namespace SRWTightness

/-- Actual tilted centered mark vectors have controlled third moments after whitening and scaling. -/
theorem referenceMark_whitened_third_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (w : ι → K → ℝ)
    (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L))
    (A : Matrix ι ι ℝ) (hA : A.PosDef) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, a * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x)) :
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
    let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
    let W := fun Y ↦ c⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) (V Y)
    Integrable (fun Y ↦ ‖W Y‖ ^ 3) ν ∧
      (∫ Y, ‖W Y‖ ^ 3 ∂ν) ≤
        (5898244 * L ^ 3 * Fintype.card ι * Real.sqrt (Fintype.card ι)) /
          (c * Real.sqrt a) ^ 3 := by
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
  let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
  let W := fun Y ↦ c⁻¹ • toEuclideanCLM (𝕜 := ℝ) ((CFC.sqrt A)⁻¹) (V Y)
  have hm : Measurable W := by dsimp [W, V, U]; fun_prop
  have hv := referenceMark_tilted_vector_centered_third D K hKD α hα hcap w hw hw1
    β L hL hαL hG hsmall
  have hb (Y : Mark K) : ‖W Y‖ ≤ ‖V Y‖ / (c * Real.sqrt a) := by
    dsimp only [W]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc)]
    calc
      _ ≤ c⁻¹ * (‖V Y‖ / Real.sqrt a) :=
        mul_le_mul_of_nonneg_left (matrix_whitening_norm_le A hA a ha hlo (V Y))
          (inv_nonneg.mpr hc.le)
      _ = _ := by ring
  have hh := third_moment_of_norm_le_div ν V W hm hv.1 (c * Real.sqrt a) (by positivity) hb
  refine ⟨hh.1, hh.2.trans ?_⟩
  exact div_le_div_of_nonneg_right hv.2 (by positivity)

end SRWTightness
