import SRWTightness.EuclideanThirdMoment
import SRWTightness.ReferenceTiltedCenteredMoment

open MeasureTheory WithLp

namespace SRWTightness

/-- Actual tilted centered observation vectors satisfy the p^(3/2) Euclidean third-moment bound. -/
theorem referenceMark_tilted_vector_centered_third {ι : Type*} [Fintype ι]
    (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (w : ι → K → ℝ)
    (hw : ∀ i z, 0 ≤ w i z) (hw1 : ∀ i, ∑ z, w i z = 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
    let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
    Integrable (fun Y ↦ ‖V Y‖ ^ 3) ν ∧
      (∫ Y, ‖V Y‖ ^ 3 ∂ν) ≤
        5898244 * L ^ 3 * Fintype.card ι * Real.sqrt (Fintype.card ι) := by
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  let U := fun i (Y : Mark K) ↦ ∑ z, w i z * (Y z : ℝ)
  let V : Mark K → EuclideanSpace ℝ ι := fun Y ↦ toLp 2 (fun i ↦ U i Y - ∫ Z, U i Z ∂ν)
  have hm : Measurable V := by dsimp [V, U]; fun_prop
  have hc (i : ι) := referenceMark_tilted_weighted_centered_third D K hKD α hα hcap
    (w i) (hw i) (hw1 i) β L hL hαL hG hsmall
  have hi (i : ι) : Integrable (fun Y ↦ |V Y i| ^ 3) ν := (hc i).2.1
  have hh := euclidean_third_moment_bound ν V hm hi
  refine ⟨hh.1, hh.2.trans ?_⟩
  calc
    _ ≤ Real.sqrt (Fintype.card ι) * ∑ _i : ι, (5898244 * L ^ 3) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      exact Finset.sum_le_sum (fun i _ ↦ (hc i).2.2)
    _ = _ := by simp; ring

end SRWTightness
