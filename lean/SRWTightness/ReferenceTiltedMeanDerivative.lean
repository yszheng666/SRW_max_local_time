import SRWTightness.TiltedMeanDerivative
import SRWTightness.ReferenceLinearExpInterior
import SRWTightness.ReferenceSecondMoment

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace SRWTightness

/-- Actual nonnegative linear mark observations obey the covariance response identity
throughout the strict physical tilt neighborhood. -/
theorem referenceMark_hasDerivAt_tilted_mean (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    HasDerivAt (fun t ↦ ∫ Y, H Y ∂μ.tilted (fun Y ↦ t * X Y))
      (covariance H X (μ.tilted (fun Y ↦ s * X Y))) s := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  have hmH : Measurable H := by dsimp [H]; fun_prop
  have hH0 (Y : Mark K) : 0 ≤ H Y :=
    Finset.sum_nonneg (fun z _ ↦ mul_nonneg (hw z) (Nat.cast_nonneg _))
  have hH2 : MemLp H 2 (referenceMarkLaw D K α) :=
    memLp_finsetSum Finset.univ (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (w z))
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hs4 : |s| * (∑ z, |β z|) < 1 / (4 * L) := hs.trans
    (one_div_lt_one_div_of_lt (by positivity) (by linarith))
  have ht := referenceMark_linear_exp_interior D K hKD α hα hcap β L hL hG s hs4
  have hdouble : |s| * (∑ z, |2 * β z|) < 1 / (4 * L) := by
    have he : (∑ z, |2 * β z|) = 2 * (∑ z, |β z|) := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), Finset.mul_sum]
    rw [he]
    calc
      _ = 2 * (|s| * ∑ z, |β z|) := by ring
      _ < 2 * (1 / (8 * L)) := mul_lt_mul_of_pos_left hs (by norm_num)
      _ = _ := by ring
  have ht2 := referenceMark_linear_exp_interior D K hKD α hα hcap
    (fun z ↦ 2 * β z) L hL hG s hdouble
  have heX : (fun Y : Mark K ↦ ∑ z, (2 * β z) * (Y z : ℝ)) = (fun Y ↦ 2 * X Y) := by
    funext Y
    dsimp [X]
    simp only [Finset.mul_sum, mul_assoc]
  rw [heX] at ht2
  exact hasDerivAt_tilted_mean (referenceMarkLaw D K α) H X hmH hH0 s ht
    (weighted_exponential_interior (referenceMarkLaw D K α) H X hmH hH0 hH2 hX s ht2)

end SRWTightness
