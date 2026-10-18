import SRWTightness.OccupationGaussianIsomorphism
import SRWTightness.ContinuousCountComparison

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

def shiftedGaussianExceedance (A : Finset Site) (u : ℝ) (a : ℕ) :
    Set (EuclideanSpace ℝ A) := {φ | ∃ z, Real.sqrt (2 * (a : ℝ)) ≤ |φ z + Real.sqrt (2 * u)|}

theorem measurableSet_shiftedGaussianExceedance (A : Finset Site) (u : ℝ) (a : ℕ) :
    MeasurableSet (shiftedGaussianExceedance A u a) := by
  unfold shiftedGaussianExceedance
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro z
  exact measurableSet_le measurable_const (by fun_prop)

theorem shiftedGaussianSquareLaw_exceedance (D A : Finset Site) (u : ℝ) (a : ℕ) :
    (shiftedGaussianSquareLaw D A u).real (continuousExceedance A a) =
      (gaussianGreenLaw D A).real (shiftedGaussianExceedance A u a) := by
  rw [shiftedGaussianSquareLaw,
    map_measureReal_apply (measurable_shiftedGaussianSquare A u)
      (measurableSet_continuousExceedance A a)]
  congr 1
  ext φ
  apply exists_congr
  intro z
  change (a : ℝ) ≤ (φ z + Real.sqrt (2 * u)) ^ 2 / 2 ↔ _
  rw [Real.sqrt_le_left (abs_nonneg _), sq_abs]
  constructor <;> intro h <;> linarith

theorem continuous_exceedance_le_shifted_gaussian (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0) (a : ℕ) :
    (continuousOccupationLaw D A α r).real (continuousExceedance A a) ≤
      (gaussianGreenLaw D A).real (shiftedGaussianExceedance A ((r : ℝ) * α) a) := by
  letI := continuousOccupationLaw_isProbabilityMeasure D A α hα hcap r
  have hC := measurableSet_continuousExceedance A a
  have he := congrArg (fun μ : Measure (A → ℝ) ↦ μ.real (continuousExceedance A a))
    (occupation_gaussian_isomorphism D A hAD α hα hcap r)
  rw [shiftedGaussianSquareLaw_exceedance, occupationPlusGaussianSquareLaw,
    map_measureReal_apply (measurable_occupationPlusGaussianSquare A) hC] at he
  rw [← he]
  have hp := (measurePreserving_fst (μ := continuousOccupationLaw D A α r)
    (ν := gaussianGreenLaw D A)).map_eq
  have hfst : ((continuousOccupationLaw D A α r).prod (gaussianGreenLaw D A)).real
      (Prod.fst ⁻¹' continuousExceedance A a) =
        (continuousOccupationLaw D A α r).real (continuousExceedance A a) := by
    rw [← map_measureReal_apply measurable_fst hC, hp]
  rw [← hfst]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro ⟨L, φ⟩ ⟨z, hz⟩
  exact ⟨z, hz.trans (le_add_of_nonneg_right (by positivity))⟩

/-- The actual discrete-to-Gaussian comparison, with a universal constant 576. -/
theorem fixed_mark_exceedance_le_gaussian (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1)
    (k a : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    fixedMarkExceedance D A α k a ≤
      576 * (gaussianGreenLaw D A).real (shiftedGaussianExceedance A ((k : ℝ) * α) a) := by
  exact (fixed_mark_exceedance_le_continuous D A α hα hcap k a hk ha).trans
    (mul_le_mul_of_nonneg_left
      (continuous_exceedance_le_shifted_gaussian D A hAD α hα hcap (k : ℝ≥0) a) (by norm_num))

/-- Manuscript Lemma `oneway` and (3.5), including observation inside larger reference marks. -/
theorem projected_fixed_mark_exceedance_le_gaussian (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (k a : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    (markProductLaw D K α k).real
      {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
        576 * (gaussianGreenLaw D A).real
          (shiftedGaussianExceedance A ((k : ℝ) * α) a) := by
  have hp := (markProductLaw_restrict D A K hAK hKD α hα hcap k).map_eq
  have he : fixedMarkExceedance D A α k a =
      (markProductLaw D K α k).real
        {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩} := by
    unfold fixedMarkExceedance
    rw [← hp, map_measureReal_apply (markProductLaw_restrict D A K hAK hKD α hα hcap k).measurable
      MeasurableSet.of_discrete]
    rfl
  rw [← he]
  exact fixed_mark_exceedance_le_gaussian D A (hAK.trans hKD) α hα
    ((mul_le_mul_of_nonneg_left (capacity_mono_set D A K hAK hKD) hα).trans hcap)
    k a hk ha

end SRWTightness
