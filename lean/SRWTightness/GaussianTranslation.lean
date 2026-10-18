import SRWTightness.GaussianMeanLaw

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Gaussian translations compose by addition of their means. -/
theorem gaussianMeanCoordinateLaw_map_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m n : ι → ℝ) (K : Matrix ι ι ℝ) :
    (gaussianMeanCoordinateLaw m K).map (fun x ↦ n + x) =
      gaussianMeanCoordinateLaw (n + m) K := by
  unfold gaussianMeanCoordinateLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  exact (add_assoc n m x).symm

/-- Translating a Gaussian event is taking its preimage under the translation. -/
theorem gaussianMeanCoordinateLaw_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    (gaussianMeanCoordinateLaw m K).real s =
      (gaussianCoordinateLaw K).real ((fun x ↦ m + x) ⁻¹' s) := by
  exact map_measureReal_apply (by fun_prop) hs

/-- A translation on the Gaussian coordinate leaves independent auxiliary variables unchanged. -/
theorem gaussianMeanCoordinateLaw_prod_real {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s) :
    ((gaussianMeanCoordinateLaw m K).prod ν).real s =
      ((gaussianCoordinateLaw K).prod ν).real ((fun x ↦ (m + x.1, x.2)) ⁻¹' s) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  have he := Measure.map_prod_map (gaussianCoordinateLaw K) ν
    (show Measurable (fun x : ι → ℝ ↦ m + x) by fun_prop) measurable_id
  rw [Measure.map_id] at he
  unfold gaussianMeanCoordinateLaw
  rw [he, map_measureReal_apply (by fun_prop) hs]
  rfl

/-- The same translation identity applies to an already shifted Gaussian with auxiliary variables. -/
theorem gaussianMeanCoordinateLaw_prod_add_real {ι Ξ : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (m n : ι → ℝ) (K : Matrix ι ι ℝ) (s : Set ((ι → ℝ) × Ξ)) (hs : MeasurableSet s) :
    ((gaussianMeanCoordinateLaw (n + m) K).prod ν).real s =
      ((gaussianMeanCoordinateLaw m K).prod ν).real
        ((fun x ↦ (n + x.1, x.2)) ⁻¹' s) := by
  letI := gaussianMeanCoordinateLaw_isProbabilityMeasure m K
  have he := Measure.map_prod_map (gaussianMeanCoordinateLaw m K) ν
    (show Measurable (fun x : ι → ℝ ↦ n + x) by fun_prop) measurable_id
  rw [Measure.map_id, gaussianMeanCoordinateLaw_map_add] at he
  rw [he, map_measureReal_apply (by fun_prop) hs]
  rfl

end SRWTightness
