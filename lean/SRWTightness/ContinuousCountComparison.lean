import SRWTightness.HoldingComparison
import SRWTightness.KernelEventProbability
import SRWTightness.MarkPoissonization

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem poissonized_mark_exceedance_eq (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (r : ℝ≥0) (a : ℕ) :
    (markCountKernel D A α ∘ₘ poissonMeasure r).real {Y : Mark A | ∃ z : A, a ≤ Y z} =
      ∫ n : ℕ, fixedMarkExceedance D A α n a ∂poissonMeasure r := by
  letI := markCountKernel_isMarkov D A α hα hcap
  have hE : MeasurableSet {Y : Mark A | ∃ z : A, a ≤ Y z} := MeasurableSet.of_discrete
  rw [measure_comp_real_event _ _ _ hE]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro n
  change ((markProductLaw D A α n).map (sumMarks A n)).real _ = _
  rw [measureReal_def, Measure.map_apply (measurable_sumMarks A n) hE]
  rfl

/-- Conditional exponential holding loses at most 36, uniformly in the observation set. -/
theorem poissonized_mark_exceedance_le_continuous (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (r : ℝ≥0) (a : ℕ) (ha : 1 ≤ a) :
    (∫ n : ℕ, fixedMarkExceedance D A α n a ∂poissonMeasure r) ≤
      36 * (continuousOccupationLaw D A α r).real (continuousExceedance A a) := by
  letI := markCountKernel_isMarkov D A α hα hcap
  let μ := markCountKernel D A α ∘ₘ poissonMeasure r
  let E := {Y : Mark A | ∃ z : A, a ≤ Y z}
  have hE : MeasurableSet E := MeasurableSet.of_discrete
  have hC := measurableSet_continuousExceedance A a
  have hI : Integrable (E.indicator (fun _ ↦ (1 : ℝ))) μ := (integrable_const _).indicator hE
  have hJ : Integrable (fun Y ↦ 36 * (holdingKernel A Y).real (continuousExceedance A a)) μ :=
    (integrable_kernel_event_probability μ (holdingKernel A) _ hC).const_mul _
  have hb := integral_mono hI hJ (count_indicator_le_holding_exceedance A a ha)
  rw [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one, integral_const_mul,
    ← measure_comp_real_event μ (holdingKernel A) _ hC] at hb
  rw [← poissonized_mark_exceedance_eq D A α hα hcap r a]
  exact hb

/-- The two dimension-free probabilistic comparison steps preceding Gaussian isomorphism. -/
theorem fixed_mark_exceedance_le_continuous (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (k a : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a) :
    fixedMarkExceedance D A α k a ≤
      576 * (continuousOccupationLaw D A α (k : ℝ≥0)).real (continuousExceedance A a) := by
  have hP := fixedMarkExceedance_le_poissonized D A α hα hcap k a hk
  have hH := poissonized_mark_exceedance_le_continuous D A α hα hcap (k : ℝ≥0) a ha
  linarith

end SRWTightness
