import SRWTightness.HoldingSupport
import SRWTightness.LaplaceGenerating
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

noncomputable def holdingKernel (A : Finset Site) : Kernel (Mark A) (A → ℝ) where
  toFun Y := (holdingTimeLaw Y).map (continuousMark Y)
  measurable' := measurable_of_countable _

instance holdingKernel_isMarkov (A : Finset Site) : IsMarkovKernel (holdingKernel A) where
  isProbabilityMeasure Y := Measure.isProbabilityMeasure_map (measurable_continuousMark Y).aemeasurable

 theorem measurable_sumMarks (A : Finset Site) (k : ℕ) : Measurable (sumMarks A k) := by
  apply measurable_pi_lambda
  intro z
  exact Finset.measurable_sum _ (fun i _ ↦
    (measurable_pi_apply z).comp (measurable_pi_apply i))

noncomputable def markCountKernel (D A : Finset Site) (α : ℝ) : Kernel ℕ (Mark A) where
  toFun k := (markProductLaw D A α k).map (sumMarks A k)
  measurable' := measurable_of_countable _

 theorem markCountKernel_isMarkov (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) : IsMarkovKernel (markCountKernel D A α) where
  isProbabilityMeasure k := by
    letI := markProductLaw_isProbabilityMeasure D A α hα hcap k
    exact Measure.isProbabilityMeasure_map (measurable_sumMarks A k).aemeasurable

/-- First choose a Poisson count, then that many independent reference marks, and then
an independent mean-one exponential holding time for every discrete visit. -/
noncomputable def continuousOccupationLaw (D A : Finset Site) (α : ℝ) (r : ℝ≥0) :
    Measure (A → ℝ) := holdingKernel A ∘ₘ (markCountKernel D A α ∘ₘ poissonMeasure r)

 theorem continuousOccupationLaw_isProbabilityMeasure (D A : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (r : ℝ≥0) :
    IsProbabilityMeasure (continuousOccupationLaw D A α r) := by
  letI := markCountKernel_isMarkov D A α hα hcap
  unfold continuousOccupationLaw
  infer_instance

 theorem holdingKernel_laplace (A : Finset Site) (Y : Mark A) (f : A → ℝ)
    (hf : ∀ z, 0 ≤ f z) :
    (∫ L, Real.exp (-(∑ z : A, f z * L z)) ∂holdingKernel A Y) =
      markMonomial (fun z ↦ (1 + f z)⁻¹) Y := by
  change (∫ L, Real.exp (-(∑ z : A, f z * L z))
    ∂(holdingTimeLaw Y).map (continuousMark Y)) = _
  have hm : Measurable (fun L : A → ℝ ↦ Real.exp (-(∑ z : A, f z * L z))) := by fun_prop
  rw [integral_map (measurable_continuousMark Y).aemeasurable hm.aestronglyMeasurable]
  exact holdingVector_laplace Y f hf

end SRWTightness
