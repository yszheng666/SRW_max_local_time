import SRWTightness.DyadicTimeApproximation
import SRWTightness.GaussianDyadicProcess
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

theorem gaussianDyadicPath_vector_distribution_limit {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    TendstoInDistribution
      (fun n ω i ↦ gaussianDyadicPath ω (dyadicTime n (t i))) atTop
      (fun ω i ↦ gaussianDyadicPath ω (t i))
      (fun _ ↦ gaussianCoefficientLaw) gaussianCoefficientLaw := by
  apply tendstoInDistribution_of_ae_tendsto
  · intro n
    exact (measurable_pi_lambda _ (fun i ↦ gaussianDyadicPath_measurable _)).aemeasurable
  · exact (measurable_pi_lambda _ (fun i ↦ gaussianDyadicPath_measurable _)).aemeasurable
  · exact gaussianDyadicPath_ae_vector_limit t ht

theorem gaussianDyadicPath_linear_distribution_limit {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    TendstoInDistribution
      (fun n ω ↦ ∑ i, a i * gaussianDyadicPath ω (dyadicTime n (t i))) atTop
      (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (t i))
      (fun _ ↦ gaussianCoefficientLaw) gaussianCoefficientLaw := by
  have hc : Continuous (fun x : ι → ℝ ↦ ∑ i, a i * x i) := by fun_prop
  simpa only [Function.comp_def] using
    (gaussianDyadicPath_vector_distribution_limit t ht).continuous_comp
      (g := fun x : ι → ℝ ↦ ∑ i, a i * x i) hc

theorem gaussianDyadicPath_linear_charFun_limit {ι : Type*} [Fintype ι]
    (t a : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (u : ℝ) :
    Tendsto (fun n ↦ charFun (gaussianCoefficientLaw.map
      (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (dyadicTime n (t i)))) u)
      atTop (nhds (charFun (gaussianCoefficientLaw.map
        (fun ω ↦ ∑ i, a i * gaussianDyadicPath ω (t i))) u)) := by
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
    (gaussianDyadicPath_linear_distribution_limit t a ht).tendsto u

end SRWTightness
