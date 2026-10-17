import SRWTightness.CenteredVectorMean
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory WithLp

namespace SRWTightness

/-- Measurable linear images of centered iid observations are independent and have zero mean. -/
theorem iid_centered_linear_vectors {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : ι → Ω → ℝ)
    (hmU : ∀ i, Measurable (U i)) (hU : ∀ i, Integrable (U i) μ)
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (c : ℝ) (k : ℕ) :
    let V : Ω → EuclideanSpace ℝ ι := fun ω ↦ toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ)
    let W := fun ω ↦ c • T (V ω)
    let ν := Measure.pi (fun _ : Fin k ↦ μ)
    iIndepFun (fun i (Y : Fin k → Ω) ↦ W (Y i)) ν ∧
      ∀ i : Fin k, Integrable (fun Y : Fin k → Ω ↦ W (Y i)) ν ∧
        (∫ Y : Fin k → Ω, W (Y i) ∂ν) = 0 := by
  let V : Ω → EuclideanSpace ℝ ι := fun ω ↦ toLp 2 (fun i ↦ U i ω - ∫ z, U i z ∂μ)
  let W := fun ω ↦ c • T (V ω)
  have hm : Measurable W := by dsimp [W, V]; fun_prop
  have hW := centered_linear_vector_mean_zero μ U hU T c
  refine ⟨iIndepFun_pi (X := fun _ ↦ W) (fun _ ↦ hm.aemeasurable), ?_⟩
  intro i
  refine ⟨(measurePreserving_eval (fun _ : Fin k ↦ μ) i).integrable_comp_of_integrable hW.1, ?_⟩
  have he := integral_map (μ := Measure.pi (fun _ : Fin k ↦ μ))
    (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable
  rw [(measurePreserving_eval (fun _ : Fin k ↦ μ) i).map_eq] at he
  exact he.symm.trans hW.2

end SRWTightness
