import SRWTightness.ContinuousOccupation

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem measurableSet_nonneg_field (A : Finset Site) :
    MeasurableSet {L : A → ℝ | ∀ z : A, 0 ≤ L z} := by
  rw [Set.setOf_forall]
  exact MeasurableSet.iInter (fun z ↦ measurableSet_le measurable_const (measurable_pi_apply z))

 theorem holdingKernel_nonneg (A : Finset Site) (Y : Mark A) :
    ∀ᵐ L ∂holdingKernel A Y, ∀ z : A, 0 ≤ L z := by
  change ∀ᵐ L ∂(holdingTimeLaw Y).map (continuousMark Y), ∀ z : A, 0 ≤ L z
  exact (ae_map_iff (measurable_continuousMark Y).aemeasurable
    (measurableSet_nonneg_field A)).mpr (continuousMark_nonneg Y)

 theorem continuousOccupationLaw_nonneg (D A : Finset Site) (α : ℝ) (r : ℝ≥0) :
    ∀ᵐ L ∂continuousOccupationLaw D A α r, ∀ z : A, 0 ≤ L z := by
  apply Measure.ae_comp_of_ae_ae (measurableSet_nonneg_field A)
  exact Filter.Eventually.of_forall (holdingKernel_nonneg A)

noncomputable def occupationLaplace {A : Finset Site} (f : A → ℝ) (L : A → ℝ) : ℝ :=
  Real.exp (-(∑ z : A, f z * L z))

 theorem measurable_occupationLaplace {A : Finset Site} (f : A → ℝ) :
    Measurable (occupationLaplace f) := by unfold occupationLaplace; fun_prop

 theorem norm_occupationLaplace_le_one {A : Finset Site} (f : A → ℝ)
    (hf : ∀ z, 0 ≤ f z) (L : A → ℝ) (hL : ∀ z, 0 ≤ L z) :
    ‖occupationLaplace f L‖ ≤ 1 := by
  rw [occupationLaplace, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun z _ ↦ mul_nonneg (hf z) (hL z)))

 theorem integrable_occupationLaplace {A : Finset Site} (μ : Measure (A → ℝ))
    [IsFiniteMeasure μ] (hμ : ∀ᵐ L ∂μ, ∀ z : A, 0 ≤ L z) (f : A → ℝ) (hf : ∀ z, 0 ≤ f z) :
    Integrable (occupationLaplace f) μ := by
  refine ⟨(measurable_occupationLaplace f).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  exact hμ.mono (fun L hL ↦ norm_occupationLaplace_le_one f hf L hL)

 theorem integral_kernel_comp_real {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    (μ : Measure X) (κ : Kernel X Z) (F : Z → ℝ) (hI : Integrable F (κ ∘ₘ μ)) :
    (∫ z, F z ∂(κ ∘ₘ μ)) = ∫ x, (∫ z, F z ∂κ x) ∂μ := by
  rw [Measure.comp_eq_comp_const_apply] at hI ⊢
  exact ProbabilityTheory.Kernel.integral_comp hI

end SRWTightness
