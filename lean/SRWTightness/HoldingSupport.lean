import SRWTightness.HoldingVector

open MeasureTheory ProbabilityTheory Set

namespace SRWTightness

 theorem exponential_holding_nonneg : ∀ᵐ t : ℝ ∂expMeasure 1, 0 ≤ t := by
  rw [ae_iff]
  have he : {t : ℝ | ¬ 0 ≤ t} = Iio 0 := by ext t; simp
  rw [he]
  change volume.withDensity (exponentialPDF 1) (Iio 0) = 0
  rw [withDensity_apply _ measurableSet_Iio]
  exact lintegral_exponentialPDF_of_nonpos (le_refl 0)

 theorem measurable_continuousMark {A : Finset Site} (Y : Mark A) :
    Measurable (continuousMark Y) := by
  apply measurable_pi_lambda
  intro z
  exact Finset.measurable_sum _ (fun i _ ↦ measurable_pi_apply (⟨z, i⟩ : HoldingIndex Y))

 theorem holdingSample_nonneg {A : Finset Site} (Y : Mark A) :
    ∀ᵐ T ∂holdingTimeLaw Y, ∀ j : HoldingIndex Y, 0 ≤ T j := by
  letI := isProbabilityMeasure_expMeasure (by norm_num : (0 : ℝ) < 1)
  apply Filter.eventually_all.mpr
  intro j
  exact (measurePreserving_eval (fun _ : HoldingIndex Y ↦ expMeasure 1) j).quasiMeasurePreserving.ae
    exponential_holding_nonneg

 theorem continuousMark_nonneg {A : Finset Site} (Y : Mark A) :
    ∀ᵐ T ∂holdingTimeLaw Y, ∀ z : A, 0 ≤ continuousMark Y T z := by
  filter_upwards [holdingSample_nonneg Y] with T hT
  intro z
  exact Finset.sum_nonneg (fun i _ ↦ hT ⟨z, i⟩)

end SRWTightness
