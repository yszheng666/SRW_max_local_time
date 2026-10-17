import SRWTightness.ExternalPositiveConvolution
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Filter
namespace SRWTightness

/-- The conditional real tail of one probability law is globally integrable under another. -/
theorem independent_sum_tail_integrable (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (z : ℝ) :
    Integrable (fun u ↦ μ.real (Ici (z - u))) ν := by
  have hm : Monotone (fun u ↦ μ.real (Ici (z - u))) := by
    intro s t hst
    apply measureReal_mono (h₂ := measure_ne_top μ _)
    intro x hx
    simp only [mem_Ici] at hx ⊢
    linarith
  apply (integrable_const (1 : ℝ)).mono' hm.measurable.aestronglyMeasurable
  filter_upwards [] with u
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- Product conditioning gives the exact real tail integral for any independent real sum. -/
theorem independent_sum_tail_integral (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (z : ℝ) :
    (μ.prod ν).real {p : ℝ × ℝ | z ≤ p.1 + p.2} =
      ∫ u, μ.real (Ici (z - u)) ∂ν := by
  have hs : MeasurableSet {p : ℝ × ℝ | z ≤ p.1 + p.2} :=
    measurableSet_le measurable_const (measurable_fst.add measurable_snd)
  have hslice : ∀ u : ℝ,
      (fun x : ℝ ↦ (x, u)) ⁻¹' {p : ℝ × ℝ | z ≤ p.1 + p.2} = Ici (z - u) := by
    intro u
    ext x
    simp only [mem_preimage, mem_setOf_eq, mem_Ici]
    constructor <;> intro h <;> linarith
  rw [measureReal_def, Measure.prod_apply_symm hs]
  simp_rw [hslice]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ ↦ measureReal_nonneg))
    (independent_sum_tail_integrable μ ν z).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro u
  exact (ofReal_measureReal (measure_ne_top μ (Ici (z - u)))).symm

/-- The original independent nonnegative convolution interface follows from exact conditioning. -/
theorem positive_convolution_input_internal : PositiveConvolutionInput := by
  intro μ ν instμ instν hν z hz
  let f : ℝ → ℝ := fun u ↦ μ.real (Ici (z - u))
  have hf : Integrable f ν := independent_sum_tail_integrable μ ν z
  refine ⟨hf.integrableOn, ?_⟩
  have h₁ : Integrable ((Icc 0 z).indicator f) ν := hf.indicator measurableSet_Icc
  have h₂ : Integrable ((Ici z).indicator (fun _ : ℝ ↦ (1 : ℝ))) ν :=
    (integrable_const (1 : ℝ) (μ := ν)).indicator measurableSet_Ici
  rw [independent_sum_tail_integral μ ν z]
  have hb : ∀ᵐ u ∂ν,
      f u ≤ (Icc 0 z).indicator f u + (Ici z).indicator (fun _ : ℝ ↦ (1 : ℝ)) u := by
    filter_upwards [hν] with u hu
    by_cases hle : u ≤ z
    · have hmem : u ∈ Icc 0 z := ⟨hu, hle⟩
      by_cases hzi : u ∈ Ici z
      · simp only [indicator_of_mem hmem, indicator_of_mem hzi]
        linarith
      · simp only [indicator_of_mem hmem, indicator_of_notMem hzi, add_zero, le_refl]
    · have hnot : u ∉ Icc 0 z := fun h ↦ hle h.2
      have hmem : u ∈ Ici z := le_of_lt (lt_of_not_ge hle)
      simp only [indicator_of_notMem hnot, indicator_of_mem hmem, zero_add]
      exact measureReal_le_one
  have hi := integral_mono_ae hf (h₁.add h₂) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add h₁ h₂, integral_indicator measurableSet_Icc,
    integral_indicator_const (μ := ν) (s := Ici z) (1 : ℝ) measurableSet_Ici,
    smul_eq_mul, mul_one] at hi
  simpa only [f, add_comm] using hi

end SRWTightness
