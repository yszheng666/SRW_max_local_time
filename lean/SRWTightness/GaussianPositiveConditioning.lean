import SRWTightness.PositiveConvolutionInternal

open MeasureTheory Set Filter
namespace SRWTightness

/-- A real positive-part sum has a globally integrable conditional probability kernel. -/
theorem positive_part_sum_tail_integrable (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a : ℝ) :
    Integrable (fun x ↦ ν.real (Ici (a - max x 0))) μ := by
  have hm : Monotone (fun x ↦ ν.real (Ici (a - max x 0))) := by
    intro s t hst
    apply measureReal_mono (h₂ := measure_ne_top ν _)
    intro y hy
    have hmax := max_le_max hst (le_refl (0 : ℝ))
    simp only [mem_Ici] at hy ⊢
    linarith
  apply (integrable_const (1 : ℝ)).mono' hm.measurable.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

/-- Exact conditioning on the first scalar preserves the original positive-part event. -/
theorem positive_part_sum_tail_integral (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a : ℝ) :
    (μ.prod ν).real {p : ℝ × ℝ | a ≤ max p.1 0 + p.2} =
      ∫ x, ν.real (Ici (a - max x 0)) ∂μ := by
  have hs : MeasurableSet {p : ℝ × ℝ | a ≤ max p.1 0 + p.2} :=
    measurableSet_le measurable_const ((measurable_fst.max measurable_const).add measurable_snd)
  have hslice : ∀ x : ℝ,
      (fun y : ℝ ↦ (x, y)) ⁻¹' {p : ℝ × ℝ | a ≤ max p.1 0 + p.2} =
        Ici (a - max x 0) := by
    intro x
    ext y
    simp only [mem_preimage, mem_setOf_eq, mem_Ici]
    constructor <;> intro h <;> linarith
  rw [measureReal_def, Measure.prod_apply hs]
  simp_rw [hslice]
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (fun _ ↦ measureReal_nonneg))
    (positive_part_sum_tail_integrable μ ν a).aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro x
  exact (ofReal_measureReal (measure_ne_top ν (Ici (a - max x 0)))).symm

/-- Three scalar regions bound the positive-part sum without requiring a density for the other law.
-/
theorem positive_part_sum_three_region_bound (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (a : ℝ) (ha : 0 < a) :
    (μ.prod ν).real {p : ℝ × ℝ | a ≤ max p.1 0 + p.2} ≤
      μ.real (Ici a) + ν.real (Ici a) + ∫ x in Icc 0 a, ν.real (Ici (a - x)) ∂μ := by
  let f : ℝ → ℝ := fun x ↦ ν.real (Ici (a - x))
  let g : ℝ → ℝ := fun x ↦ ν.real (Ici (a - max x 0))
  have hf : Integrable f μ := independent_sum_tail_integrable ν μ a
  have hg : Integrable g μ := positive_part_sum_tail_integrable μ ν a
  have h₀ : Integrable ((Iic 0).indicator (fun _ : ℝ ↦ ν.real (Ici a))) μ :=
    (integrable_const _).indicator measurableSet_Iic
  have h₁ : Integrable ((Ici a).indicator (fun _ : ℝ ↦ (1 : ℝ))) μ :=
    (integrable_const _).indicator measurableSet_Ici
  have h₂ : Integrable ((Icc 0 a).indicator f) μ := hf.indicator measurableSet_Icc
  have hb : ∀ x : ℝ, g x ≤ (Iic 0).indicator (fun _ : ℝ ↦ ν.real (Ici a)) x +
      (Ici a).indicator (fun _ : ℝ ↦ (1 : ℝ)) x + (Icc 0 a).indicator f x := by
    intro x
    by_cases hx : x ≤ 0
    · have h₀mem : x ∈ Iic 0 := hx
      have h₁not : x ∉ Ici a := fun h ↦ by
        simp only [mem_Ici] at h
        linarith
      by_cases h₂mem : x ∈ Icc 0 a
      · simp only [g, max_eq_right hx, sub_zero, indicator_of_mem h₀mem,
          indicator_of_notMem h₁not, indicator_of_mem h₂mem, add_zero]
        exact le_add_of_nonneg_right measureReal_nonneg
      · simp only [g, max_eq_right hx, sub_zero, indicator_of_mem h₀mem,
          indicator_of_notMem h₁not, indicator_of_notMem h₂mem, add_zero, le_refl]
    · have hx0 : 0 < x := lt_of_not_ge hx
      have h₀not : x ∉ Iic 0 := hx
      by_cases hxa : a ≤ x
      · have h₁mem : x ∈ Ici a := hxa
        by_cases h₂mem : x ∈ Icc 0 a
        · simp only [indicator_of_notMem h₀not, indicator_of_mem h₁mem,
            indicator_of_mem h₂mem, zero_add]
          exact measureReal_le_one.trans (le_add_of_nonneg_right measureReal_nonneg)
        · simp only [indicator_of_notMem h₀not, indicator_of_mem h₁mem,
            indicator_of_notMem h₂mem, zero_add, add_zero]
          exact measureReal_le_one
      · have h₁not : x ∉ Ici a := hxa
        have h₂mem : x ∈ Icc 0 a := ⟨hx0.le, (lt_of_not_ge hxa).le⟩
        simp only [g, f, max_eq_left hx0.le, indicator_of_notMem h₀not,
          indicator_of_notMem h₁not, indicator_of_mem h₂mem, zero_add, le_refl]
  have hi := integral_mono_ae hg ((h₀.add h₁).add h₂) (Eventually.of_forall hb)
  simp only [Pi.add_apply] at hi
  have h₀₁ : Integrable (fun x : ℝ ↦
      (Iic 0).indicator (fun _ : ℝ ↦ ν.real (Ici a)) x +
      (Ici a).indicator (fun _ : ℝ ↦ (1 : ℝ)) x) μ := h₀.add h₁
  rw [integral_add h₀₁ h₂, integral_add h₀ h₁,
    integral_indicator_const (ν.real (Ici a)) measurableSet_Iic,
    integral_indicator_const (1 : ℝ) measurableSet_Ici,
    integral_indicator measurableSet_Icc] at hi
  simp only [smul_eq_mul, mul_one] at hi
  have hbase : μ.real (Iic 0) * ν.real (Ici a) ≤ ν.real (Ici a) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (measureReal_le_one (μ := μ) (s := Iic 0)) (measureReal_nonneg (μ := ν) (s := Ici a))
  rw [positive_part_sum_tail_integral μ ν a]
  dsimp only [f, g] at hi
  linarith

end SRWTightness
