import SRWTightness.DiskTimeTailComparison

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Only the lower tail of the inner disk and the upper tail of the outer disk are needed. -/
theorem time_tail_le_one_sided_disk_tails (A : ℝ) (hA : 1 < A) (n : ℕ) (hn : 1 ≤ n)
    (K C : ℝ)
    (hlo : |diskCenter (Real.sqrt n / A) - timeCenter n| ≤ C)
    (hhi : |diskCenter (A * Real.sqrt n) - timeCenter n| ≤ C) :
    pathLaw.real {ω | K + C < |timeFluctuation n ω|} ≤
      (2 / A ^ 2 + 2 / (A * Real.sqrt n) + 1 / n) +
      pathLaw.real {ω | diskFluctuation (Real.sqrt n / A) ω < -K} +
      pathLaw.real {ω | K < diskFluctuation (A * Real.sqrt n) ω} := by
  let E : Set Sample := {ω | ¬ (exitTime (Real.sqrt n / A) ω ≤ n ∧
    (n : WithTop ℕ) ≤ exitTime (A * Real.sqrt n) ω)}
  let L : Set Sample := {ω | diskFluctuation (Real.sqrt n / A) ω < -K}
  let U : Set Sample := {ω | K < diskFluctuation (A * Real.sqrt n) ω}
  have hsub : {ω | K + C < |timeFluctuation n ω|} ≤ᵐ[pathLaw] (((E ∪ L) ∪ U) : Set Sample) := by
    filter_upwards [ae_scaled_disk_time_sandwich A hA n] with ω hs
    intro ht
    by_contra hbad
    have he : ω ∉ E := fun he ↦ hbad (Or.inl (Or.inl he))
    have hl : ω ∉ L := fun hl ↦ hbad (Or.inl (Or.inr hl))
    have hu : ω ∉ U := fun hu ↦ hbad (Or.inr hu)
    have hg : exitTime (Real.sqrt n / A) ω ≤ n ∧
        (n : WithTop ℕ) ≤ exitTime (A * Real.sqrt n) ω := by simpa [E] using he
    obtain ⟨hsl, hsu⟩ := hs hg
    have hsl' : Real.sqrt (diskMax (Real.sqrt n / A) ω) ≤ Real.sqrt (maxLocalTime ω n) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hsl)
    have hsu' : Real.sqrt (maxLocalTime ω n) ≤ Real.sqrt (diskMax (A * Real.sqrt n) ω) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hsu)
    have hl' : -K ≤ diskFluctuation (Real.sqrt n / A) ω := le_of_not_gt hl
    have hu' : diskFluctuation (A * Real.sqrt n) ω ≤ K := le_of_not_gt hu
    obtain ⟨hcl, hcu⟩ := abs_le.mp hlo
    obtain ⟨hdl, hdu⟩ := abs_le.mp hhi
    have hb : |timeFluctuation n ω| ≤ K + C := by
      apply abs_le.mpr
      dsimp [timeFluctuation, diskFluctuation] at *
      constructor <;> linarith
    exact (not_lt_of_ge hb) ht
  have hm : pathLaw.real {ω | K + C < |timeFluctuation n ω|} ≤ pathLaw.real ((E ∪ L) ∪ U) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  have hu := measureReal_union_le (μ := pathLaw) (E ∪ L) U
  have hl := measureReal_union_le (μ := pathLaw) E L
  have he := prob_scaled_disk_comparison_failure A hA n hn
  change pathLaw.real E ≤ _ at he
  change _ ≤ _ + pathLaw.real L + pathLaw.real U
  linarith

theorem scaled_center_source_eventual (A : ℝ) (hA : 1 < A) :
    ∀ᶠ n : ℕ in atTop,
      |diskCenter (Real.sqrt n / A) - timeCenter n| ≤
        (Real.log 2 + 2 * Real.log A) / Real.sqrt Real.pi + 1 ∧
      |diskCenter (A * Real.sqrt n) - timeCenter n| ≤
        (Real.log 2 + 2 * Real.log A) / Real.sqrt Real.pi + 1 := by
  have hAp : 0 < A := by linarith
  have hlA : 0 < Real.log A := Real.log_pos hA
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hlo := (diskCenter_sqrt_scale_sub_timeCenter_tendsto (1 / A) (by positivity)).abs
  have hhi := (diskCenter_sqrt_scale_sub_timeCenter_tendsto A hAp).abs
  have habs : |(Real.log 2 + 2 * Real.log (1 / A)) / Real.sqrt Real.pi| ≤
      (Real.log 2 + 2 * Real.log A) / Real.sqrt Real.pi := by
    rw [abs_div, abs_of_pos hsq]
    apply div_le_div_of_nonneg_right _ hsq.le
    rw [one_div, Real.log_inv]
    apply abs_le.mpr
    constructor <;> linarith
  have hblo := hlo.eventually (gt_mem_nhds (show
      |(Real.log 2 + 2 * Real.log (1 / A)) / Real.sqrt Real.pi| <
      (Real.log 2 + 2 * Real.log A) / Real.sqrt Real.pi + 1 by linarith))
  have hbhi := hhi.eventually (gt_mem_nhds (show
      |(Real.log 2 + 2 * Real.log A) / Real.sqrt Real.pi| <
      (Real.log 2 + 2 * Real.log A) / Real.sqrt Real.pi + 1 by
        rw [abs_of_pos (by positivity)]; linarith))
  filter_upwards [hblo, hbhi] with n hn₁ hn₂
  constructor
  · simpa [div_eq_mul_inv, mul_comm] using hn₁.le
  · exact hn₂.le

end SRWTightness
