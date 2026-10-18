import SRWTightness.DiskTimeTailComparison
import SRWTightness.InclusiveTightnessTransfer

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem scaled_center_eventual_bound (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ c * Real.sqrt n ∧ |diskCenter (c * Real.sqrt n) - timeCenter n| ≤ C := by
  let L := (Real.log 2 + 2 * Real.log c) / Real.sqrt Real.pi
  have hlim := (diskCenter_sqrt_scale_sub_timeCenter_tendsto c hc).abs
  have hb : ∀ᶠ n : ℕ in atTop, |diskCenter (c * Real.sqrt n) - timeCenter n| < |L| + 1 :=
    hlim.eventually (gt_mem_nhds (by dsimp [L]; linarith))
  have hs : Tendsto (fun n : ℕ ↦ c * Real.sqrt (n : ℝ)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  refine ⟨|L| + 1, by positivity, ?_⟩
  filter_upwards [hb, hs.eventually (eventually_ge_atTop 2)] with n hn hr
  exact ⟨hr, hn.le⟩

/-- Deterministic finite-prefix control upgrades eventual tail tightness to all n≥3. -/
theorem timeTightness_of_eventual_tails
    (h : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ n : ℕ in atTop, pathLaw.real {ω | K < |timeFluctuation n ω|} < ε) :
    TimeTightnessClaim := by
  intro ε hε
  obtain ⟨K, hK, htail⟩ := h ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp htail
  let B : ℝ := ∑ k ∈ Finset.range N, (Real.sqrt k + |timeCenter k|)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ ↦ by positivity)
  refine ⟨K + B, add_nonneg hK hB, ?_⟩
  intro n _
  by_cases hn : N ≤ n
  · have hsub : {ω | K + B < |timeFluctuation n ω|} ⊆ {ω | K < |timeFluctuation n ω|} := by
      intro ω hω
      change K < |timeFluctuation n ω|
      change K + B < |timeFluctuation n ω| at hω
      linarith
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans_lt (hN n hn)
  · have hb : Real.sqrt n + |timeCenter n| ≤ B :=
      Finset.single_le_sum (fun k (_ : k ∈ Finset.range N) ↦
        show 0 ≤ Real.sqrt (k : ℝ) + |timeCenter k| by positivity)
        (Finset.mem_range.mpr (by omega))
    have hbound (ω : Sample) : |timeFluctuation n ω| ≤ K + B := by
      have hs : Real.sqrt (maxLocalTime ω n) ≤ Real.sqrt (n : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast maxLocalTime_le_time ω n)
      have ht := abs_sub (Real.sqrt (maxLocalTime ω n)) (timeCenter n)
      rw [abs_of_nonneg (Real.sqrt_nonneg _)] at ht
      dsimp [timeFluctuation]
      linarith
    have he : {ω | K + B < |timeFluctuation n ω|} = (∅ : Set Sample) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact (not_lt_of_ge (hbound ω)) hω
    simpa only [he, measureReal_empty] using hε

/-- The source's time-tightness deduction, conditional only on its disk-tightness theorem. -/
theorem timeTightness_of_diskTightness (h : DiskTightnessClaim) : TimeTightnessClaim := by
  apply timeTightness_of_eventual_tails
  intro ε hε
  let A : ℝ := 8 / ε + 2
  have hA : 1 < A := by dsimp [A]; have := div_pos (by norm_num : (0 : ℝ) < 8) hε; linarith
  have hAp : 0 < A := by linarith
  have hAe : 8 < ε * A := by dsimp [A]; field_simp; nlinarith
  have hAA : A ≤ A ^ 2 := by nlinarith
  have herr : 2 / A ^ 2 < ε / 4 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hAp)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hAA hε.le]
  have hlim := scaled_disk_comparison_error_tendsto A hAp
  have hevent : ∀ᶠ n : ℕ in atTop,
      2 / A ^ 2 + 2 / (A * Real.sqrt n) + 1 / (n : ℝ) < ε / 2 :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨C₁, hC₁, h₁⟩ := scaled_center_eventual_bound (1 / A) (by positivity)
  obtain ⟨C₂, hC₂, h₂⟩ := scaled_center_eventual_bound A hAp
  obtain ⟨K, hK, ht⟩ := h 2 (by norm_num) (ε / 4) (by positivity)
  refine ⟨K + (C₁ + C₂), by positivity, ?_⟩
  filter_upwards [hevent, h₁, h₂, eventually_ge_atTop (1 : ℕ)] with n he hn₁ hn₂ hn
  have hr₁ : 2 ≤ Real.sqrt n / A := by simpa [div_eq_mul_inv, mul_comm] using hn₁.1
  have hc₁ : |diskCenter (Real.sqrt n / A) - timeCenter n| ≤ C₁ := by
    simpa [div_eq_mul_inv, mul_comm] using hn₁.2
  have hcomp := time_tail_le_disk_tails A hA n hn K (C₁ + C₂)
    (by linarith) (by linarith [hn₂.2])
  have ht₁ := ht (Real.sqrt n / A) hr₁
  have ht₂ := ht (A * Real.sqrt n) hn₂.1
  linarith

theorem inclusiveTimeTightness_of_diskTightness (h : DiskTightnessClaim) : InclusiveTimeTightnessClaim :=
  inclusiveTimeTightness_of_timeTightness (timeTightness_of_diskTightness h)

end SRWTightness
