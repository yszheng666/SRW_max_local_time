import SRWTightness.TimeCenterIncrement

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem timeCenter_increment_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |timeCenter (n + 1) - timeCenter n| ≤ C := by
  have h : Tendsto (fun n : ℕ ↦ |timeCenter (n + 1) - timeCenter n|) atTop (𝓝 0) := by
    simpa using timeCenter_increment_tendsto_zero.abs
  have he : ∀ᶠ n : ℕ in atTop, |timeCenter (n + 1) - timeCenter n| < 1 :=
    h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  let C : ℝ := 1 + ∑ k ∈ Finset.range N, |timeCenter (k + 1) - timeCenter k|
  have hs : 0 ≤ ∑ k ∈ Finset.range N, |timeCenter (k + 1) - timeCenter k| :=
    Finset.sum_nonneg (fun k _ ↦ abs_nonneg _)
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro n
  dsimp [C]
  by_cases hn : n < N
  · have hb := Finset.single_le_sum (fun k (_ : k ∈ Finset.range N) ↦ abs_nonneg (timeCenter (k + 1) - timeCenter k)) (Finset.mem_range.mpr hn)
    linarith
  · have hb := hN n (by omega)
    linarith

/-- The inclusive endpoint convention follows from the half-open actual-walk theorem. -/
theorem inclusiveTimeTightness_of_timeTightness (h : TimeTightnessClaim) : InclusiveTimeTightnessClaim := by
  intro ε hε
  obtain ⟨K, hK, htail⟩ := h ε hε
  obtain ⟨C, hC, hinc⟩ := timeCenter_increment_bounded
  refine ⟨K + C, add_nonneg hK hC, ?_⟩
  intro n hn
  have hsub : {ω | K + C < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n|} ⊆
      {ω | K < |timeFluctuation (n + 1) ω|} := by
    intro ω hω
    change K < |timeFluctuation (n + 1) ω|
    have ht : |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n| ≤
        |timeFluctuation (n + 1) ω| + |timeCenter (n + 1) - timeCenter n| := by
      rw [inclusiveMaxLocalTime_eq]
      have he : Real.sqrt (maxLocalTime ω (n + 1)) - timeCenter n =
          timeFluctuation (n + 1) ω + (timeCenter (n + 1) - timeCenter n) := by
        unfold timeFluctuation
        ring
      rw [he]
      exact abs_add_le _ _
    have hh : K + C < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n| := hω
    linarith [hinc n]
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans_lt (htail (n + 1) (by omega))

end SRWTightness
