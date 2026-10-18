import SRWTightness.SourceUpperActualForestError

open Filter
open scoped Topology

namespace SRWTightness

/-- The exact upper terminal radius eventually dominates every fixed multiple of the fine radius. -/
theorem source_upper_radius_dominates_fine (C : ℝ) :
    ∀ᶠ t : ℝ in atTop, C * upperTerminalFineRadius (sourceUpperLogRadius t) ≤
      sourceUpperRadius t := by
  filter_upwards [eventually_ge_atTop (max (max 1 C) (Real.exp 1))] with t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ((le_max_left _ _).trans ht)
  have htC : C ≤ t := (le_max_right _ _).trans ((le_max_left _ _).trans ht)
  have ht0 : 0 < t := by linarith
  have hl : 1 ≤ Real.log t := by
    have h := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans ht)
    simpa only [Real.log_exp] using h
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  have hr : 0 ≤ r := by unfold r upperTerminalFineRadius; positivity
  have hf := source_upper_fine_ratio_bound t ht0 hl
  have hq := (div_le_div_iff₀ (Real.exp_pos (sourceUpperLogRadius t)) ht0).mp hf
  change t * r * t ≤ 1 * sourceUpperRadius t at hq
  have hmul := mul_le_mul_of_nonneg_right (show C ≤ t ^ 2 by nlinarith) hr
  nlinarith only [hq, hmul]

/-- Every geometric and return-error premise of the record comparison holds at the upper scales. -/
theorem source_upper_record_scale_conditions (B T M : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ t : ℝ in atTop,
      1 ≤ sourceUpperBuffer t ∧ 8 * sourceUpperBuffer t ≤ sourceUpperRadius t ∧
      T ≤ sourceUpperRadius t - sourceUpperBuffer t ∧ M ≤ sourceUpperRadius t ∧
      B * sourceUpperBuffer t / sourceUpperRadius t ≤ 1 / 4 ∧
      4 * upperTerminalFineRadius (sourceUpperLogRadius t) <
        sourceUpperRadius t - sourceUpperBuffer t - 2 := by
  filter_upwards [source_upper_radius_dominates_fine (152 + 56 * B + |T| + |M|)] with t ht
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  let m := sourceUpperRadius t
  have hr : 1 ≤ r := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hm : 0 < m := Real.exp_pos _
  have hH : sourceUpperBuffer t = 4 * r + 10 := rfl
  have hHr : sourceUpperBuffer t ≤ 14 * r := by rw [hH]; linarith
  have bound (q : ℝ) (hq : q ≤ 152 + 56 * B + |T| + |M|) : q * r ≤ m :=
    (mul_le_mul_of_nonneg_right hq (by linarith)).trans ht
  have hb := bound 152 (by linarith [abs_nonneg T, abs_nonneg M])
  have hBbig := bound (56 * B) (by linarith [abs_nonneg T, abs_nonneg M])
  have hTbig := bound (14 + |T|) (by linarith [abs_nonneg M])
  have hMbig := bound |M| (by linarith [abs_nonneg T])
  have hTr : T ≤ |T| * r := (le_abs_self T).trans (by nlinarith [abs_nonneg T])
  have hMr : M ≤ |M| * r := (le_abs_self M).trans (by nlinarith [abs_nonneg M])
  refine ⟨by rw [hH]; linarith, by linarith, by linarith, hMr.trans hMbig, ?_, ?_⟩
  · apply (div_le_iff₀ hm).mpr
    have h := mul_le_mul_of_nonneg_left hHr (show 0 ≤ 4 * B by positivity)
    nlinarith
  · linarith

/-- The terminal relative error is small at the actual upper observation radius. -/
theorem source_upper_terminal_comparison_small (W : ℝ) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop,
      W * (2 * upperTerminalFineRadius (sourceUpperLogRadius t) + 1) / sourceUpperRadius t *
        Real.log (sourceUpperRadius t /
          (2 * upperTerminalFineRadius (sourceUpperLogRadius t))) ≤ 1 / 2 := by
  have hlim := (source_upper_actual_forest_error_majorant_vanishes 0 W).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [source_upper_forest_error_bound 0 W (by norm_num) hW, hlim,
    eventually_ge_atTop (1 : ℝ)] with t he hs ht
  let r := upperTerminalFineRadius (sourceUpperLogRadius t)
  have hr : 1 ≤ r := by
    change (1 : ℝ) ≤ (sourceUpperBlockSide t : ℝ)
    exact_mod_cast (show 1 ≤ sourceUpperBlockSide t from sourceUpperBlockSide_pos t)
  have hb := he (2 * r) (by linarith) le_rfl Unit 0 [()] (by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp only [forestLevelPopulation, finiteRecordLevelPopulation, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ite_true, Nat.cast_one]
    nlinarith)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    finiteRecordError] at hb
  change 2 * (W * (2 * r + 1) / sourceUpperRadius t *
    Real.log (sourceUpperRadius t / (2 * r))) ≤ _ at hb
  change W * (2 * r + 1) / sourceUpperRadius t *
    Real.log (sourceUpperRadius t / (2 * r)) ≤ 1 / 2
  linarith only [hb, hs]

end SRWTightness
