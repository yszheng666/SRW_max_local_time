import SRWTightness.SourceEarlyRootPairMeanError
import SRWTightness.SourceEarlyCommonNumericalError

open MeasureTheory Filter
namespace SRWTightness

/-- The first-mean error remains uniformly small after the full quadratic mark weight. -/
theorem source_early_weighted_mean_error (hLast : FiniteLastVisitCountInput)
    (hinput : PotentialKernelAsymptoticInput) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let μ := ∫ Y, ((sourceCommonWordRootCount t b ν Y +
        sourceCommonWordRootCount t w ν Y : ℕ) : ℝ) ∂sourceCommonWordLaw t b w j
      ((j : ℝ) + 1) ^ 2 * |μ - 2| ≤ D / t ^ 5 := by
  obtain ⟨C, hC, Jmin, hmean⟩ := source_early_root_pair_mean_error hLast hinput
  refine ⟨4 * (224 + C), by positivity, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨am, ham, hm⟩ := hmean J₀ hJ₀
  obtain ⟨al, hl⟩ := source_early_distance_levels J₀
  refine ⟨max am al, ham.trans (le_max_left _ _), ?_⟩
  filter_upwards [hm, hl, source_early_level_bounds,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hm hl ht hscale
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let μ := ∫ Y, ((sourceCommonWordRootCount t b ν Y +
    sourceCommonWordRootCount t w ν Y : ℕ) : ℝ) ∂sourceCommonWordLaw t b w j
  have herr := hm b w hbw ((le_max_left _ _).trans ha) hrange
  have hν := (hl a ((le_max_right _ _).trans ha) hrange).2.2
  have hj : j ≤ 2 * sourceCoarseLowerLevel t := by dsimp [j]; omega
  have hrj := sourceCommonPairInnerRadius_ge_lower t j (ht.2 j hj).1
  have hrν := sourceCommonPairInnerRadius_ge_lower t ν (ht.2 ν hν).1
  have hm0 := sourceLowerRadius_pos t
  have ht0 : 0 < t := by linarith [ht.1]
  have hsq : ((j : ℝ) + 1) ^ 2 ≤ 4 * t ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ (j : ℝ) + 1)
      (show (j : ℝ) + 1 ≤ 2 * t by linarith [(ht.2 j hj).2.1, ht.1]) 2
    nlinarith only [hh]
  have herr' : |μ - 2| ≤ (224 + C) / sourceLowerRadius t := by
    calc
      _ ≤ 224 / sourceCommonPairInnerRadius t j +
          C / sourceCommonPairInnerRadius t ν := herr
      _ ≤ 224 / sourceLowerRadius t + C / sourceLowerRadius t :=
        add_le_add (div_le_div_of_nonneg_left (by norm_num) hm0 hrj)
          (div_le_div_of_nonneg_left hC hm0 hrν)
      _ = _ := by ring
  have hmajor : t ^ 2 / sourceLowerRadius t ≤ 1 / t ^ 5 := by
    have hh := div_le_div_of_nonneg_left (sq_nonneg t) (pow_pos ht0 7)
      (sourceLowerRadius_ge_seventh_power t hscale)
    exact hh.trans_eq (by field_simp [ht0.ne'])
  calc
    _ ≤ (4 * t ^ 2) * ((224 + C) / sourceLowerRadius t) :=
      mul_le_mul hsq herr' (abs_nonneg _) (by positivity)
    _ = (4 * (224 + C)) * (t ^ 2 / sourceLowerRadius t) := by ring
    _ ≤ (4 * (224 + C)) * (1 / t ^ 5) :=
      mul_le_mul_of_nonneg_left hmajor (by positivity)
    _ = _ := by ring

end SRWTightness
