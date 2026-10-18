import SRWTightness.SourceEarlySingleMarkLogMoment
import SRWTightness.SourceEarlyWeightedMeanError
import SRWTightness.RootLogMeanReplacement
import SRWTightness.ProductCgf

open MeasureTheory ProbabilityTheory Filter
namespace SRWTightness

/-- The explicit error in the early independent-mark logarithmic moment tends to zero. -/
theorem source_early_product_log_error_tendsto (A D : ℝ) :
    Tendsto (fun t : ℝ ↦ A * D / t ^ 5) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (5 : ℕ) ≠ 0))

/-- Equation 8.20 for the actual product of common reference word laws, with uniform error. -/
theorem source_early_product_log_moment (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let N := fun Y ↦ sourceCommonWordRootCount t b ν Y + sourceCommonWordRootCount t w ν Y
      let P := sourceCommonWordLaw t b w j
      ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, (k : ℝ) ≤ A * ((j : ℝ) + 1) ^ 2 →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → (C * ((J : ℝ) + 1)) * s ≤ 1 / 4 →
        Integrable (fun Y : Fin k → WordMark ↦ Real.exp (s * ∑ i, (N (Y i) : ℝ)))
          (Measure.pi (fun _ : Fin k ↦ P)) ∧
        Real.log (∫ Y : Fin k → WordMark, Real.exp (s * ∑ i, (N (Y i) : ℝ))
          ∂Measure.pi (fun _ : Fin k ↦ P)) ≤
          2 * k * s + (6 + 24 * C) * k * ((J : ℝ) + 1) * s ^ 2 + A * D / t ^ 5 := by
  obtain ⟨C, hC, Js, hsingle⟩ := source_early_single_mark_log_moment hLast hrec hinput
  obtain ⟨D, hD, Je, herr⟩ := source_early_weighted_mean_error hLast hinput
  obtain ⟨Jp, hprob⟩ := source_early_common_root_mean hLast
  refine ⟨C, D, hC, hD, max Js (max Je Jp), ?_⟩
  intro J₀ hJ₀
  obtain ⟨as, has, hs⟩ := hsingle J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨ae, hae, he⟩ := herr J₀ ((le_max_left _ _).trans ((le_max_right _ _).trans hJ₀))
  obtain ⟨ap, hap, hp⟩ := hprob J₀ ((le_max_right _ _).trans ((le_max_right _ _).trans hJ₀))
  refine ⟨max as (max ae ap), has.trans (le_max_left _ _), ?_⟩
  filter_upwards [hs, he, hp, eventually_ge_atTop (max 1 D)] with t hs he hp ht
  intro b w hbw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let N := fun Y ↦ sourceCommonWordRootCount t b ν Y + sourceCommonWordRootCount t w ν Y
  let P := sourceCommonWordLaw t b w j
  let μ : ℝ := ∫ Y, (N Y : ℝ) ∂P
  have hs := hs b w hbw ((le_max_left _ _).trans ha) hrange
  have he := he b w hbw ((le_max_left _ _).trans ((le_max_right _ _).trans ha)) hrange
  have hp := (hp b w hbw
    ((le_max_right _ _).trans ((le_max_right _ _).trans ha)) hrange).1
  letI : IsProbabilityMeasure P := hp
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have hDt : D ≤ t := (le_max_right _ _).trans ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have ht5 : t ≤ t ^ 5 := by
    have hh := one_le_pow₀ ht1 (n := 4)
    nlinarith [mul_le_mul_of_nonneg_left hh ht0.le]
  have hfrac : D / t ^ 5 ≤ 1 := (div_le_one (pow_pos ht0 5)).2 (hDt.trans ht5)
  have hweight : 1 ≤ ((j : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) j, sq_nonneg (j : ℝ)]
  have habs : |μ - 2| ≤ D / t ^ 5 :=
    (le_mul_of_one_le_left (abs_nonneg _) hweight).trans he
  have hμ : 0 ≤ μ := integral_nonneg (fun _ ↦ Nat.cast_nonneg _)
  have hμ3 : μ ≤ 3 := by linarith [le_abs_self (μ - 2), habs.trans hfrac]
  intro A hA k hk s hs0 hsSmall hsQ
  have hsM := hs s hs0 hsSmall hsQ
  constructor
  · simp_rw [Finset.mul_sum, Real.exp_sum]
    exact Integrable.fintype_prod (fun _ : Fin k ↦ hsM.1)
  · have hproduct :
        Real.log (∫ Y : Fin k → WordMark, Real.exp (s * ∑ i, (N (Y i) : ℝ))
          ∂Measure.pi (fun _ : Fin k ↦ P)) =
        (k : ℝ) * Real.log (∫ Y, Real.exp (s * (N Y : ℝ)) ∂P) :=
      cgf_iid_sum P (fun Y ↦ (N Y : ℝ)) k s
    rw [hproduct]
    have hke : (k : ℝ) * |μ - 2| ≤ A * D / t ^ 5 := by
      calc
        _ ≤ (A * ((j : ℝ) + 1) ^ 2) * |μ - 2| :=
          mul_le_mul_of_nonneg_right hk (abs_nonneg _)
        _ = A * (((j : ℝ) + 1) ^ 2 * |μ - 2|) := by ring
        _ ≤ A * (D / t ^ 5) := mul_le_mul_of_nonneg_left he hA
        _ = _ := by ring
    exact root_log_mean_replacement μ C ((J : ℝ) + 1) k s (A * D / t ^ 5) _
      hμ hμ3 hC (by linarith [Nat.cast_nonneg (α := ℝ) J]) (Nat.cast_nonneg _) hs0 (by linarith)
      hke (mul_le_mul_of_nonneg_left hsM.2.2 (Nat.cast_nonneg _))

end SRWTightness
