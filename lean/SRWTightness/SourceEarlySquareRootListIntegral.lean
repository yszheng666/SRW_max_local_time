import SRWTightness.SourceEarlySquareRootMoment
import SRWTightness.IndependentForestRootIntegral

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- The source conditional square-root moment as a nonnegative integral over mark lists. -/
theorem source_early_square_root_list_lintegral [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput)
    (γ : ℝ) (hγ : γ ≤ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ z w : Site, z ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ γ
      let P := sourceCommonWordLaw t z w j
      ∀ k : ℕ, Real.sqrt (2 * (k : ℝ)) ≤ b →
      (∫⁻ rs, ENNReal.ofReal (Real.exp
        (2 * Real.sqrt (2 * (((rs.map (sourceCommonWordRootCount t z ν)).sum : ℕ) : ℝ)) +
         2 * Real.sqrt (2 * (((rs.map (sourceCommonWordRootCount t w ν)).sum : ℕ) : ℝ))))
        ∂independentForestLaw P k) ≤
        ENNReal.ofReal (Real.exp
          (2 * b + 4 * (k : ℝ) / b + (C * ((J : ℝ) + 1) + D / t ^ 5))) := by
  obtain ⟨C, D, hC, hD, Jmin, hm⟩ :=
    source_early_square_root_moment hLast hrec hinput γ hγ
  refine ⟨C, D, hC, hD, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hm⟩ := hm J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hm] with t hm
  intro z w hzw ha hrange
  dsimp only
  intro k hk
  have hh := hm z w hzw ha hrange k hk
  dsimp only at hh
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
  let J := sourceEarlyDistanceGap a J₀
  let ν := a + J + 5
  rw [independentForest_joint_root_lintegral _ k
    (sourceCommonWordRootCount t z ν) (sourceCommonWordRootCount t w ν)
    (fun v ↦ ENNReal.ofReal (Real.exp
      (2 * Real.sqrt (2 * (v.1 : ℝ)) + 2 * Real.sqrt (2 * (v.2 : ℝ)))))]
  simp only [Nat.cast_sum]
  rw [← ofReal_integral_eq_lintegral_ofReal hh.1
    (Filter.Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))]
  apply ENNReal.ofReal_le_ofReal
  convert hh.2 using 1 <;> congr 1
  rw [Real.sq_sqrt (by positivity)]
  ring

end SRWTightness
