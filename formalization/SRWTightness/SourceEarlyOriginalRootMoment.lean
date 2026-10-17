import SRWTightness.SourceEarlyReferenceRootMoment
import SRWTightness.SourceEarlyOriginalRootWeighted

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- Both original root counts have the explicit early-prefix exponential moment bound. -/
theorem source_early_original_root_moment [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∃ C D E : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ 0 ≤ E ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ z w : Site, z ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
      (∀ x ∈ ({z, w} : Finset Site), Real.exp t / 4 ≤ Real.sqrt (normSq x) ∧
        Real.sqrt (normSq x) ≤ Real.exp t / 3) →
      ∀ [MeasurableSpace (FiniteExcursionRecord WordMark j)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))],
      (∫⁻ ω in sourceEarlyPrefixEvent t z j, ENNReal.ofReal (Real.exp
        (2 * Real.sqrt (2 * (sourceActualCount t z ν ω : ℝ)) +
         2 * Real.sqrt (2 * (sourceActualCount t w ν ω : ℝ)))) ∂pathLaw) ≤
        ENNReal.ofReal (36 * (j : ℝ) ^ 2 * Real.exp
          (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) +
            (C * ((J : ℝ) + 1) + D / t ^ 5) + E)) := by
  obtain ⟨C, D, hC, hD, Jm, hm⟩ :=
    source_early_reference_root_moment hLast hrec hinput hGW hJoint
  obtain ⟨E, hE, Jw, hw⟩ := source_early_original_root_weighted hinput hFlat
  refine ⟨C, D, E, hC, hD, hE, max Jm Jw, ?_⟩
  intro J₀ hJ₀
  obtain ⟨am, ham, hm⟩ := hm J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨aw, haw, hw⟩ := hw J₀ ((le_max_right _ _).trans hJ₀)
  refine ⟨am + aw, by omega, ?_⟩
  filter_upwards [hm, hw] with t hm hw
  intro z w hzw ha hrange
  dsimp only
  intro hann inst₁ inst₂ inst₃ inst₄
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
  let H : ℕ × ℕ → ℝ≥0∞ := fun v ↦ ENNReal.ofReal (Real.exp
    (2 * Real.sqrt (2 * (v.1 : ℝ)) + 2 * Real.sqrt (2 * (v.2 : ℝ))))
  have hweighted := hw z w hzw (show aw ≤ _ by omega) hrange hann
    (markedGWJoint_population hJoint) H
  have hmoment := hm z w hzw (show am ≤ _ by omega) hrange
  simp only [sourceCommonWordLaw, sourceCommonPairDomain_eq,
    sourceCommonPairIntensity] at hmoment
  have hbound := hweighted.trans (mul_le_mul_left' hmoment (ENNReal.ofReal (Real.exp E)))
  refine hbound.trans_eq ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos E).le]
  congr 1
  simp only [Real.exp_add]
  ring

end SRWTightness
