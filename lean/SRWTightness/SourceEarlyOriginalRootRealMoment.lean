import SRWTightness.SourceEarlyOriginalRootMoment
import SRWTightness.SourceCountMeasurable

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

set_option maxHeartbeats 400000

/-- The real original-prefix moment with the comparison and vanishing errors absorbed uniformly. -/
theorem source_early_original_root_real_moment [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
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
      (∫ ω, (sourceEarlyPrefixEvent t z j).indicator (fun u ↦ Real.exp
        (2 * Real.sqrt (2 * (sourceActualCount t z ν u : ℝ)) +
         2 * Real.sqrt (2 * (sourceActualCount t w ν u : ℝ)))) ω ∂pathLaw) ≤
        36 * (j : ℝ) ^ 2 * Real.exp
          (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) + C * ((J : ℝ) + 1)) := by
  obtain ⟨C, D, E, hC, hD, hE, Jmin, hm⟩ :=
    source_early_original_root_moment hLast hrec hinput hGW hJoint hFlat
  refine ⟨C + D + E, by positivity, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hm⟩ := hm J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hm, eventually_ge_atTop (1 : ℝ)] with t hm ht
  intro z w hzw ha hrange
  dsimp only
  intro hann inst₁ inst₂ inst₃ inst₄
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
  let f : Sample → ℝ := fun u ↦ Real.exp
    (2 * Real.sqrt (2 * (sourceActualCount t z ν u : ℝ)) +
     2 * Real.sqrt (2 * (sourceActualCount t w ν u : ℝ)))
  have hz : Measurable (fun u ↦ (sourceActualCount t z ν u : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_sourceActualCount t z ν)
  have hw : Measurable (fun u ↦ (sourceActualCount t w ν u : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_sourceActualCount t w ν)
  have hf : Measurable f :=
    (((hz.const_mul 2).sqrt.const_mul 2).add ((hw.const_mul 2).sqrt.const_mul 2)).exp
  let B := 36 * (j : ℝ) ^ 2 * Real.exp
    (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) + (C * ((J : ℝ) + 1) + D / t ^ 5) + E)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hb := hm z w hzw ha hrange hann
  change (∫⁻ u, ENNReal.ofReal (f u)
    ∂pathLaw.restrict (sourceEarlyPrefixEvent t z j)) ≤ ENNReal.ofReal B at hb
  have hnon : 0 ≤ᵐ[pathLaw.restrict (sourceEarlyPrefixEvent t z j)] f :=
    Filter.Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le)
  have hi : Integrable f (pathLaw.restrict (sourceEarlyPrefixEvent t z j)) :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hnon).mp
      (ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top))
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnon] at hb
  have hb' := (ENNReal.ofReal_le_ofReal_iff hB).mp hb
  rw [integral_indicator (measurableSet_sourceEarlyPrefixEvent t z j)]
  apply hb'.trans
  change B ≤ 36 * (j : ℝ) ^ 2 * Real.exp
    (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) + (C + D + E) * ((J : ℝ) + 1))
  dsimp only [B]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hpow : (1 : ℝ) ≤ t ^ 5 := one_le_pow₀ ht
  have hd : D / t ^ 5 ≤ D := div_le_self hD hpow
  have hj : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  nlinarith only [hd, mul_nonneg hD hj, mul_nonneg hE hj]

end SRWTightness
