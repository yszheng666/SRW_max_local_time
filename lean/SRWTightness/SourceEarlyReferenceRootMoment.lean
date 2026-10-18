import SRWTightness.SourceEarlySquareRootListIntegral
import SRWTightness.MarkedGWEarlyEndpoint
import SRWTightness.SourceEarlyBarrierMinimum
import SRWTightness.SourceOrderedPrefixEvent
import SRWTightness.SourceCommonReferenceHighEvent

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- The original early prefix and both short-root labels under the common reference tree law. -/
theorem source_early_reference_root_moment [MeasurableSpace (List WordMark)]
    [MeasurableSingletonClass (List WordMark)] (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hJoint : MarkedGWJointInput WordMark) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ z w : Site, z ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
      let P := sourceCommonWordLaw t z w j
      ∀ [MeasurableSpace (FiniteExcursionRecord WordMark j)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)],
      (∫⁻ r in sourceOrderedPrefixRecords t j, ENNReal.ofReal (Real.exp
        (2 * Real.sqrt (2 * ((((finiteRecordLeaves j r).map
          (sourceCommonWordRootCount t z ν)).sum : ℕ) : ℝ)) +
         2 * Real.sqrt (2 * ((((finiteRecordLeaves j r).map
          (sourceCommonWordRootCount t w ν)).sum : ℕ) : ℝ))))
        ∂finiteRecordReferenceMeasure P j) ≤
        ENNReal.ofReal (36 * (j : ℝ) ^ 2 * Real.exp
          (4 * b - b ^ 2 / (2 * ((j : ℝ) + 1)) +
            (C * ((J : ℝ) + 1) + D / t ^ 5))) := by
  obtain ⟨C, D, hC, hD, Jm, hm⟩ :=
    source_early_square_root_list_lintegral hLast hrec hinput (2 / 5) (by norm_num)
  obtain ⟨Jp, hp⟩ := source_early_common_root_mean hLast
  refine ⟨C, D, hC, hD, max Jm Jp, ?_⟩
  intro J₀ hJ₀
  obtain ⟨am, ham, hm⟩ := hm J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨ap, hap, hp⟩ := hp J₀ ((le_max_right _ _).trans hJ₀)
  obtain ⟨ab, hab, hb⟩ := source_early_barrier_tilt J₀ 0 (2 / 5) (by norm_num) (by norm_num)
  obtain ⟨al, hl⟩ := source_early_distance_levels J₀
  refine ⟨max am (max ap (max ab al)), ham.trans (le_max_left _ _), ?_⟩
  filter_upwards [hm, hp, hb, hl, source_early_endpoint_formula] with t hm hp hb hl he
  intro z w hzw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ (2 / 5 : ℝ)
  have ham' : am ≤ a := (le_max_left _ _).trans ha
  have hap' : ap ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have hab' : ab ≤ a := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ha))
  have hal' : al ≤ a := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ha))
  have hprob := (hp z w hzw hap' hrange).1
  have hmoment := hm z w hzw ham' hrange
  have hbar := hb a hab'
  have hlevels := hl a hal' hrange
  have hj : 1 ≤ j := hlevels.1
  have hjmax : j ≤ 2 * sourceCoarseLowerLevel t := by
    have hh := hlevels.2.2
    dsimp only [j, ν] at *
    omega
  have hbpos : 0 < b := by have hh := hbar.1; change 4 ≤ b at hh; linarith
  intro inst₁ inst₂
  exact markedGWJoint_early_endpoint_bound hJoint hGW _ hprob j hj b
    (C * ((J : ℝ) + 1) + D / t ^ 5) hbpos hbar.2.1
    (sourceCommonPrefixGWBarrier t j)
    (fun g hg ↦ by simpa only [he j hjmax] using hg j hj (le_refl j))
    (fun rs ↦ ENNReal.ofReal (Real.exp
      (2 * Real.sqrt (2 * (((rs.map (sourceCommonWordRootCount t z ν)).sum : ℕ) : ℝ)) +
       2 * Real.sqrt (2 * (((rs.map (sourceCommonWordRootCount t w ν)).sum : ℕ) : ℝ)))))
    hmoment

end SRWTightness
