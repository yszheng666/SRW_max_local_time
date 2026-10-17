import SRWTightness.SourceCommonLevelContribution
import SRWTightness.SourceCommonDentLower
import SRWTightness.SourceCommonLevels
import SRWTightness.CommonLevelDecay

open MeasureTheory Filter
open scoped BigOperators Topology
namespace SRWTightness

/-- All later common coarse levels have a uniformly vanishing total pair contribution. -/
theorem source_common_total_contribution (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) (hpot : PotentialKernelAsymptoticInput)
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (hJoint : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWJointInput (Mark K)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (A γ : ℝ) (I : ℕ)
      (z : ∀ b : Site, translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I))),
      (∀ b, (z b : Site) = b) →
      (∑ j ∈ sourceCommonLevels t,
        ∑ p ∈ sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j,
          sourcePairSuccessWeight t A γ I z p) ≤ C / t ^ 1973 := by
  classical
  obtain ⟨C, hC, hu⟩ := source_common_level_contribution hDisk hAnnulus hpot hGW hOcc hRes hJoint
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hu, source_common_dent_lower, source_common_levels_card,
    eventually_ge_atTop (1 : ℝ)] with t hu hdent hcard ht
  intro A γ I z hz
  let Q := C * t ^ 26 * Real.exp (-2000 * Real.log t)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hlevel (j : ℕ) (hj : j ∈ sourceCommonLevels t) :
      (∑ p ∈ sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j,
        sourcePairSuccessWeight t A γ I z p) ≤ Q := by
    obtain ⟨hjr, hjcut⟩ := Finset.mem_filter.mp hj
    have hjdepth : j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
      have hh := Finset.mem_range.mp hjr
      omega
    have hbound := hu A γ I j z hz hjcut hjdepth
    have hd := hdent j hjcut hjdepth
    have hexp := Real.exp_le_exp.mpr (show
      -2 * (min (j : ℝ) (sourceTotalTime t - j)) ^ (2 / 5 : ℝ) ≤
        -2000 * Real.log t by linarith)
    exact hbound.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum : (∑ j ∈ sourceCommonLevels t,
      ∑ p ∈ sourceCommonPairs (sourceCandidateAnnulus (Real.exp t)) t j,
        sourcePairSuccessWeight t A γ I z p) ≤ ((sourceCommonLevels t).card : ℝ) * Q := by
    calc
      _ ≤ ∑ j ∈ sourceCommonLevels t, Q := Finset.sum_le_sum hlevel
      _ = _ := by simp
  calc
    _ ≤ (t + 1) * Q := hsum.trans (mul_le_mul_of_nonneg_right hcard hQ)
    _ = C * ((t + 1) * t ^ 26 * Real.exp (-2000 * Real.log t)) := by dsimp [Q]; ring
    _ ≤ C * (2 / t ^ 1973) := mul_le_mul_of_nonneg_left (common_level_decay t ht) hC.le
    _ = (2 * C) / t ^ 1973 := by ring

/-- The explicit common-level upper bound tends to zero for every fixed constant. -/
theorem common_total_majorant_tendsto_zero (C : ℝ) :
    Tendsto (fun t : ℝ ↦ C / t ^ 1973) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (1973 : ℕ) ≠ 0))

end SRWTightness
