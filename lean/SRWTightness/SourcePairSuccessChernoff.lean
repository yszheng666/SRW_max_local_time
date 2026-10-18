import SRWTightness.SourcePairRecordChernoff
import SRWTightness.SourcePairSuccessProbabilityComparison

open MeasureTheory Filter

namespace SRWTightness

/-- The Chernoff branch on the common probability space of the two actual SRW successes. -/
theorem source_pair_success_chernoff
    (hPotential : PotentialKernelAsymptoticInput) (hUpper : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (A : ℝ)
      (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I)
    (z y : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (hz : (z : Site) = b) (hρ : 1 ≤ Real.sqrt (normSq ((y : Site) - b)))
    (hlo : 4 * Real.sqrt (normSq ((y : Site) - b)) ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤
      4 * diskEnergyGapRatio * Real.sqrt (normSq ((y : Site) - b)))
    (γ : ℝ)
    (hlog : sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A)
    (J : ℕ)
    (z' : translateFinset (y : Site) (diskFinset (A * diskEnergyGapRatio ^ J)))
    (hz' : (z' : Site) = (y : Site))
    (hblo : Real.exp t / 4 ≤ Real.sqrt (normSq b))
    (hbhi : Real.sqrt (normSq b) ≤ Real.exp t / 3),
    ∀ [MeasurableSpace (List (Mark (translateFinset b
      (diskFinset (A * diskEnergyGapRatio ^ I)))))]
      [MeasurableSingletonClass (List (Mark (translateFinset b
        (diskFinset (A * diskEnergyGapRatio ^ I)))))],
    MarkedGWJointInput (Mark (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))) →
    let d := sourceLowerTime (sourceLowerRadius t)
    let h := d - sourceObservationTime t A I (I - i + 1)
    let ρ := Real.sqrt (normSq ((y : Site) - b))
    sourceEnlargedLaw.real
      (sourceSiteSuccessEvent t A γ b I z ∩ sourceSiteSuccessEvent t A γ (y : Site) J z') ≤
      C * d * Real.exp (-2 * t - 2 * h - 2 * h ^ γ) := by
  obtain ⟨C, hC, hrecord⟩ := source_pair_record_chernoff hPotential hUpper
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrecord, source_pair_success_probability_le_record] with t hrecord hsuccess
  intro b A hA ht I hI i hi z y hz hρ hlo hhi γ hlog J z' hz' hblo hbhi instM instMS hjoint
  have hs := hsuccess A γ b (y : Site) I J i hA ht hlog hI hi z y z' rfl hz' hblo hbhi
  exact hs.trans (hrecord b A hA ht I hI i hi z y hz hρ hlo hhi
    ((sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)) ^ γ)
    hblo hbhi hjoint)

end SRWTightness
