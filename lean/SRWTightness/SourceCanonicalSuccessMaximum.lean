import SRWTightness.SourceSuccessMaximum
import SRWTightness.SourceCenteredSuccessCount
import SRWTightness.SourcePairCenterChoice
import SRWTightness.DiskObservable

open MeasureTheory
namespace SRWTightness

/-- A positive canonical count forces the original disk-maximum threshold pathwise. -/
theorem source_canonical_success_sqrt_max (t A γ : ℝ) (I : ℕ) (hA : 0 < A)
    (ht : sourceScaleThreshold 4 ≤ t)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I)
    (p : Sample × (Site → ℕ → GaussianCoefficientSpace))
    (hp : 0 < sourceCenteredSuccessCount t A γ I p) :
    diskCenter (Real.exp t) ≤ Real.sqrt (diskMax (Real.exp t) p.1) := by
  obtain ⟨z, hz⟩ := source_pair_center_choice A I hA
  have he := source_success_count_eq_centered t A γ I (fun _ ↦ I)
    (fun b ↦ z b) hI (fun _ ↦ hI) (fun b ↦ hz b)
  apply source_success_count_sqrt_max (Real.exp t) A γ (Real.exp_pos _)
    (by simpa only [Real.log_exp] using ht) (fun _ ↦ I) (fun b ↦ z b) p
  simpa only [he] using hp

/-- The disk-maximum threshold is measurable on the original path space. -/
theorem measurableSet_disk_seed_event (R : ℝ) :
    MeasurableSet {ω | diskCenter R ≤ Real.sqrt (diskMax R ω)} := by
  exact measurableSet_le measurable_const
    (Real.continuous_sqrt.measurable.comp
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_diskMax R)))

/-- Removing all auxiliary bridges preserves the original disk-maximum probability. -/
theorem source_enlarged_disk_seed_probability (R : ℝ) :
    sourceEnlargedLaw.real {p | diskCenter R ≤ Real.sqrt (diskMax R p.1)} =
      pathLaw.real {ω | diskCenter R ≤ Real.sqrt (diskMax R ω)} := by
  have hm : MeasurePreserving Prod.fst sourceEnlargedLaw pathLaw := measurePreserving_fst
  exact hm.measureReal_preimage (measurableSet_disk_seed_event R).nullMeasurableSet

/-- The positive canonical-count probability is bounded by the original path seed event. -/
theorem source_canonical_positive_probability_le_seed (t A γ : ℝ) (I : ℕ) (hA : 0 < A)
    (ht : sourceScaleThreshold 4 ≤ t)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) :
    sourceEnlargedLaw.real {p | 0 < sourceCenteredSuccessCount t A γ I p} ≤
      pathLaw.real {ω | diskCenter (Real.exp t) ≤ Real.sqrt (diskMax (Real.exp t) ω)} := by
  rw [← source_enlarged_disk_seed_probability]
  exact measureReal_mono (fun p hp ↦ source_canonical_success_sqrt_max t A γ I hA ht hI p hp)

end SRWTightness
