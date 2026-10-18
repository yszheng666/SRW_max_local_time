import SRWTightness.LowerTailFromSeed
import SRWTightness.DiskTightnessFromTails
import SRWTightness.TimeTightnessTransfer
import SRWTightness.TimeTailsFromDiskTails

namespace SRWTightness

/-- Both source tail bounds follow from the two unproved spatial propositions. -/
theorem diskTails_of_upper_and_seed (hu : DiskUpperTailClaim) (hs : DiskSeedClaim) : DiskTailClaim := by
  obtain ⟨C, s₁, hC, hs₁, hupper⟩ := hu
  obtain ⟨c, s₂, hc, hs₂, hlower⟩ := disk_lower_tail_of_seed hs
  refine ⟨C, c, max s₁ s₂, hC, hc, lt_max_of_lt_left hs₁, ?_⟩
  intro s hss
  exact ⟨hupper s ((le_max_left _ _).trans hss), hlower s ((le_max_right _ _).trans hss)⟩

/-- This is an implication, not a proof of either spatial input. -/
theorem diskTightness_of_upper_and_seed (hu : DiskUpperTailClaim) (hs : DiskSeedClaim) : DiskTightnessClaim :=
  diskTightness_of_diskTails (diskTails_of_upper_and_seed hu hs)

theorem timeTightness_of_upper_and_seed (hu : DiskUpperTailClaim) (hs : DiskSeedClaim) : TimeTightnessClaim :=
  timeTightness_of_diskTightness (diskTightness_of_upper_and_seed hu hs)

theorem inclusiveTimeTightness_of_upper_and_seed (hu : DiskUpperTailClaim) (hs : DiskSeedClaim) :
    InclusiveTimeTightnessClaim :=
  inclusiveTimeTightness_of_diskTightness (diskTightness_of_upper_and_seed hu hs)

theorem timeTails_of_upper_and_seed (hu : DiskUpperTailClaim) (hs : DiskSeedClaim) : TimeTailClaim :=
  timeTails_of_diskTails (diskTails_of_upper_and_seed hu hs)

/-- All requested conclusions reduce to the two explicit spatial propositions. -/
theorem mainClaims_of_spatial_inputs (hu : DiskUpperTailClaim) (hs : DiskSeedClaim) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧ InclusiveTimeTightnessClaim :=
  ⟨diskTightness_of_upper_and_seed hu hs, diskTails_of_upper_and_seed hu hs,
    timeTightness_of_upper_and_seed hu hs, timeTails_of_upper_and_seed hu hs,
    inclusiveTimeTightness_of_upper_and_seed hu hs⟩

end SRWTightness
