import SRWTightness.SourceCommonPairParameters

namespace SRWTightness

/-- Stopping at the common inner radius preserves every original coarse radius. -/
theorem sourceRecordRadius_rebase (m : ℝ) (ℓ j k : ℕ) :
    sourceRecordRadius (sourceRecordRadius m ℓ (j + 1)) (j + 1) k =
      sourceRecordRadius m ℓ k := by
  unfold sourceRecordRadius
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Rebased entrance disks coincide with the original source disks. -/
theorem sourceEntranceDomain_rebase (m r : ℝ) (ℓ j k : ℕ) (b : Site) :
    sourceEntranceDomain (sourceRecordRadius m ℓ (j + 1)) r (j + 1) b k =
      sourceEntranceDomain m r ℓ b k := by
  simp only [sourceEntranceDomain, sourceRecordRadius_rebase]

/-- Rebased killing disks coincide with the original source disks. -/
theorem sourceExitDomain_rebase (m r : ℝ) (ℓ j k : ℕ) (b : Site) :
    sourceExitDomain (sourceRecordRadius m ℓ (j + 1)) r (j + 1) b k =
      sourceExitDomain m r ℓ b k := by
  simp only [sourceExitDomain, sourceRecordRadius_rebase]

/-- The full finite excursion-domain list is unchanged by common-radius rebasing. -/
theorem sourceExcursionLevels_rebase (m r : ℝ) (ℓ j k n : ℕ) (b : Site) :
    sourceExcursionLevels (sourceRecordRadius m ℓ (j + 1)) r (j + 1) b k n =
      sourceExcursionLevels m r ℓ b k n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [sourceExcursionLevels, sourceEntranceDomain_rebase, sourceExitDomain_rebase, ih]

/-- The common mark killing disk is the final disk of the rebased source profile. -/
theorem sourceCommonPairDomain_rebase (t : ℝ) (b : Site) (j : ℕ) :
    sourceExitDomain (sourceCommonPairInnerRadius t j) 1 (j + 1) b j =
      sourceCommonPairDomain t b j := by
  exact sourceExitDomain_rebase _ _ _ _ _ _

end SRWTightness
