import SRWTightness.SourcePairShellCount

open Filter
open scoped Topology

namespace SRWTightness

/-- The manuscript's candidate annulus has at most C R² aᵢ² ordered pairs in each shell. -/
theorem source_pair_shell_annulus_card (hDisk : LatticeDiskCountInput)
    (hAnnulus : LatticeAnnulusCountInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop, ∀ (A : ℝ) (i : ℕ),
      1 ≤ A * diskEnergyGapRatio ^ i →
      ((sourcePairShell (sourceCandidateAnnulus R) A i).card : ℝ) ≤
        C * R ^ 2 * (A * diskEnergyGapRatio ^ i) ^ 2 := by
  obtain ⟨C, hC, hcount⟩ := source_pair_shell_card hDisk
  obtain ⟨c, B, hc, hB, hband⟩ := hAnnulus
  refine ⟨C * B, mul_pos hC hB, ?_⟩
  filter_upwards [hband] with R hR
  intro A i ha
  calc
    _ ≤ C * (sourceCandidateAnnulus R).card * (A * diskEnergyGapRatio ^ i) ^ 2 :=
      hcount _ A i ha
    _ ≤ C * (B * R ^ 2) * (A * diskEnergyGapRatio ^ i) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR.2 hC.le) (sq_nonneg _)
    _ = _ := by ring

end SRWTightness
