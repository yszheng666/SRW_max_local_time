import SRWTightness.SourceActualNestedRecords

open MeasureTheory
namespace SRWTightness

/-- Every starting level extracts the same ordered terminal words, not just the same terminal count. -/
theorem source_terminal_record_consistency (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ k : ℕ) (b : Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (hk : k < ℓ) (D : Finset Site) (x : Site)
    (hD : sourceExitDomain m r ℓ b 0 ⊆ D) :
    sourceTerminalRecords m r ℓ k b D x =ᵐ[pathLaw] sourceTerminalRecords m r ℓ 0 b D x := by
  have hDk := (sourceExitDomain_antitone m r ℓ b hr hm (Nat.zero_le k)).trans hD
  have h₀ := source_forward_nested_records hF m r ℓ b hr hm 0 (ℓ - 1) (Nat.zero_le _)
    (by omega) D x hD
  have hk' := source_forward_nested_records hF m r ℓ b hr hm k (ℓ - 1) (by omega)
    (by omega) D x hDk
  have hn₀ : ℓ - 1 - 0 + 1 = ℓ - 0 := by omega
  have hnk : ℓ - 1 - k + 1 = ℓ - k := by omega
  change actualTerminalWordRecords (sourceExcursionLevels m r ℓ b k (ℓ - k)) D x =ᵐ[pathLaw]
    actualTerminalWordRecords (sourceExcursionLevels m r ℓ b 0 (ℓ - 0)) D x
  simpa only [hn₀, hnk] using hk'.trans h₀.symm

end SRWTightness
