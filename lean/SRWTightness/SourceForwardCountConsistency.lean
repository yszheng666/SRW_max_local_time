import SRWTightness.SourceActualNestedRecords

open MeasureTheory
namespace SRWTightness

/-- Changing the starting level of a complete nested extraction preserves its final original count. -/
theorem source_forward_count_consistency (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ : ℕ) (b : Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (k i : ℕ) (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (D : Finset Site) (x : Site)
    (hD : sourceExitDomain m r ℓ b 0 ⊆ D) :
    sourceForwardRecordCount m r ℓ k i b D x =ᵐ[pathLaw]
      sourceForwardRecordCount m r ℓ 0 i b D x := by
  have hDk : sourceExitDomain m r ℓ b k ⊆ D :=
    (sourceExitDomain_antitone m r ℓ b hr hm (Nat.zero_le k)).trans hD
  filter_upwards [source_forward_nested_records hF m r ℓ b hr hm k i hki hi D x hDk,
    source_forward_nested_records hF m r ℓ b hr hm 0 i (Nat.zero_le _) hi D x hD]
    with ω hk h0
  exact congrArg List.length (hk.trans h0.symm)

end SRWTightness
