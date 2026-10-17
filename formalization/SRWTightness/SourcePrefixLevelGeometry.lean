import SRWTightness.SourceExcursionDomains
import SRWTightness.RecordExitSlice

namespace SRWTightness

/-- Every source level in a finite prefix has its exact generation index. -/
theorem sourceExcursionLevels_mem (m r : ℝ) (ℓ : ℕ) (b : Site) (k n : ℕ)
    (L : Finset Site × Finset Site) (hL : L ∈ sourceExcursionLevels m r ℓ b k n) :
    ∃ i, k ≤ i ∧ i < k + n ∧
      L = (sourceEntranceDomain m r ℓ b i, sourceExitDomain m r ℓ b i) := by
  induction n generalizing k with
  | zero => simpa [sourceExcursionLevels] using hL
  | succ n ih =>
    simp only [sourceExcursionLevels, List.mem_cons] at hL
    rcases hL with hL | hL
    · exact ⟨k, le_rfl, by omega, hL⟩
    · obtain ⟨i, hi, hin, he⟩ := ih (k + 1) hL
      exact ⟨i, by omega, by omega, he⟩

/-- The innermost prefix target lies inside every earlier source target. -/
theorem sourceEntranceDomain_subset_earlier (m r : ℝ) (ℓ : ℕ) (b : Site) (i j : ℕ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (hj : j + 1 ≤ ℓ) (hij : i ≤ j) :
    sourceEntranceDomain m r ℓ b j ⊆ sourceEntranceDomain m r ℓ b i := by
  have hH : 0 ≤ sourceRecordBuffer r := by unfold sourceRecordBuffer; linarith
  have hm0 : 0 ≤ m := by linarith
  have hlo := sourceRecordRadius_ge_terminal m hm0 ℓ (j + 1) hj
  have hmono := sourceRecordRadius_antitone m hm0 ℓ (Nat.add_le_add_right hij 1)
  unfold sourceEntranceDomain
  exact Finset.image_subset_image (diskFinset_mono _ _ (by linarith) (by linarith))

/-- Containment in the final prefix target supplies every domain premise for count invariance. -/
theorem source_prefix_level_geometry (m r : ℝ) (ℓ : ℕ) (b : Site) (j : ℕ)
    (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m) (hj : j + 1 ≤ ℓ)
    (C : Finset Site) (hC : C ⊆ sourceEntranceDomain m r ℓ b j)
    (hB : domainExitBoundary C ⊆ (sourceEntranceDomain m r ℓ b j : Set Site))
    (i : ℕ) (hi : i ≤ j) :
    ∀ L ∈ sourceExcursionLevels m r ℓ b 0 (i + 1),
      L.1 ⊆ L.2 ∧ C ⊆ L.1 ∧ domainExitBoundary C ⊆ (L.1 : Set Site) := by
  intro L hL
  obtain ⟨q, _, hq, rfl⟩ := sourceExcursionLevels_mem m r ℓ b 0 (i + 1) L hL
  have hqj : q ≤ j := by omega
  have hnest := sourceEntranceDomain_subset_earlier m r ℓ b q j hr hm hj hqj
  exact ⟨sourceEntranceDomain_subset_exit m r ℓ b q hr hm (by omega),
    hC.trans hnest, fun y hy ↦ hnest (hB hy)⟩

end SRWTightness
