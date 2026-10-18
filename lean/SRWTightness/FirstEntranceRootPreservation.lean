import SRWTightness.FirstEntranceWordMark
import SRWTightness.KilledRootPrefixRemoval
import SRWTightness.ChildExitBounds

open MeasureTheory
namespace SRWTightness

/-- Every short inner set contained in the observation set has the same roots after first entry. -/
theorem firstEntranceWordMark_root_count (D K L C : Finset Site) (hLK : L ⊆ K)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) :
    wordMarkRootCount L C (killedWordMark D x ω) =
      wordMarkRootCount L C (firstEntranceWordMark D K x ω) := by
  let a := domainSteps (D \ K) x ω
  obtain ⟨hf, ha⟩ := subdomain_exit_bounds D (D \ K) Finset.sdiff_subset x ω hfin
  have hpre (i : ℕ) (hi : i < a) : x + position ω i ∉ L := by
    have hh := (Finset.mem_sdiff.mp
      (position_before_domainSteps_mem (D \ K) x ω hf i hi)).2
    exact fun h ↦ hh (hLK h)
  by_cases hh : domainExitLocation (D \ K) x ω ∈ K
  · rw [firstEntranceWordMark, if_pos hh]
    change (killedChildIntervals D L C x ω).length =
      (killedChildIntervals D L C (domainExitLocation (D \ K) x ω)
        (futureAt (domainExit (D \ K) x) ω)).length
    exact killedChildIntervals_length_remove_prefix D L C x ω hfin a ha hpre
  · have haeq : a = domainSteps D x ω := by
      apply Nat.le_antisymm ha
      by_contra hn
      have halt : a < domainSteps D x ω := by omega
      have hm := position_before_domainSteps_mem D x ω hfin a halt
      have hnK : x + position ω a ∉ K := hh
      exact position_domain_exit_not_mem (D \ K) x ω hf (Finset.mem_sdiff.mpr ⟨hm, hnK⟩)
    have hno (i : ℕ) (hi : i ∈ List.range (domainSteps D x ω + 1)) :
        x + position ω i ∉ L := by
      have hi' := List.mem_range.mp hi
      by_cases hil : i < a
      · exact hpre i hil
      · have hieq : i = a := by omega
        subst i
        exact fun h ↦ hh (hLK h)
    have hempty : killedChildIntervals D L C x ω = [] := by
      rw [killedChildIntervals_eq_scan]
      simpa only [List.append_nil, scanChildIntervals] using
        scanChildIntervals_skip_prefix L C x ω (List.range (domainSteps D x ω + 1)) [] hno
    rw [firstEntranceWordMark, if_neg hh]
    change (killedChildIntervals D L C x ω).length = 0
    rw [hempty]
    rfl

/-- Root preservation holds almost surely under the original SRW law. -/
theorem firstEntranceWordMark_root_count_ae (D K L C : Finset Site) (hLK : L ⊆ K)
    (x : Site) :
    ∀ᵐ ω ∂pathLaw, wordMarkRootCount L C (killedWordMark D x ω) =
      wordMarkRootCount L C (firstEntranceWordMark D K x ω) := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  exact firstEntranceWordMark_root_count D K L C hLK x ω hfin

/-- Both labels are preserved on the same sample, without any independence assertion. -/
theorem firstEntranceWordMark_pair_root_count_ae (D K L₁ C₁ L₂ C₂ : Finset Site)
    (hL₁ : L₁ ⊆ K) (hL₂ : L₂ ⊆ K) (x : Site) :
    ∀ᵐ ω ∂pathLaw,
      (wordMarkRootCount L₁ C₁ (killedWordMark D x ω),
        wordMarkRootCount L₂ C₂ (killedWordMark D x ω)) =
      (wordMarkRootCount L₁ C₁ (firstEntranceWordMark D K x ω),
        wordMarkRootCount L₂ C₂ (firstEntranceWordMark D K x ω)) := by
  filter_upwards [firstEntranceWordMark_root_count_ae D K L₁ C₁ hL₁ x,
    firstEntranceWordMark_root_count_ae D K L₂ C₂ hL₂ x] with ω h₁ h₂
  rw [h₁, h₂]

end SRWTightness
