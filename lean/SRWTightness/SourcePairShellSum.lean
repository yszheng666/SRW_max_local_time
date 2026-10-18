import SRWTightness.SourcePairShellCover
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace SRWTightness

/-- Summing nonnegative pair weights over retained shells bounds the complete late-pair sum. -/
theorem source_late_pair_sum_le_shells (Z : Finset Site) (A : ℝ) (I : ℕ) (hA : 0 < A)
    (P : Site × Site → ℝ) (hP : ∀ p, 0 ≤ P p) :
    (∑ p ∈ sourceLatePairs Z A I, P p) ≤
      ∑ i ∈ Finset.range (I + 1), ∑ p ∈ sourcePairShell Z A i, P p := by
  classical
  calc
    _ ≤ ∑ p ∈ sourceLatePairs Z A I, ∑ i ∈ Finset.range (I + 1),
        if p ∈ sourcePairShell Z A i then P p else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨i, hi, hmem, _⟩ := source_late_pair_shell_cover Z A I hA p hp
      have hh := Finset.single_le_sum
        (s := Finset.range (I + 1))
        (f := fun j ↦ if p ∈ sourcePairShell Z A j then P p else 0)
        (fun j _ ↦ by split; exact hP p; exact le_rfl)
        (show i ∈ Finset.range (I + 1) by simpa using Nat.lt_succ_of_le hi)
      simpa only [if_pos hmem] using hh
    _ = ∑ i ∈ Finset.range (I + 1), ∑ p ∈ sourceLatePairs Z A I,
        if p ∈ sourcePairShell Z A i then P p else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (Finset.mem_filter.mp hp).2
      · intro p hp hnot
        exact hP p

end SRWTightness
