import SRWTightness.FiniteOrderedBinomialSum
import Mathlib.Data.Finset.Card

namespace SRWTightness

/-- The ordered binomial identity keeps list multiplicities when completion times are distinct. -/
theorem list_sum_choose_later_length (ts : List ℕ) (ht : ts.Nodup) (p : ℕ) :
    (ts.map (fun n ↦ ((ts.filter (fun k ↦ n < k)).length).choose p)).sum =
      ts.length.choose (p + 1) := by
  classical
  have hcard (n : ℕ) : (ts.toFinset.filter (fun k ↦ n < k)).card =
      (ts.filter (fun k ↦ n < k)).length := by
    have he : (ts.filter (fun k ↦ n < k)).toFinset =
        ts.toFinset.filter (fun k ↦ n < k) := by ext k; simp
    rw [← he]
    exact List.toFinset_card_of_nodup (ht.filter _)
  have h := finset_sum_choose_greater_card ts.toFinset p
  simp only [hcard, List.toFinset_card_of_nodup ht] at h
  rw [List.sum_toFinset _ ht] at h
  exact h

end SRWTightness
