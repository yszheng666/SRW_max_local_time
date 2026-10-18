import SRWTightness.PairWindows
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

/-- Every deficit below the endpoint cap belongs to a window, including integer boundaries. -/
theorem pairDeficitWindow_cover (top s : ℝ) (hs : s ≤ top) :
    ∃ l : ℕ, s ∈ pairDeficitWindow top l := by
  by_cases hnear : top - s ≤ 1
  · refine ⟨0, ?_⟩
    simp only [pairDeficitWindow, if_pos rfl, Set.mem_Icc]
    exact ⟨by linarith, hs⟩
  · have hr : 1 < top - s := lt_of_not_ge hnear
    let N := Nat.ceil (top - s)
    have hN : 1 < N := (Nat.lt_ceil).mpr (by simpa using hr)
    have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    refine ⟨N - 1, ?_⟩
    simp only [pairDeficitWindow, if_neg (by omega : N - 1 ≠ 0), Set.mem_Ico]
    rw [hc]
    have hlo := Nat.le_ceil (top - s)
    have hhi := Nat.ceil_lt_add_one (by linarith : 0 ≤ top - s)
    change top - s ≤ (N : ℝ) at hlo
    change (N : ℝ) < top - s + 1 at hhi
    constructor <;> linarith

/-- The site excesses and last-average deficit are covered by the exact three-index windows. -/
theorem pairWindow_cover {N : ℕ} (last : Fin N) (At top : ℝ)
    (x : PairObservationIndex N → ℝ)
    (hz : At ≤ x (.inr false)) (hy : At ≤ x (.inr true))
    (hs : x (.inl last) ≤ top) :
    ∃ n m l : ℕ, x ∈ pairWindow last At top n m l := by
  obtain ⟨l, hl⟩ := pairDeficitWindow_cover top (x (.inl last)) hs
  refine ⟨Nat.floor (x (.inr false) - At), Nat.floor (x (.inr true) - At), l, ?_⟩
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, hl⟩
  · linarith [Nat.floor_le (by linarith : 0 ≤ x (.inr false) - At)]
  · linarith [Nat.lt_floor_add_one (x (.inr false) - At)]
  · linarith [Nat.floor_le (by linarith : 0 ≤ x (.inr true) - At)]
  · linarith [Nat.lt_floor_add_one (x (.inr true) - At)]

end SRWTightness
