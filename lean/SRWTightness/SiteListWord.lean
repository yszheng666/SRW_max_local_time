import SRWTightness.PathWordSlice
import SRWTightness.DirectionReversal
import Mathlib.Data.List.OfFn

namespace SRWTightness

/-- Recover a nearest-neighbor direction from its endpoints, with a default off valid edges. -/
noncomputable def directionBetween (x y : Site) : Direction :=
  if h : ∃ d : Direction, x + step d = y then h.choose else 0

/-- Recovering a direction from an actual step preserves that direction exactly. -/
theorem direction_between_step (x : Site) (d : Direction) :
    directionBetween x (x + step d) = d := by
  classical
  have h : ∃ e : Direction, x + step e = x + step d := ⟨d, rfl⟩
  unfold directionBetween
  rw [dif_pos h]
  exact step_injective (add_left_cancel h.choose_spec)

/-- Reconstruct a direction word from consecutive recorded sites. -/
noncomputable def siteListWord (zs : List Site) : PathWord :=
  ⟨zs.length - 1, fun k ↦ directionBetween (zs[k.val]'(by omega))
    (zs[k.val + 1]'(by omega))⟩

/-- Consecutive sites of an actual finite segment recover its full direction word. -/
theorem site_list_word_actual_segment (x : Site) (ω : Sample) (a n : ℕ) :
    siteListWord (List.ofFn (fun i : Fin (n + 1) ↦ x + position ω (a + i.val))) =
      (⟨n, fun k ↦ ω (a + k.val)⟩ : PathWord) := by
  unfold siteListWord
  congr 1
  · simp
  · apply (Fin.heq_fun_iff (by simp)).mpr
    intro k
    simp only [List.getElem_ofFn]
    have hp : x + position ω (a + (k.val + 1)) =
        (x + position ω (a + k.val)) + step (ω (a + k.val)) := by
      rw [← Nat.add_assoc]
      change x + (position ω (a + k.val) + step (ω (a + k.val))) = _
      exact (add_assoc _ _ _).symm
    rw [hp, direction_between_step]

end SRWTightness
