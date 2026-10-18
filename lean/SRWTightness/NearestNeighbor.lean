import SRWTightness.DirectionReversal
import SRWTightness.CoordinateBounds
import SRWTightness.GreenMatrix
import Mathlib.Tactic.IntervalCases

namespace SRWTightness

 theorem normSq_eq_one_iff_step (z : Site) : normSq z = 1 ↔ ∃ d : Direction, z = step d := by
  constructor
  · intro h
    have hf := abs_fst_le_normSq_bound z (show (0 : ℝ) ≤ 1 by norm_num)
      (show normSq z ≤ 1 ^ 2 by nlinarith)
    have hs := abs_snd_le_normSq_bound z (show (0 : ℝ) ≤ 1 by norm_num)
      (show normSq z ≤ 1 ^ 2 by nlinarith)
    have hfi : |z.1| ≤ (1 : ℤ) := by exact_mod_cast hf
    have hsi : |z.2| ≤ (1 : ℤ) := by exact_mod_cast hs
    obtain ⟨a, b⟩ := z
    obtain ⟨hal, hau⟩ := abs_le.mp hfi
    obtain ⟨hbl, hbu⟩ := abs_le.mp hsi
    dsimp at hal hau hbl hbu
    interval_cases a <;> interval_cases b <;>
      norm_num [normSq] at h <;> first
      | exact ⟨0, rfl⟩
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
  · rintro ⟨d, rfl⟩
    exact normSq_step d

 theorem killedTransition_nearest_neighbor (D : Finset Site) (x y : D) :
    killedTransition D x y = if normSq ((y : Site) - x) = 1 then (1 / 4 : ℝ) else 0 := by
  classical
  by_cases h : normSq ((y : Site) - x) = 1
  · obtain ⟨d, hd⟩ := (normSq_eq_one_iff_step _).mp h
    have he (e : Direction) : (x : Site) + step e = (y : Site) ↔ e = d := by
      constructor
      · intro he
        apply step_injective
        rw [← hd, ← he]
        abel
      · rintro rfl
        rw [← hd]
        abel
    simp only [killedTransition, he, if_pos h]
    simp
  · have he (e : Direction) : (x : Site) + step e ≠ (y : Site) := by
      intro he
      apply h
      apply (normSq_eq_one_iff_step _).mpr
      refine ⟨e, ?_⟩
      rw [← he]
      abel
    simp [killedTransition, he, h]

end SRWTightness
