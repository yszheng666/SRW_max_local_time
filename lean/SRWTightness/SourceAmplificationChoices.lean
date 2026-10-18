import SRWTightness.AmplificationScaleChoice
import Mathlib.Algebra.Order.Floor.Semifield

open Filter

namespace SRWTightness

/-- The natural amplification parameters equal both literal integer floors in source (10.3). -/
theorem source_amplification_floors (s : ℝ) :
    (amplificationScale s : ℤ) = ⌊Real.exp (s / (2 * (2 / Real.sqrt Real.pi)))⌋ ∧
      (amplificationScale s / 2 : ℕ) = ⌊(amplificationScale s : ℝ) / 2⌋₊ ∧
      ((amplificationScale s / 2 : ℕ) : ℤ) = ⌊(amplificationScale s : ℝ) / 2⌋ := by
  have hp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have he : s / (2 * (2 / Real.sqrt Real.pi)) = s * Real.sqrt Real.pi / 4 := by
    field_simp <;> ring
  have hJ : ⌊(amplificationScale s : ℝ) / 2⌋₊ = amplificationScale s / 2 :=
    Nat.floor_div_eq_div (K := ℝ) (amplificationScale s) 2
  refine ⟨?_, ?_, ?_⟩
  · rw [he]
    exact Int.natCast_floor_eq_floor (Real.exp_pos _).le
  · exact hJ.symm
  · rw [← hJ]
    exact Int.natCast_floor_eq_floor (show 0 ≤ (amplificationScale s : ℝ) / 2 by positivity)

/-- The exact source floor choices eventually give admissible disks and the centering shift. -/
theorem source_amplification_choices (s : ℝ) (hs : 0 ≤ s) :
    ∀ᶠ R : ℝ in atTop, 1 < R / amplificationScale s ∧
      ((amplificationScale s / 2 : ℕ) : ℝ) * (R / amplificationScale s + 1) < R ∧
      diskCenter R - diskCenter (R / amplificationScale s) ≤ s / 2 := by
  have hQ : (0 : ℝ) < amplificationScale s := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (amplificationScale_pos s hs)
  filter_upwards [eventually_gt_atTop (amplificationScale s : ℝ)] with R hR
  exact ⟨(lt_div_iff₀ hQ).mpr (by simpa using hR), amplificationScale_geometry s R hs hR,
    diskCenter_amplification_shift s R hs hR⟩

end SRWTightness
