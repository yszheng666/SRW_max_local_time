import SRWTightness.GeometricDiskFamily
import Mathlib.Algebra.Order.Archimedean.Basic

namespace SRWTightness

theorem exists_scaled_geometric_terminal (A q L : ℝ) (hA : 0 < A) (hq : 1 < q)
    (hAL : A ≤ L) : ∃ I : ℕ, A * q ^ I ≤ L ∧ L < A * q ^ (I + 1) := by
  obtain ⟨I, hl, hu⟩ := exists_nat_pow_near ((one_le_div hA).mpr hAL) hq
  refine ⟨I, ?_, ?_⟩
  · have hh := (le_div_iff₀ hA).mp hl
    simpa only [mul_comm] using hh
  · have hh := (div_lt_iff₀ hA).mp hu
    simpa only [mul_comm] using hh

/-- The largest geometric scale below a cutoff, defined only in the nonempty regime. -/
noncomputable def geometricTerminalIndex (A q L : ℝ) (hA : 0 < A) (hq : 1 < q)
    (hAL : A ≤ L) : ℕ := Classical.choose (exists_scaled_geometric_terminal A q L hA hq hAL)

theorem geometricTerminalIndex_spec (A q L : ℝ) (hA : 0 < A) (hq : 1 < q) (hAL : A ≤ L) :
    A * q ^ geometricTerminalIndex A q L hA hq hAL ≤ L ∧
      L < A * q ^ (geometricTerminalIndex A q L hA hq hAL + 1) :=
  Classical.choose_spec (exists_scaled_geometric_terminal A q L hA hq hAL)

/-- This index is exactly the maximum in the manuscript, rather than an arbitrary scale below cutoff. -/
theorem geometricTerminalIndex_max_iff (A q L : ℝ) (hA : 0 < A) (hq : 1 < q)
    (hAL : A ≤ L) (i : ℕ) :
    A * q ^ i ≤ L ↔ i ≤ geometricTerminalIndex A q L hA hq hAL := by
  obtain ⟨hl, hu⟩ := geometricTerminalIndex_spec A q L hA hq hAL
  constructor
  · intro hi
    by_contra hn
    have he : geometricTerminalIndex A q L hA hq hAL + 1 ≤ i := by omega
    have hh := geometric_radius_mono A q hA.le hq.le he
    exact (not_lt_of_ge (hh.trans hi)) hu
  · intro hi
    exact (geometric_radius_mono A q hA.le hq.le hi).trans hl

theorem geometricTerminalIndex_radius_bounds (A q L : ℝ) (hA : 0 < A) (hq : 1 < q)
    (hAL : A ≤ L) :
    L / q < A * q ^ geometricTerminalIndex A q L hA hq hAL ∧
      A * q ^ geometricTerminalIndex A q L hA hq hAL ≤ L := by
  obtain ⟨hl, hu⟩ := geometricTerminalIndex_spec A q L hA hq hAL
  refine ⟨(div_lt_iff₀ (by linarith : 0 < q)).mpr ?_, hl⟩
  simpa only [pow_succ, mul_assoc] using hu

end SRWTightness
