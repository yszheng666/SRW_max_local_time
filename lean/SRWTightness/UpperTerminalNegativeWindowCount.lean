import SRWTightness.UpperTerminalNegativeWindowSum
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Floor.Ring

namespace SRWTightness

/-- A shifted unit grid has at most Q+1 points in a closed negative interval of length Q. -/
theorem upper_terminal_negative_window_card (I : Finset ℕ) (v Q : ℝ) (hQ : 0 ≤ Q)
    (hq : ∀ J ∈ I, -Q ≤ v - (J : ℝ) ∧ v - (J : ℝ) ≤ 0) :
    (I.card : ℝ) ≤ Q + 1 := by
  by_cases hI : I.Nonempty
  · let J₀ := I.min' hI
    have hmem : J₀ ∈ I := I.min'_mem hI
    have hmin (J : ℕ) (hJ : J ∈ I) : J₀ ≤ J := I.min'_le J hJ
    have hcard : I.card ≤ (Finset.range (⌊Q⌋₊ + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun J : ℕ ↦ J - J₀)
      · intro J hJ
        apply Finset.mem_range.mpr
        apply Nat.lt_succ_of_le
        apply Nat.le_floor
        rw [Nat.cast_sub (hmin J hJ)]
        have hh := hq J hJ
        have hb := hq J₀ hmem
        linarith
      · intro J hJ L hL he
        change J - J₀ = L - J₀ at he
        have hJmin := hmin J hJ
        have hLmin := hmin L hL
        omega
    have hr : (I.card : ℝ) ≤ (⌊Q⌋₊ : ℝ) + 1 := by
      simp only [Finset.card_range] at hcard
      exact_mod_cast hcard
    linarith [Nat.floor_le hQ]
  · have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    simp only [he, Finset.card_empty, Nat.cast_zero]
    linarith

/-- The entire negative shifted-window contribution has the exact interval-length prefactor. -/
theorem upper_terminal_negative_shifted_sum (I : Finset ℕ) (v d S β Q c : ℝ)
    (hd : 0 < d) (hQ : 0 ≤ Q) (hQS : Q ≤ S)
    (hq : ∀ J ∈ I, -Q ≤ v - (J : ℝ) ∧ v - (J : ℝ) ≤ 0) :
    (∑ J ∈ I, (S + (v - (J : ℝ))) *
      (1 + max (v - (J : ℝ)) 0 / Real.sqrt d) / d *
        Real.exp (β * (v - (J : ℝ)) - c * (max (v - (J : ℝ) - 1) 0) ^ 2 / d)) ≤
      (Q + 1) * (S / d * Real.exp (|β| * Q)) := by
  have hS : 0 ≤ S := hQ.trans hQS
  have hh := upper_terminal_negative_window_sum I (fun J ↦ v - (J : ℝ))
    d S β Q c hd hQ hQS hq
  exact hh.trans (mul_le_mul_of_nonneg_right
    (upper_terminal_negative_window_card I v Q hQ hq) (by positivity))

end SRWTightness
