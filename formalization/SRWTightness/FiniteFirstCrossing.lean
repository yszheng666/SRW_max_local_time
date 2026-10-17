import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace SRWTightness

/-- A finite path that crosses a level has a unique first crossing index. -/
theorem finite_first_crossing (w : ℕ → ℝ) (q : ℝ) (n : ℕ)
    (h : ∃ k ≤ n, q ≤ w k) :
    ∃ k ≤ n, q ≤ w k ∧ ∀ j < k, w j < q := by
  classical
  refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
  intro j hj
  apply lt_of_not_ge
  intro hq
  exact Nat.find_min h hj ⟨(Nat.le_of_lt hj).trans (Nat.find_spec h).1, hq⟩

/-- Two first crossing indices of the same finite path agree. -/
theorem first_crossing_unique (w : ℕ → ℝ) (q : ℝ) (j k : ℕ)
    (hj : q ≤ w j ∧ ∀ i < j, w i < q)
    (hk : q ≤ w k ∧ ∀ i < k, w i < q) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact False.elim ((not_lt_of_ge hj.1) (hk.2 j h))
  · exact h
  · exact False.elim ((not_lt_of_ge hk.1) (hj.2 k h))

/-- A bound on each upward increment bounds the overshoot at the first crossing. -/
theorem first_crossing_overshoot (w : ℕ → ℝ) (q δ : ℝ) (n k : ℕ)
    (hzero : w 0 < q) (hkn : k ≤ n)
    (hk : q ≤ w k ∧ ∀ j < k, w j < q)
    (hstep : ∀ j < n, w (j + 1) - w j ≤ δ) :
    0 < k ∧ q ≤ w k ∧ w k < q + δ := by
  have hk0 : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    subst k
    linarith [hk.1]
  have hp : k - 1 < k := by omega
  have hn : k - 1 < n := by omega
  have he : k - 1 + 1 = k := by omega
  have hs := hstep (k - 1) hn
  rw [he] at hs
  exact ⟨hk0, hk.1, by linarith [hk.2 (k - 1) hp]⟩

end SRWTightness
