import SRWTightness.TailRecurrence
import SRWTightness.GreenHarmonic
import Mathlib.Tactic.FieldSimp

namespace SRWTightness

 theorem occupationTail_green_ratio (D : Finset Site) (x y : Site) (hy : y ∈ D)
    (k : ℕ) (hk : 0 < k) :
    occupationTail D y k x = (killedGreen D x y / killedGreen D y y) * occupationTail D y k y := by
  by_cases hx : x ∈ D
  · let yy : D := ⟨y, hy⟩
    have hh : ∀ z : D, z ≠ yy → occupationTail D y k z =
        (1 / 4 : ℝ) * ∑ d : Direction, occupationTail D y k ((z : Site) + step d) := by
      intro z hz
      apply occupationTail_first_step_of_ne D z y z.property _ k
      exact fun h ↦ hz (Subtype.ext h)
    have hz : ∀ z, z ∉ D → occupationTail D y k z = 0 :=
      fun z h ↦ occupationTail_zero_of_not_mem D z y h k hk
    have hfx := harmonic_off_site_green_column D (occupationTail D y k) hz yy hh (⟨x, hx⟩ : D)
    have hfy := harmonic_off_site_green_column D (occupationTail D y k) hz yy hh yy
    have hg : killedGreen D y y ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (killedGreen_diag_ge_one D y hy))
    let c := occupationTail D y k y - (1 / 4 : ℝ) *
      ∑ d : Direction, occupationTail D y k (y + step d)
    calc
      occupationTail D y k x = killedGreen D x y * c := hfx
      _ = (killedGreen D x y / killedGreen D y y) * (killedGreen D y y * c) := by field_simp
      _ = _ := congrArg (fun z : ℝ ↦ (killedGreen D x y / killedGreen D y y) * z) hfy.symm
  · rw [occupationTail_zero_of_not_mem D x y hx k hk, killedGreen_zero_of_not_mem D x y hx]
    simp

 theorem occupationTail_self_recurrence (D : Finset Site) (y : Site) (hy : y ∈ D)
    (k : ℕ) (hk : 0 < k) :
    occupationTail D y (k + 1) y = (1 - 1 / killedGreen D y y) * occupationTail D y k y := by
  rw [occupationTail_succ_at_self D y hy k]
  have hs : (∑ d : Direction, occupationTail D y k (y + step d)) =
      ∑ d : Direction, (killedGreen D (y + step d) y / killedGreen D y y) *
        occupationTail D y k y :=
    Finset.sum_congr rfl (fun d _ ↦ occupationTail_green_ratio D _ y hy k hk)
  rw [hs]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  have hg : killedGreen D y y ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (killedGreen_diag_ge_one D y hy))
  have havg : (1 / 4 : ℝ) * ∑ d : Direction, killedGreen D (y + step d) y = killedGreen D y y - 1 := by
    have h := killedGreen_first_step_sum D y y hy
    simp at h
    linarith
  calc
    _ = (((1 / 4 : ℝ) * ∑ d : Direction, killedGreen D (y + step d) y) /
      killedGreen D y y) * occupationTail D y k y := by ring
    _ = ((killedGreen D y y - 1) / killedGreen D y y) * occupationTail D y k y := by rw [havg]
    _ = _ := by field_simp <;> ring

 theorem occupationTail_self_formula (D : Finset Site) (y : Site) (hy : y ∈ D) (j : ℕ) :
    occupationTail D y (j + 1) y = (1 - 1 / killedGreen D y y) ^ j := by
  induction j with
  | zero => simpa using occupationTail_one_at_self D y hy
  | succ j ih =>
    rw [occupationTail_self_recurrence D y hy (j + 1) (Nat.succ_pos j), ih, pow_succ]
    ring

/-- Exact finite-domain one-point geometric tail, with its first-hitting prefactor. -/
theorem occupation_probability_ge (D : Finset Site) (x y : Site) (hy : y ∈ D) (k : ℕ) (hk : 1 ≤ k) :
    pathLaw.real {ω | k ≤ domainLocalTime D x y ω} =
      (killedGreen D x y / killedGreen D y y) * (1 - 1 / killedGreen D y y) ^ (k - 1) := by
  rw [← occupationTail_eq_probability, occupationTail_green_ratio D x y hy k hk]
  have h : k = (k - 1) + 1 := by omega
  rw [h, occupationTail_self_formula D y hy]
  simp

end SRWTightness
