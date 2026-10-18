import SRWTightness.KilledGreen

open MeasureTheory

namespace SRWTightness

 theorem localTime_sum_translate (D : Finset Site) (x : Site) (ω : Sample) (n : ℕ)
    (hstay : ∀ i < n, x + position ω i ∈ D) :
    ∑ y ∈ D, localTime ω n (y - x) = n := by
  simp only [localTime]
  rw [Finset.sum_comm]
  have h : ∀ i ∈ Finset.range n,
      (∑ y ∈ D, if position ω i = y - x then (1 : ℕ) else 0) = 1 := by
    intro i hi
    have hmem := hstay i (Finset.mem_range.mp hi)
    have he (y : Site) : position ω i = y - x ↔ y = x + position ω i := by
      constructor
      · intro h
        rw [h]
        simp
      · intro h
        rw [h]
        simp
    simp_rw [he]
    simp [hmem]
  simp only [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

 theorem domainLocalTime_sum (D : Finset Site) (x : Site) (ω : Sample) :
    ∑ y ∈ D, domainLocalTime D x y ω = domainSteps D x ω := by
  apply localTime_sum_translate
  intro i hi
  by_contra hnot
  have he : domainExit D x ω ≤ i := (domainExit_le_iff D x ω i).mpr ⟨i, le_rfl, hnot⟩
  have hfin : domainExit D x ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top he
  rw [← coe_domainSteps D x ω hfin] at he
  exact (not_le_of_gt hi) (WithTop.coe_le_coe.mp he)

 theorem killedGreen_row_sum (D : Finset Site) (x : Site) :
    ∑ y ∈ D, killedGreen D x y = ∫ ω, (domainSteps D x ω : ℝ) ∂pathLaw := by
  simp only [killedGreen]
  rw [← integral_finsetSum D (fun y _ ↦ integrable_domainLocalTime D x y)]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [← Nat.cast_sum, domainLocalTime_sum]

end SRWTightness
