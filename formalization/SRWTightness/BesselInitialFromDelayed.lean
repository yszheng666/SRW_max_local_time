import SRWTightness.BesselSharpInverseMoment

open MeasureTheory
namespace SRWTightness

/-- The actual radial process begins at its prescribed positive radius. -/
theorem actualBesselThree_initial (T x : ℝ) (hx : 0 ≤ x)
    (ω : Fin 3 → GaussianCoefficientSpace) : actualBesselThree T x 0 ω = x := by
  simp [actualBesselThree, gaussianDyadicPath_zero, Fin.sum_univ_succ, Real.sqrt_sq hx]

/-- The original initial hitting input follows from delayed hitting and the proved sharp moment. -/
theorem besselThreeHittingInput_of_delayed (hHit : BesselThreeDelayedHittingInput) :
    BesselThreeHittingInput := by
  intro T x b hT hx hb
  apply le_min measureReal_le_one
  by_cases hxb : x ≤ b
  · exact measureReal_le_one.trans ((one_le_div hx).mpr hxb)
  have hbx : b < x := lt_of_not_ge hxb
  let μ := independentBridgeLaw (Fin 3)
  let E : ℕ → Set (Fin 3 → GaussianCoefficientSpace) := fun n ↦
    {ω | ∃ t ∈ Set.Icc (T / ((n : ℝ) + 1)) T, actualBesselThree T x t ω ≤ b}
  have hs (n : ℕ) : 0 < T / ((n : ℝ) + 1) := div_pos hT (by positivity)
  have hsT (n : ℕ) : T / ((n : ℝ) + 1) ≤ T := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hm : Monotone E := by
    intro n m hnm ω hω
    obtain ⟨t, ht, hh⟩ := hω
    refine ⟨t, ⟨?_, ht.2⟩, hh⟩
    apply le_trans _ ht.1
    exact div_le_div_of_nonneg_left hT.le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have he : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω ≤ b} = ⋃ n, E n := by
    ext ω
    constructor
    · rintro ⟨t, ht, hh⟩
      have htpos : 0 < t := by
        by_contra hn
        have hz : t = 0 := le_antisymm (le_of_not_gt hn) ht.1
        rw [hz, actualBesselThree_initial T x hx.le] at hh
        exact (not_le_of_gt hbx) hh
      obtain ⟨n, hn⟩ := exists_nat_gt (T / t)
      apply Set.mem_iUnion.mpr
      refine ⟨n, t, ⟨?_, ht.2⟩, hh⟩
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      have hh' := (div_lt_iff₀ htpos).mp hn
      nlinarith
    · intro hω
      obtain ⟨n, t, ht, hh⟩ := Set.mem_iUnion.mp hω
      exact ⟨t, ⟨(hs n).le.trans ht.1, ht.2⟩, hh⟩
  have hbound (n : ℕ) : μ.real (E n) ≤ b / x := by
    have hd := hHit T x b (T / ((n : ℝ) + 1)) hT hx hb (hs n) (hsT n)
    have hi := bessel_three_sharp_inverse_moment T x (T / ((n : ℝ) + 1))
      hT hx (hs n) (hsT n)
    exact hd.trans (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hi hb.le)
  rw [he]
  have hμ : μ (⋃ n, E n) ≤ ENNReal.ofReal (b / x) := by
    rw [hm.measure_iUnion]
    apply iSup_le
    intro n
    rw [← ofReal_measureReal (measure_ne_top μ (E n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ).trans_eq
    (ENNReal.toReal_ofReal (div_nonneg hb.le hx.le))

end SRWTightness
