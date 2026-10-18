import SRWTightness.CompetingEntranceLaw

namespace SRWTightness

/-- A small additive half-probability error gives the exponential bounds used by record comparison. -/
theorem half_probability_exponential_bounds (p ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : |p - 1 / 2| ≤ ε) : Real.exp (-(4 * ε)) / 2 ≤ p ∧ p ≤ Real.exp (4 * ε) / 2 := by
  have hl := (abs_le.mp hp).1
  have hu := (abs_le.mp hp).2
  have hexp := Real.add_one_le_exp (4 * ε)
  have hpos := Real.exp_pos (4 * ε)
  have hlower : Real.exp (-(4 * ε)) ≤ 1 - 2 * ε := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ hpos).mpr
    have hm := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1 - 2 * ε by linarith)
    nlinarith [mul_nonneg hε (show 0 ≤ 1 - 4 * ε by linarith)]
  constructor <;> linarith

/-- Both actual competing masses satisfy the multiplicative comparison input. -/
theorem competing_mass_exponential_bounds (D K : Finset Site) (hKD : K ⊆ D) (x : Site)
    (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 4)
    (hp : |setHitProbability D K x - 1 / 2| ≤ ε) :
    (Real.exp (-(4 * ε)) / 2 ≤ (competingEntranceLaw D K x).real Set.univ ∧
      (competingEntranceLaw D K x).real Set.univ ≤ Real.exp (4 * ε) / 2) ∧
    (Real.exp (-(4 * ε)) / 2 ≤ competingExitMass D K x ∧
      competingExitMass D K x ≤ Real.exp (4 * ε) / 2) := by
  rw [competingEntranceLaw_mass D K hKD, competingExitMass_eq_one_sub_hit D K hKD]
  refine ⟨half_probability_exponential_bounds _ ε hε hsmall hp, ?_⟩
  apply half_probability_exponential_bounds _ ε hε hsmall
  have he : |1 - setHitProbability D K x - 1 / 2| =
      |setHitProbability D K x - 1 / 2| := by
    rw [show 1 - setHitProbability D K x - 1 / 2 = -(setHitProbability D K x - 1 / 2) by ring,
      abs_neg]
  rw [he]
  exact hp

end SRWTightness
