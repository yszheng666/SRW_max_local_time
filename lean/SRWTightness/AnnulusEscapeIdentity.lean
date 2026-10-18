import SRWTightness.AnnulusBarrierProbability

namespace SRWTightness

theorem exitPayoff_congr_on_compl (D : Finset Site) (f g : Site → ℝ)
    (hfg : ∀ y, y ∉ D → f y = g y) (x : Site) : exitPayoff D f x = exitPayoff D g x :=
  le_antisymm (exitPayoff_mono_on_compl D f g (fun y hy ↦ (hfg y hy).le) x)
    (exitPayoff_mono_on_compl D g f (fun y hy ↦ (hfg y hy).ge) x)

theorem one_sub_setHitProbability_harmonic (D K : Finset Site) (x : Site)
    (hx : x ∈ D) (hK : x ∉ K) :
    1 - setHitProbability D K x =
      (1 / 4 : ℝ) * ∑ d : Direction, (1 - setHitProbability D K (x + step d)) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
  simp only [Direction, Fintype.card_fin, nsmul_eq_mul]
  have hh := setHitProbability_harmonic D K x hx hK
  linarith

/-- Annulus outer exit is the actual escape-before-hitting probability. -/
theorem annulusOuterExitProbability_eq_one_sub_hit (a R : ℝ) (x : Site) :
    annulusOuterExitProbability a R x = 1 - setHitProbability (diskFinset R) (diskFinset a) x := by
  let D := annulusFinset a R
  let f : Site → ℝ := fun y ↦ 1 - setHitProbability (diskFinset R) (diskFinset a) y
  have hh : f x = exitPayoff D f x := by
    apply harmonic_eq_exitPayoff
    intro y hy
    exact one_sub_setHitProbability_harmonic _ _ y (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  have he : exitPayoff D f x = exitPayoff D (fun y ↦ if y ∉ diskFinset R then 1 else 0) x := by
    apply exitPayoff_congr_on_compl
    intro y hy
    by_cases hyR : y ∈ diskFinset R
    · have hya : y ∈ diskFinset a := by
        by_contra hna
        exact hy (Finset.mem_sdiff.mpr ⟨hyR, hna⟩)
      simp only [f, setHitProbability_one _ _ y hyR hya, sub_self, not_true_eq_false,
        if_false, hyR]
    · simp only [f, setHitProbability_zero_of_not_mem _ _ y hyR, sub_zero, hyR,
        not_false_eq_true, if_true]
  rw [he, exitPayoff_outside_eq_probability] at hh
  exact hh.symm

theorem escape_double_radius_near_upper (a : ℝ) (ha : 4 ≤ a) (x : Site)
    (hxlo : a ^ 2 ≤ normSq x) (hxhi : normSq x ≤ (a + 1) ^ 2) :
    1 - setHitProbability (diskFinset (2 * a)) (diskFinset a) x ≤ 16 / (3 * a) := by
  rw [← annulusOuterExitProbability_eq_one_sub_hit]
  exact annulusOuterExitProbability_near_upper a ha x hxlo hxhi

end SRWTightness
