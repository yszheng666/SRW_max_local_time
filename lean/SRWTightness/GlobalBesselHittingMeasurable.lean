import SRWTightness.GlobalBesselInfiniteHitting

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Strict lower hitting over all nonnegative times
is a completed measurable global Bessel event. -/
theorem global_bessel_strict_hitting_nullMeasurable (x b : ℝ) :
    NullMeasurableSet {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω < b}
      (independentBridgeLaw (Fin 3)) := by
  let E := fun n : ℕ ↦ {ω | ∃ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1),
    actualGlobalBesselThree x t ω < b}
  have hm (n : ℕ) : NullMeasurableSet (E n) (independentBridgeLaw (Fin 3)) := by
    have hC := continuousPath_survival_nullMeasurable (independentBridgeLaw (Fin 3))
      (actualGlobalBesselThree x) (actualGlobalBesselThree_measurable x)
      (actualGlobalBesselThree_continuous x) ((n : ℝ) + 1) (fun _ ↦ b) continuous_const
    have he : E n = {ω | ∀ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1),
        b ≤ actualGlobalBesselThree x t ω}ᶜ := by
      ext ω
      simp only [E, Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_le, exists_prop]
    rw [he]
    exact hC.compl
  have he : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω < b} = ⋃ n, E n := by
    ext ω
    constructor
    · rintro ⟨t, ht, hhit⟩
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact Set.mem_iUnion.mpr ⟨n, t, ⟨ht, by linarith⟩, hhit⟩
    · intro hω
      obtain ⟨n, t, ht, hhit⟩ := Set.mem_iUnion.mp hω
      exact ⟨t, ht.1, hhit⟩
  rw [he]
  exact NullMeasurableSet.iUnion hm

/-- Closed lower hitting over the full half-line
is measurable in the completed global Bessel law. -/
theorem global_bessel_hitting_nullMeasurable (hReflection : BridgeReflectionInput)
    (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    NullMeasurableSet {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b}
      (independentBridgeLaw (Fin 3)) := by
  let μ := independentBridgeLaw (Fin 3)
  by_cases hxb : x ≤ b
  · have he : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨0, by simp, (actualGlobalBesselThree_initial x hx.le ω).le.trans hxb⟩
    rw [he]
    exact MeasurableSet.univ.nullMeasurableSet
  · have hbx : b < x := lt_of_not_ge hxb
    let S := {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω < b}
    let E := {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b}
    have hS : NullMeasurableSet S μ := global_bessel_strict_hitting_nullMeasurable x b
    have hsub : S ⊆ E := by
      rintro ω ⟨t, ht, hhit⟩
      exact ⟨t, ht, hhit.le⟩
    have he : μ E = μ S := by
      apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change μ.real E = μ.real S
      rw [global_bessel_infinite_hitting hReflection x b hx hb,
        global_bessel_infinite_strict_hitting hReflection x b hb hbx,
        min_eq_right ((div_le_one hx).mpr hbx.le)]
    exact hS.congr (ae_eq_of_subset_of_measure_ge hsub he.le hS (measure_ne_top μ E))

end SRWTightness
