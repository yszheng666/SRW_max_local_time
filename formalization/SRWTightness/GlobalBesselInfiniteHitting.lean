import SRWTightness.GlobalBesselStrictHitting
import SRWTightness.GaussianSurvivalMassDecay

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SRWTightness

/-- The actual global Bessel path has the exact infinite-time strict lower-hitting probability. -/
theorem global_bessel_infinite_strict_hitting (hReflection : BridgeReflectionInput)
    (x b : ℝ) (hb : 0 < b) (hbx : b < x) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω < b} = b / x := by
  let μ := independentBridgeLaw (Fin 3)
  let E := fun n : ℕ ↦ {ω | ∃ t ∈ Set.Icc (0 : ℝ) ((n : ℝ) + 1),
    actualGlobalBesselThree x t ω < b}
  have hmono : Monotone E := by
    intro n m hnm ω hω
    obtain ⟨t, ht, hhit⟩ := hω
    exact ⟨t, ⟨ht.1, ht.2.trans (by exact_mod_cast Nat.add_le_add_right hnm 1)⟩, hhit⟩
  have he : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω < b} = ⋃ n, E n := by
    ext ω
    constructor
    · rintro ⟨t, ht, hhit⟩
      obtain ⟨n, hn⟩ := exists_nat_gt t
      exact Set.mem_iUnion.mpr ⟨n, t, ⟨ht, by linarith⟩, hhit⟩
    · intro hω
      obtain ⟨n, t, ht, hhit⟩ := Set.mem_iUnion.mp hω
      exact ⟨t, ht.1, hhit⟩
  have hlim : Tendsto (fun n : ℕ ↦ μ.real (E n)) atTop (𝓝 (μ.real (⋃ n, E n))) := by
    simpa only [Measure.real, Function.comp_def] using
      (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp
        (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  have htime : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero := (gaussian_survival_mass_tendsto_zero (x - b) (sub_pos.mpr hbx)).comp htime
  have hformula (n : ℕ) : μ.real (E n) = (b / x) *
      (1 - (gaussianReal 0 (((n : ℝ) + 1).toNNReal)).real (Set.Icc (-(x - b)) (x - b))) :=
    global_bessel_strict_hitting_finite hReflection ((n : ℝ) + 1) x b (by positivity) hb hbx
  have hlim' : Tendsto (fun n : ℕ ↦ μ.real (E n)) atTop (𝓝 (b / x)) := by
    simp_rw [hformula]
    simpa only [sub_zero, mul_one, Function.comp_def] using
      (tendsto_const_nhds (x := b / x)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hzero)
  rw [he]
  exact tendsto_nhds_unique hlim hlim'

/-- The original infinite-time Bessel lower-hitting identity holds for a genuine global process. -/
theorem global_bessel_infinite_hitting (hReflection : BridgeReflectionInput)
    (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} = min 1 (b / x) := by
  let μ := independentBridgeLaw (Fin 3)
  by_cases hxb : x ≤ b
  · have he : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact ⟨0, by simp, (actualGlobalBesselThree_initial x hx.le ω).le.trans hxb⟩
    rw [he, probReal_univ, min_eq_left ((one_le_div hx).mpr hxb)]
  · have hbx : b < x := lt_of_not_ge hxb
    rw [min_eq_right ((div_le_one hx).mpr hbx.le)]
    apply le_antisymm
    · apply le_of_forall_gt_imp_ge_of_dense
      intro r hr
      by_cases h1 : 1 ≤ r
      · exact measureReal_le_one.trans h1
      · have hr1 : r < 1 := lt_of_not_ge h1
        have hbr : b < r * x := (div_lt_iff₀ hx).mp hr
        have hrx : r * x < x := by nlinarith
        have hsub : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} ⊆
            {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω < r * x} := by
          rintro ω ⟨t, ht, hhit⟩
          exact ⟨t, ht, hhit.trans_lt hbr⟩
        have hh := measureReal_mono hsub (μ := μ)
        rw [global_bessel_infinite_strict_hitting hReflection x (r * x)
          (hb.trans hbr) hrx] at hh
        simpa only [mul_div_cancel_right₀ _ hx.ne'] using hh
    · have hsub : {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω < b} ⊆
          {ω | ∃ t ∈ Set.Ici (0 : ℝ), actualGlobalBesselThree x t ω ≤ b} := by
        rintro ω ⟨t, ht, hhit⟩
        exact ⟨t, ht, hhit.le⟩
      have hh := measureReal_mono hsub (μ := μ)
      rw [global_bessel_infinite_strict_hitting hReflection x b hb hbx] at hh
      exact hh

end SRWTightness
