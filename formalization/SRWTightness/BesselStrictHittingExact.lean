import SRWTightness.BesselLowerBarrierExact
import SRWTightness.KilledBrownianSurvivalMass

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Finite-horizon strict lower hitting is measurable in the completion of the Bessel law. -/
theorem bessel_strict_hitting_nullMeasurable (T x b : ℝ) :
    NullMeasurableSet {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω < b}
      (independentBridgeLaw (Fin 3)) := by
  have hm := continuousPath_survival_nullMeasurable (independentBridgeLaw (Fin 3))
    (actualBesselThree T x) (actualBesselThree_measurable T x)
    (actualBesselThree_ae_continuous T x) T (fun _ ↦ b) continuous_const
  have he : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω < b} =
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T, b ≤ actualBesselThree T x t ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_le, exists_prop]
  rw [he]
  exact hm.compl

/-- Exact finite-time Bessel lower hitting follows from the actual Doob transform. -/
theorem bessel_strict_hitting_exact (hReflection : BridgeReflectionInput)
    (T x b : ℝ) (hT : 0 < T) (hb : 0 < b) (hbx : b < x) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω < b} =
      (b / x) * (1 - (gaussianReal 0 T.toNNReal).real (Set.Icc (-(x - b)) (x - b))) := by
  have hm := continuousPath_survival_nullMeasurable (independentBridgeLaw (Fin 3))
    (actualBesselThree T x) (actualBesselThree_measurable T x)
    (actualBesselThree_ae_continuous T x) T (fun _ ↦ b) continuous_const
  have he : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, actualBesselThree T x t ω < b} =
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T, b ≤ actualBesselThree T x t ω}ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_forall, not_le, exists_prop]
  rw [he, measureReal_compl₀ hm, probReal_univ,
    bessel_lower_barrier_exact hReflection T x b hT hb hbx,
    killed_brownian_survival_mass hReflection T (x - b) hT (sub_pos.mpr hbx)]
  field_simp [(hb.trans hbx).ne']
  <;> ring

end SRWTightness
