import SRWTightness.GlobalBesselInverseMoment
import SRWTightness.BesselDelayedHittingInternal

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SRWTightness

/-- The global Bessel endpoint lies below a fixed radius with inverse-square-root probability. -/
theorem global_bessel_small_endpoint_bound (x b s : ℝ)
    (hx : 0 < x) (hb : 0 < b) (hs : 0 < s) :
    (independentBridgeLaw (Fin 3)).real {ω | actualGlobalBesselThree x s ω ≤ b} ≤
      (b * besselInverseMomentConstant) / Real.sqrt s := by
  have hmG := actualGlobalBesselThree_measurable x s
  have hmF := actualBesselThree_measurable s x s
  have he := congrArg (fun ρ : Measure ℝ ↦ ρ.real (Set.Iic b))
    (global_bessel_endpoint_law s x hs)
  rw [map_measureReal_apply hmG measurableSet_Iic,
    map_measureReal_apply hmF measurableSet_Iic] at he
  have hh := besselThreeDelayedHittingInput_internal s x b s hs hx hb hs le_rfl
  have hp : (independentBridgeLaw (Fin 3)).real {ω | actualBesselThree s x s ω ≤ b} ≤
      b * ∫ ω, (actualBesselThree s x s ω)⁻¹ ∂independentBridgeLaw (Fin 3) := by
    simpa only [Set.Icc_self, Set.mem_singleton_iff, exists_eq_left] using hh
  change (independentBridgeLaw (Fin 3)).real ((actualGlobalBesselThree x s) ⁻¹' Set.Iic b) ≤ _
  rw [he]
  exact hp.trans (by
    have hi := (bessel_three_inverse_moment_input_internal.2 s x s hs hx hs le_rfl).2
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hi hb.le)

/-- The global Bessel path exceeds every prescribed positive radius
at some integer time almost surely. -/
theorem global_bessel_exceeds_ae (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      ∃ n : ℕ, b < actualGlobalBesselThree x ((n : ℝ) + 1) ω := by
  let μ := independentBridgeLaw (Fin 3)
  let E := {ω | ∃ n : ℕ, b < actualGlobalBesselThree x ((n : ℝ) + 1) ω}
  have hbound (n : ℕ) : μ.real Eᶜ ≤
      (b * besselInverseMomentConstant) / Real.sqrt ((n : ℝ) + 1) := by
    have hsub : Eᶜ ⊆ {ω | actualGlobalBesselThree x ((n : ℝ) + 1) ω ≤ b} := by
      intro ω hω
      simp only [E, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_lt] at hω
      exact hω n
    exact (measureReal_mono hsub).trans
      (global_bessel_small_endpoint_bound x b ((n : ℝ) + 1) hx hb (by positivity))
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun n : ℕ ↦
      (b * besselInverseMomentConstant) / Real.sqrt ((n : ℝ) + 1)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp ht).const_div_atTop (b * besselInverseMomentConstant)
  have hz : μ.real Eᶜ = 0 := le_antisymm
    (ge_of_tendsto hl (Eventually.of_forall hbound)) measureReal_nonneg
  apply ae_iff.mpr
  exact (measureReal_eq_zero_iff (measure_ne_top μ Eᶜ)).mp hz

end SRWTightness
