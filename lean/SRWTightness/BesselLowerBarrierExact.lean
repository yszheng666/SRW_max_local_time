import SRWTightness.KilledBrownianDoobLowerBarrier
import SRWTightness.KilledBrownianDoobBesselPathLaw
import SRWTightness.BesselContinuity

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual Bessel path's full lower-barrier probability is an exact killed-kernel expression. -/
theorem bessel_lower_barrier_exact (hReflection : BridgeReflectionInput)
    (T x b : ℝ) (hT : 0 < T) (hb : 0 < b) (hbx : b < x) :
    (independentBridgeLaw (Fin 3)).real
      {ω | ∀ t ∈ Set.Icc (0 : ℝ) T, b ≤ actualBesselThree T x t ω} =
      ((x - b) + b * (killedBrownianDensityLaw T (x - b)).real Set.univ) / x := by
  let C : Set (Set.Icc (0 : ℝ) T → ℝ) :=
    {p | (fun u ↦ -p u) ∈ dyadicFlatPathEvent T (-b)}
  let D := fun ω (u : Set.Icc (0 : ℝ) T) ↦
    x - Real.sqrt T * gaussianDyadicPath ω (u / T)
  let R := fun ω (u : Set.Icc (0 : ℝ) T) ↦ actualBesselThree T x u ω
  let P := fun ω (u : Set.Icc (0 : ℝ) T) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T)
  have hC : MeasurableSet C := (dyadicFlatPathEvent_measurable T (-b)).preimage
    (measurable_pi_lambda _ (fun u ↦ (measurable_pi_apply u).neg))
  have hD : Measurable D := measurable_pi_lambda _ (fun _ ↦
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _)))
  have hR : Measurable R := measurable_pi_lambda _ (fun _ ↦ actualBesselThree_measurable T x _)
  have he := congrArg (fun ρ : Measure (Set.Icc (0 : ℝ) T → ℝ) ↦ ρ.real C)
    (killed_brownian_doob_bessel_path_law hReflection T x hT (hb.trans hbx))
  change ((killedBrownianDoobCoefficientLaw T x).map D).real C =
    ((independentBridgeLaw (Fin 3)).map R).real C at he
  rw [map_measureReal_apply hD hC, map_measureReal_apply hR hC] at he
  have hset : D ⁻¹' C = P ⁻¹' dyadicFlatPathEvent T (x - b) := by
    ext ω
    change (∀ n j : ℕ, ∀ h : (j : ℝ) / 2 ^ n ≤ T,
      -(x - Real.sqrt T * gaussianDyadicPath ω (((j : ℝ) / 2 ^ n) / T)) ≤ -b) ↔
      (∀ n j : ℕ, ∀ h : (j : ℝ) / 2 ^ n ≤ T,
        Real.sqrt T * gaussianDyadicPath ω (((j : ℝ) / 2 ^ n) / T) ≤ x - b)
    constructor <;> intro h n j hj <;> have hh := h n j hj <;> linarith
  have hfull : {ω | ∀ t ∈ Set.Icc (0 : ℝ) T, b ≤ actualBesselThree T x t ω} =ᵐ[
      independentBridgeLaw (Fin 3)] (R ⁻¹' C) := by
    filter_upwards [actualBesselThree_ae_continuous T x] with ω hω
    apply propext
    change (∀ t ∈ Set.Icc (0 : ℝ) T, b ≤ actualBesselThree T x t ω) ↔
      (fun u : Set.Icc (0 : ℝ) T ↦ -actualBesselThree T x u ω) ∈ dyadicFlatPathEvent T (-b)
    simpa only [neg_le_neg_iff] using
      (continuous_flat_iff_dyadic (fun t ↦ -actualBesselThree T x t ω) hω.neg T (-b))
  rw [measureReal_congr hfull, ← he, hset]
  exact killed_brownian_doob_lower_barrier hReflection T x b hT hb hbx

end SRWTightness
