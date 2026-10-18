import SRWTightness.GlobalBrownianFiniteHorizonLaw
import SRWTightness.BesselPast

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual three-coordinate radial Brownian process on the full nonnegative time half-line. -/
noncomputable def actualGlobalBesselThree (x t : ℝ)
    (ω : Fin 3 → GaussianCoefficientSpace) : ℝ :=
  Real.sqrt (∑ i : Fin 3, ((if i = 0 then x else 0) + globalBrownianPath t (ω i)) ^ 2)

/-- Global Bessel evaluations are measurable. -/
theorem actualGlobalBesselThree_measurable (x t : ℝ) :
    Measurable (actualGlobalBesselThree x t) := by
  unfold actualGlobalBesselThree
  apply Measurable.sqrt
  apply Finset.measurable_sum
  intro i hi
  exact (measurable_const.add
    ((globalBrownianPath_measurable t).comp (measurable_pi_apply i))).pow_const 2

/-- The global radial process starts at its prescribed nonnegative radius. -/
theorem actualGlobalBesselThree_initial (x : ℝ) (hx : 0 ≤ x)
    (ω : Fin 3 → GaussianCoefficientSpace) : actualGlobalBesselThree x 0 ω = x := by
  simp [actualGlobalBesselThree, globalBrownianPath_zero, Fin.sum_univ_succ, Real.sqrt_sq hx]

/-- The global radial construction has continuous paths almost surely. -/
theorem actualGlobalBesselThree_continuous (x : ℝ) :
    ∀ᵐ ω ∂independentBridgeLaw (Fin 3), Continuous (fun t ↦ actualGlobalBesselThree x t ω) := by
  have hh : ∀ᵐ ω ∂independentBridgeLaw (Fin 3),
      ∀ i : Fin 3, Continuous (fun t ↦ globalBrownianPath t (ω i)) := by
    apply ae_all_iff.mpr
    intro i
    have hp := measurePreserving_eval_infinitePi (fun _ : Fin 3 ↦ gaussianCoefficientLaw) i
    exact hp.quasiMeasurePreserving.ae globalBrownianPath_continuous
  filter_upwards [hh] with ω hω
  unfold actualGlobalBesselThree
  apply Continuous.sqrt
  apply continuous_finset_sum
  intro i hi
  exact (continuous_const.add (hω i)).pow 2

/-- Every finite global Bessel path restriction is the original actual finite-horizon Bessel law. -/
theorem global_bessel_finite_horizon_law (T x : ℝ) (hT : 0 < T) :
    (independentBridgeLaw (Fin 3)).map
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ actualGlobalBesselThree x u ω) =
    (independentBridgeLaw (Fin 3)).map
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ actualBesselThree T x u ω) := by
  let P := fun (ω : Fin 3 → GaussianCoefficientSpace) (i : Fin 3)
    (u : Set.Icc (0 : ℝ) T) ↦ globalBrownianPath u (ω i)
  have hm : Measurable (fun ω (u : Set.Icc (0 : ℝ) T) ↦ globalBrownianPath u ω) :=
    measurable_pi_lambda _ (fun u ↦ globalBrownianPath_measurable u)
  have hP : Measurable P := measurable_pi_lambda _ (fun i ↦
    hm.comp (measurable_pi_apply i))
  have hv : (independentBridgeLaw (Fin 3)).map P =
      (independentBridgeLaw (Fin 3)).map (besselPast T T) := by
    rw [independentBridgeLaw, Measure.infinitePi_eq_pi]
    have hmQ : Measurable (fun ω (u : Set.Icc (0 : ℝ) T) ↦
        Real.sqrt T * gaussianDyadicPath ω (u / T)) :=
      measurable_pi_lambda _ (fun _ ↦ measurable_const.mul (gaussianDyadicPath_measurable _))
    have hQ : (Measure.pi (fun _ : Fin 3 ↦ gaussianCoefficientLaw)).map (besselPast T T) =
        Measure.pi (fun _ : Fin 3 ↦ gaussianCoefficientLaw.map
          (fun ω (u : Set.Icc (0 : ℝ) T) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T))) :=
      Measure.pi_map_pi (μ := fun _ : Fin 3 ↦ gaussianCoefficientLaw)
        (fun _ ↦ hmQ.aemeasurable)
    rw [Measure.pi_map_pi (μ := fun _ : Fin 3 ↦ gaussianCoefficientLaw)
      (fun _ ↦ hm.aemeasurable), hQ]
    congr 1
    funext i
    exact global_brownian_finite_horizon_law T hT
  let H := fun p : Fin 3 → Set.Icc (0 : ℝ) T → ℝ ↦
    fun u ↦ Real.sqrt (∑ i : Fin 3, ((if i = 0 then x else 0) + p i u) ^ 2)
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro u
    dsimp [H]
    fun_prop
  have he := congrArg (fun ρ : Measure (Fin 3 → Set.Icc (0 : ℝ) T → ℝ) ↦ ρ.map H) hv
  rw [Measure.map_map hH hP, Measure.map_map hH (besselPast_measurable T T)] at he
  exact he

end SRWTightness
