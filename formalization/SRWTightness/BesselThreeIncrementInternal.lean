import SRWTightness.BesselCoordinateIncrement
import SRWTightness.BesselRadialIncrementBound

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The complete original radial Brownian increment input is proved by coordinate domination. -/
theorem bessel_three_increment_input_internal : BesselThreeIncrementInput := by
  intro T x r s hT hx hr hrs hsT
  let f := fun i (ω : Fin 3 → GaussianCoefficientSpace) ↦
    (Real.sqrt T * (gaussianDyadicPath (ω i) (s / T) -
      gaussianDyadicPath (ω i) (r / T))) ^ 2
  have hi (i : Fin 3) : Integrable (f i) (independentBridgeLaw (Fin 3)) :=
    (bessel_coordinate_increment_second_moment T r s i hT hr hrs hsT).1
  have hsum : Integrable (fun ω ↦ ∑ i : Fin 3, f i ω) (independentBridgeLaw (Fin 3)) :=
    integrable_finsetSum _ (fun i _ ↦ hi i)
  have hm (v : ℝ) : Measurable (actualBesselThree T x v) := by
    unfold actualBesselThree
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_const.add (measurable_const.mul
      ((gaussianDyadicPath_measurable _).comp (measurable_pi_apply i)))).pow_const 2
  have hleft : Integrable
      (fun ω ↦ (actualBesselThree T x s ω - actualBesselThree T x r ω) ^ 2)
      (independentBridgeLaw (Fin 3)) := by
    apply hsum.mono' (((hm s).sub (hm r)).pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact bessel_three_increment_pathwise T x r s ω
  refine ⟨hleft, ?_⟩
  have hh := integral_mono hleft hsum (bessel_three_increment_pathwise T x r s)
  rw [integral_finsetSum _ (fun i _ ↦ hi i)] at hh
  have he (i : Fin 3) : (∫ ω, f i ω ∂independentBridgeLaw (Fin 3)) = s - r :=
    (bessel_coordinate_increment_second_moment T r s i hT hr hrs hsT).2
  simpa only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] using hh

end SRWTightness
