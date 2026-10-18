import SRWTightness.OccupationMoments

open MeasureTheory

namespace SRWTightness

noncomputable def occupationSecondMoment (D : Finset Site) (x y z : Site) : ℝ :=
  ∫ ω, (domainLocalTime D x y ω : ℝ) * domainLocalTime D x z ω ∂pathLaw

 theorem occupationSecondMoment_zero_of_not_mem (D : Finset Site) (x y z : Site)
    (hx : x ∉ D) : occupationSecondMoment D x y z = 0 := by
  simp [occupationSecondMoment, domainLocalTime_zero_of_not_mem D x y hx]

 theorem integral_shifted_product (D : Finset Site) (x y z : Site) (a b : ℝ) :
    (∫ ω, (a + (domainLocalTime D x y ω : ℝ)) *
      (b + (domainLocalTime D x z ω : ℝ)) ∂pathLaw) =
      a * b + a * killedGreen D x z + b * killedGreen D x y + occupationSecondMoment D x y z := by
  have hy := integrable_domainLocalTime D x y
  have hz := integrable_domainLocalTime D x z
  have hp := integrable_domainLocalTime_mul D x y z
  have he : (fun ω ↦ (a + (domainLocalTime D x y ω : ℝ)) *
      (b + (domainLocalTime D x z ω : ℝ))) =
      (fun ω ↦ a * b + a * (domainLocalTime D x z ω : ℝ) +
        b * (domainLocalTime D x y ω : ℝ) +
          (domainLocalTime D x y ω : ℝ) * domainLocalTime D x z ω) := by
    funext ω
    ring
  have hia : Integrable (fun ω ↦ a * (domainLocalTime D x z ω : ℝ)) pathLaw := hz.const_mul a
  have hib : Integrable (fun ω ↦ b * (domainLocalTime D x y ω : ℝ)) pathLaw := hy.const_mul b
  have hiab : Integrable (fun ω ↦ a * b + a * (domainLocalTime D x z ω : ℝ)) pathLaw :=
    (integrable_const (a * b)).add hia
  have hiabc : Integrable (fun ω ↦ a * b + a * (domainLocalTime D x z ω : ℝ) +
      b * (domainLocalTime D x y ω : ℝ)) pathLaw := hiab.add hib
  rw [he, integral_add hiabc hp, integral_add hiab hib,
    integral_add (integrable_const (a * b)) hia]
  simp only [integral_const_mul]
  simp [killedGreen, occupationSecondMoment]

 theorem occupationSecondMoment_first_step (D : Finset Site) (x y z : Site) (hx : x ∈ D) :
    occupationSecondMoment D x y z =
      (if x = y then 1 else 0) * (if x = z then 1 else 0) +
      (if x = y then 1 else 0) * ((1 / 4 : ℝ) * ∑ d : Direction, killedGreen D (x + step d) z) +
      (if x = z then 1 else 0) * ((1 / 4 : ℝ) * ∑ d : Direction, killedGreen D (x + step d) y) +
      (1 / 4 : ℝ) * ∑ d : Direction, occupationSecondMoment D (x + step d) y z := by
  let a : ℝ := if x = y then 1 else 0
  let b : ℝ := if x = z then 1 else 0
  let f : Direction → Sample → ℝ := fun d ω ↦
    (a + (domainLocalTime D (x + step d) y ω : ℝ)) *
      (b + (domainLocalTime D (x + step d) z ω : ℝ))
  have hm (d : Direction) : Measurable (f d) := by
    exact (measurable_const.add ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_domainLocalTime D _ y))).mul
      (measurable_const.add ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
        (measurable_domainLocalTime D _ z)))
  have hi (d : Direction) : Integrable (f d) pathLaw := by
    have he : f d = (fun ω ↦ a * b + a * (domainLocalTime D (x + step d) z ω : ℝ) +
      b * (domainLocalTime D (x + step d) y ω : ℝ) +
        (domainLocalTime D (x + step d) y ω : ℝ) * domainLocalTime D (x + step d) z ω) := by
      funext ω
      dsimp [f]
      ring
    rw [he]
    exact (((integrable_const (a * b)).add ((integrable_domainLocalTime D _ z).const_mul a)).add
      ((integrable_domainLocalTime D _ y).const_mul b)).add (integrable_domainLocalTime_mul D _ y z)
  have he : (fun ω ↦ (domainLocalTime D x y ω : ℝ) * domainLocalTime D x z ω) =ᵐ[pathLaw]
      (fun ω ↦ f (ω 0) (shift 1 ω)) := by
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    simp only [domainLocalTime_first_step D x y hx ω hω,
      domainLocalTime_first_step D x z hx ω hω, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, f, a, b]
  unfold occupationSecondMoment
  rw [integral_congr_ae he, integral_first_step_future f hm hi]
  change (∫ d, (∫ ω, (a + (domainLocalTime D (x + step d) y ω : ℝ)) *
    (b + (domainLocalTime D (x + step d) z ω : ℝ)) ∂pathLaw) ∂directionLaw) = _
  simp_rw [integral_shifted_product]
  rw [integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_add (Integrable.of_finite) (Integrable.of_finite),
    integral_add (Integrable.of_finite) (Integrable.of_finite)]
  simp only [integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [integral_direction_average, integral_direction_average, integral_direction_average]
  rfl

end SRWTightness
