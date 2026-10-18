import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory
namespace SRWTightness

/-- The radial Laplace substitution has a strictly positive dimension-three Jacobian. -/
theorem radial_laplace_substitution_deriv (s t : ℝ) (hs : 0 ≤ s) :
    HasDerivAt (fun u : ℝ ↦ u / Real.sqrt (1 + 2 * s * u ^ 2))
      ((Real.sqrt (1 + 2 * s * t ^ 2))⁻¹ ^ 3) t := by
  have ha : 0 < 1 + 2 * s * t ^ 2 := by positivity
  have hr : 0 < Real.sqrt (1 + 2 * s * t ^ 2) := Real.sqrt_pos.mpr ha
  have hd : HasDerivAt (fun u : ℝ ↦ 1 + 2 * s * u ^ 2) (4 * s * t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul (2 * s)).const_add 1 using 1 <;> try rfl
    simp only [id_eq]
    ring
  convert (hasDerivAt_id t).div (hd.sqrt ha.ne') hr.ne' using 1 <;> try rfl
  simp only [id_eq]
  have hsq := Real.sq_sqrt ha.le
  field_simp
  nlinarith

/-- The positive radial substitution is injective, with image in the positive half-line. -/
theorem radial_laplace_substitution_injective (s : ℝ) (hs : 0 ≤ s) :
    Function.Injective (fun u : ℝ ↦ u / Real.sqrt (1 + 2 * s * u ^ 2)) := by
  apply StrictMono.injective
  apply strictMono_of_hasDerivAt_pos (fun t ↦ radial_laplace_substitution_deriv s t hs)
  intro t
  positivity

/-- The dimension-three Laplace integral is bounded by the unshifted Gaussian half integral. -/
theorem radial_laplace_integral_bound (s x : ℝ) (hs : 0 ≤ s) (hx : 0 < x) :
    (∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2)) /
        (Real.sqrt (1 + 2 * s * t ^ 2)) ^ 3) ≤
      Real.sqrt Real.pi / (2 * x) := by
  let f : ℝ → ℝ := fun t ↦ t / Real.sqrt (1 + 2 * s * t ^ 2)
  let g : ℝ → ℝ := fun u ↦ Real.exp (-(x ^ 2) * u ^ 2)
  have hd (t : ℝ) : HasDerivAt f ((Real.sqrt (1 + 2 * s * t ^ 2))⁻¹ ^ 3) t :=
    radial_laplace_substitution_deriv s t hs
  have he := integral_image_eq_integral_abs_deriv_smul (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ ↦ (hd t).hasDerivWithinAt)
    (radial_laplace_substitution_injective s hs).injOn g
  have hi : IntegrableOn g (Set.Ioi 0) :=
    (integrable_exp_neg_mul_sq (sq_pos_of_pos hx)).integrableOn
  have hsub : f '' Set.Ioi 0 ⊆ Set.Ioi 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact div_pos ht (Real.sqrt_pos.mpr (by positivity))
  have hle := setIntegral_mono_set hi
    (Filter.Eventually.of_forall (fun u ↦ (Real.exp_pos _).le))
    (Filter.Eventually.of_forall hsub)
  change (∫ u in f '' Set.Ioi 0, g u) ≤ ∫ u in Set.Ioi 0, g u at hle
  rw [he] at hle
  have hfun (t : ℝ) :
      |(Real.sqrt (1 + 2 * s * t ^ 2))⁻¹ ^ 3| • g (f t) =
        Real.exp (-(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2)) /
          (Real.sqrt (1 + 2 * s * t ^ 2)) ^ 3 := by
    have ha : 0 < 1 + 2 * s * t ^ 2 := by positivity
    rw [abs_of_nonneg (by positivity), smul_eq_mul]
    dsimp [g, f]
    rw [div_pow, Real.sq_sqrt ha.le]
    have harg : -(x ^ 2) * (t ^ 2 / (1 + 2 * s * t ^ 2)) =
        -(t ^ 2) * x ^ 2 / (1 + 2 * s * t ^ 2) := by ring
    rw [harg]
    ring
  simp_rw [hfun] at hle
  have hval : (∫ u in Set.Ioi (0 : ℝ), g u) = Real.sqrt Real.pi / (2 * x) := by
    rw [show g = (fun u : ℝ ↦ Real.exp (-(x ^ 2) * u ^ 2)) from rfl,
      integral_gaussian_Ioi, Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hx.le]
    ring
  exact hle.trans_eq hval

end SRWTightness
