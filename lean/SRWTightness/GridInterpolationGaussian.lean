import SRWTightness.GridInterpolationCovariance
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The entire interpolated process is Gaussian when the finite node vector is Gaussian. -/
theorem timeGridInterpolation_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : ℕ → ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (hX : HasGaussianLaw (fun ω (j : Fin (n + 1)) ↦ X j ω) μ) :
    IsGaussianProcess (fun v ω ↦ timeGridInterpolation T (fun j ↦ X j ω) n v) μ where
  hasGaussianLaw I := by
    classical
    let L : (Fin (n + 1) → ℝ) →L[ℝ] (I → ℝ) :=
      { toFun x v := x 0 + ∑ j : Fin n,
          timeGridRamp (T j) (T (j + 1)) v * (x j.succ - x j.castSucc)
        map_add' x y := by
          ext v
          simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          ring
        map_smul' c x := by
          ext v
          simp [mul_sub, mul_add, Finset.mul_sum, mul_assoc, mul_left_comm] }
    have he : (fun ω ↦ I.restrict (fun v ↦ timeGridInterpolation T (fun j ↦ X j ω) n v)) =
        L ∘ (fun ω (j : Fin (n + 1)) ↦ X j ω) := by
      ext ω v
      simp only [Function.comp_apply, L, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
        AddHom.coe_mk, Finset.restrict_def, timeGridInterpolation, Fin.val_zero,
        Fin.val_succ, Fin.val_castSucc]
      rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
        timeGridRamp (T j) (T (j + 1)) v * (X (j + 1) ω - X j ω)) n]
    rw [he]
    exact hX.map L

end SRWTightness
