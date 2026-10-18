import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open MeasureTheory Matrix
open scoped ENNReal

namespace SRWTightness

/-- Transport a density through a measurable map with a measurable left inverse. -/
theorem map_withDensity_leftInverse {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (g : β → α) (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) (ρ : α → ℝ≥0∞) (hρ : Measurable ρ) :
    (μ.withDensity ρ).map f = (μ.map f).withDensity (fun y ↦ ρ (g y)) := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs (show Measurable (fun y ↦ ρ (g y)) from hρ.comp hg) hf]
  apply setLIntegral_congr_fun (hf hs)
  intro x hx
  exact (congrArg ρ (hgf x)).symm

theorem matrix_map_withDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : IsUnit M) (ρ : (ι → ℝ) → ℝ≥0∞) (hρ : Measurable ρ) :
    ((volume : Measure (ι → ℝ)).withDensity ρ).map (fun x ↦ M *ᵥ x) =
      volume.withDensity (fun y ↦ ENNReal.ofReal (abs M.det⁻¹) * ρ (M⁻¹ *ᵥ y)) := by
  have hf : Measurable (fun x : ι → ℝ ↦ M *ᵥ x) := by fun_prop
  have hg : Measurable (fun x : ι → ℝ ↦ M⁻¹ *ᵥ x) := by fun_prop
  have hi : Function.LeftInverse (fun x ↦ M⁻¹ *ᵥ x) (fun x ↦ M *ᵥ x) := by
    intro x
    change M⁻¹ *ᵥ (M *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M ((Matrix.isUnit_iff_isUnit_det M).mp hM),
      Matrix.one_mulVec]
  rw [map_withDensity_leftInverse volume _ _ hf hg hi ρ hρ]
  have hv : (volume : Measure (ι → ℝ)).map (fun x ↦ M *ᵥ x) =
      ENNReal.ofReal (abs M.det⁻¹) • volume :=
    Real.map_matrix_volume_pi_eq_smul_volume_pi
      (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hM))
  rw [hv, withDensity_smul_measure]
  exact (withDensity_smul (μ := volume) (ENNReal.ofReal (abs M.det⁻¹)) (hρ.comp hg)).symm

end SRWTightness
