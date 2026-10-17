import SRWTightness.SourceUpperDepthInternal
import SRWTightness.DiskDiagonalFineAsymptotic

open Filter
open scoped Topology
namespace SRWTightness

/-- Removing one lattice unit from an exponential radius has a vanishing logarithmic error. -/
theorem log_exponential_radius_error :
    Tendsto (fun u : ℝ ↦ Real.log (Real.exp (u + 1) - 1) - (u + 1)) atTop (𝓝 0) := by
  have he : Tendsto (fun u : ℝ ↦ Real.exp (u + 1)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id)
  have hi := (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).comp he
  have hf : Tendsto (fun u : ℝ ↦ 1 - (Real.exp (u + 1))⁻¹) atTop (𝓝 1) := by
    simpa only [sub_zero, Function.comp_def] using tendsto_const_nhds.sub hi
  have hl : Tendsto (fun u : ℝ ↦ Real.log (1 - (Real.exp (u + 1))⁻¹))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hf
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  have hbig : 1 < Real.exp (u + 1) := Real.one_lt_exp_iff.mpr (by linarith)
  have hinv : (Real.exp (u + 1))⁻¹ < 1 := by
    rw [inv_eq_one_div]
    exact (div_lt_one (Real.exp_pos _)).mpr hbig
  have hfactor : 0 < 1 - (Real.exp (u + 1))⁻¹ := by linarith
  have heq : Real.exp (u + 1) - 1 =
      Real.exp (u + 1) * (1 - (Real.exp (u + 1))⁻¹) := by
    rw [mul_sub, mul_one, mul_inv_cancel₀ (Real.exp_ne_zero _)]
  rw [heq, Real.log_mul (Real.exp_ne_zero _) hfactor.ne', Real.log_exp]
  ring

/-- The actual reference radius grows without bound along the source upper logarithmic scale. -/
theorem source_upper_reference_radius_tendsto :
    Tendsto (fun t : ℝ ↦ upperTerminalRadius (sourceUpperLogRadius t)) atTop atTop := by
  have hh := Real.tendsto_exp_atTop.comp
    (tendsto_atTop_add_const_right atTop (1 : ℝ) sourceUpperLogRadius_tendsto)
  simpa only [upperTerminalRadius, sub_eq_add_neg, Function.comp_def] using
    tendsto_atTop_add_const_right atTop (-1 : ℝ) hh

/-- The same fine-potential constant gives the full little-o expansion of actual Green depth. -/
theorem source_upper_depth_fine_expansion (hinput : PotentialKernelAsymptoticInput) :
    ∃ κ : ℝ, Tendsto (fun t : ℝ ↦ upperTerminalDepth (sourceUpperLogRadius t) -
      (sourceUpperLogRadius t + 1 + κ / (2 / Real.pi))) atTop (𝓝 0) := by
  obtain ⟨κ, B, R₁, hB, hR₁, hb, hlim⟩ := diskGreen_fine_asymptotic hinput
  have hg := (hlim.comp source_upper_reference_radius_tendsto).div_const (2 / Real.pi)
  have hl := log_exponential_radius_error.comp sourceUpperLogRadius_tendsto
  refine ⟨κ, ?_⟩
  have hh := hg.add hl
  convert hh using 1
  · funext t
    dsimp [upperTerminalDepth, upperTerminalRadius, Function.comp_def]
    field_simp
    <;> ring
  · simp

end SRWTightness
