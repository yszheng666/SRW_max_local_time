import SRWTightness.SourceUpperTerminalRemainderDecay
import SRWTightness.SourceUpperBlockTotalCount
import SRWTightness.SourceUpperBlockRootGeometry

open Filter
open scoped Topology

namespace SRWTightness

/-- The terminal remainder summed over all spatial return scales decays exponentially. -/
theorem source_upper_spatial_remainder_decay (hScale : ExponentialFloorScaleInput)
    (K C ρ : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    ∀ᶠ t : ℝ in atTop,
      (∑ b ∈ sourceUpperBlockCenters t, ((sourceUpperBlockRoot t b : ℝ) + K) *
        sourceUpperTerminalRemainder t C ρ) ≤ 50 * C * Real.exp (-2 * t) := by
  have hK0 : 0 ≤ K := by linarith
  filter_upwards [source_upper_terminal_remainder_decay hScale C ρ hC hρ,
    source_upper_block_total_count, source_upper_block_root_conditions,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (K + 1)),
    eventually_gt_atTop (0 : ℝ)] with t he hc hk hl ht
  have hlog : Real.log t ≤ Real.exp t := by
    have h₁ := Real.log_le_sub_one_of_pos ht
    have h₂ := Real.add_one_le_exp t
    linarith
  have hp (b : Site) (hb : b ∈ sourceUpperBlockCenters t) :
      ((sourceUpperBlockRoot t b : ℝ) + K) * sourceUpperTerminalRemainder t C ρ ≤
        2 * Real.exp t * (C * Real.exp (-5 * t)) := by
    have hq0 : 0 ≤ (sourceUpperBlockRoot t b : ℝ) + K := by positivity
    have hq : (sourceUpperBlockRoot t b : ℝ) + K ≤ 2 * Real.exp t := by
      have := (hk b hb).2.1
      linarith
    exact (mul_le_mul_of_nonneg_left he hq0).trans
      (mul_le_mul_of_nonneg_right hq (by positivity))
  calc
    _ ≤ ∑ b ∈ sourceUpperBlockCenters t, 2 * Real.exp t * (C * Real.exp (-5 * t)) :=
      Finset.sum_le_sum hp
    _ = ((sourceUpperBlockCenters t).card : ℝ) *
        (2 * Real.exp t * (C * Real.exp (-5 * t))) := by simp
    _ ≤ (25 * (Real.exp t) ^ 2) * (2 * Real.exp t * (C * Real.exp (-5 * t))) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 50 * C * Real.exp (-2 * t) := by
      rw [show -2 * t = t + t + t + (-5 * t) by ring]
      simp only [Real.exp_add]
      ring

/-- The retained real spatial error vanishes for the actual block family. -/
theorem source_upper_spatial_remainder_vanishes (hScale : ExponentialFloorScaleInput)
    (K C ρ : ℝ) (hK : 1 ≤ K) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    Tendsto (fun t : ℝ ↦ ∑ b ∈ sourceUpperBlockCenters t,
      ((sourceUpperBlockRoot t b : ℝ) + K) * sourceUpperTerminalRemainder t C ρ)
      atTop (𝓝 0) := by
  have hK0 : 0 ≤ K := by linarith
  have hl : Tendsto (fun t : ℝ ↦ 50 * C * Real.exp (-2 * t)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [Function.comp_apply, id_eq, neg_mul, mul_zero] using hh.const_mul (50 * C)
  apply squeeze_zero' _ (source_upper_spatial_remainder_decay hScale K C ρ hK hC hρ) hl
  exact Filter.Eventually.of_forall (fun t ↦ Finset.sum_nonneg (fun b _ ↦ by
    unfold sourceUpperTerminalRemainder
    positivity))

/-- The exact ENNReal error appearing in the principal/error total tends to zero. -/
theorem source_upper_spatial_remainder_ennreal_vanishes
    (hScale : ExponentialFloorScaleInput) (K C ρ : ℝ)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    Tendsto (fun t : ℝ ↦ ∑ b ∈ sourceUpperBlockCenters t,
      ENNReal.ofReal (((sourceUpperBlockRoot t b : ℝ) + K) *
        sourceUpperTerminalRemainder t C ρ)) atTop (𝓝 0) := by
  have hK0 : 0 ≤ K := by linarith
  have hh := ENNReal.tendsto_ofReal
    (source_upper_spatial_remainder_vanishes hScale K C ρ hK hC hρ)
  simp only [ENNReal.ofReal_zero] at hh
  convert hh using 1
  funext t
  symm
  apply ENNReal.ofReal_sum_of_nonneg
  intro b hb
  unfold sourceUpperTerminalRemainder
  positivity

end SRWTightness
