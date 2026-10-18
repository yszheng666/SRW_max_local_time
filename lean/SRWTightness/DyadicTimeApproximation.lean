import SRWTightness.GaussianSeriesContinuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

noncomputable def dyadicTimeIndex (n : ℕ) (t : ℝ) : ℕ := ⌊(2 : ℝ) ^ n * t⌋₊

noncomputable def dyadicTime (n : ℕ) (t : ℝ) : ℝ :=
  (dyadicTimeIndex n t : ℝ) / (2 : ℝ) ^ n

theorem dyadicTime_bounds (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ dyadicTime n t ∧ dyadicTime n t ≤ t ∧ t - dyadicTime n t ≤ ((2 : ℝ) ^ n)⁻¹ := by
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have hlow := Nat.floor_le (show 0 ≤ (2 : ℝ) ^ n * t by positivity)
  have hu := Nat.lt_floor_add_one ((2 : ℝ) ^ n * t)
  refine ⟨by unfold dyadicTime; positivity, ?_, ?_⟩
  · exact (div_le_iff₀ hp).mpr (by simpa [dyadicTimeIndex, mul_comm] using hlow)
  · unfold dyadicTime dyadicTimeIndex
    rw [inv_eq_one_div, le_div_iff₀ hp]
    have he : (t - (⌊(2 : ℝ) ^ n * t⌋₊ : ℝ) / (2 : ℝ) ^ n) * (2 : ℝ) ^ n =
        t * (2 : ℝ) ^ n - (⌊(2 : ℝ) ^ n * t⌋₊ : ℝ) := by field_simp
    rw [he]
    nlinarith

theorem dyadicTimeIndex_le (n : ℕ) (t : ℝ) (ht : t ≤ 1) :
    dyadicTimeIndex n t ≤ 2 ^ n := by
  unfold dyadicTimeIndex
  apply Nat.floor_le_of_le
  push_cast
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

theorem dyadicTime_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n ↦ dyadicTime n t) atTop (nhds t) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hpow : Tendsto (fun n : ℕ ↦ ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  apply squeeze_zero (fun _ ↦ dist_nonneg) _ hpow
  intro n
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (dyadicTime_bounds n t ht).2.1)]
  linarith [(dyadicTime_bounds n t ht).2.2]

theorem gaussianDyadicPath_ae_dyadic_limit :
    ∀ᵐ ω ∂gaussianCoefficientLaw, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun n ↦ gaussianDyadicPath ω (dyadicTime n t)) atTop
        (nhds (gaussianDyadicPath ω t)) := by
  filter_upwards [gaussianDyadicPath_ae_continuous] with ω hω
  intro t ht
  exact (hω.tendsto t).comp (dyadicTime_tendsto t ht)

theorem gaussianDyadicPath_ae_vector_limit {ι : Type*} (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∀ᵐ ω ∂gaussianCoefficientLaw,
      Tendsto (fun n i ↦ gaussianDyadicPath ω (dyadicTime n (t i))) atTop
        (nhds (fun i ↦ gaussianDyadicPath ω (t i))) := by
  filter_upwards [gaussianDyadicPath_ae_dyadic_limit] with ω hω
  exact tendsto_pi_nhds.mpr (fun i ↦ hω (t i) (ht i))

end SRWTightness
