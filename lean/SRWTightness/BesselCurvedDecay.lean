import SRWTightness.BesselCurvedCrossing
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A finite dyadic cover always exists; its size does not enter the resulting bound. -/
theorem besselCurvedCrossing_uniform (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C)
    (T x H γ : ℝ) (hT : 0 < T) (hx : 0 < x) (hH : 0 < H)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    (independentBridgeLaw (Fin 3)).real (besselCurvedCrossing T x H γ 0 T) ≤
      (2 * H) ^ γ / x +
        C * (((3 : ℝ) ^ γ * H ^ (γ - 1 / 2)) / (1 - (2 : ℝ) ^ (γ - 1 / 2))) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (T / H)
  have hp : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast n.lt_two_pow_self
  exact besselCurvedCrossing_bound hInitial hHit C hMoment T x H γ hT hx hH hγ hγhalf n
    ((div_lt_iff₀ hH).mp (hn.trans hp)).le

/-- For starting height at least sqrt(H), the crossing cost has the required negative power. -/
theorem besselCurvedCrossing_power_decay (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C)
    (T x H γ : ℝ) (hT : 0 < T) (hH : 0 < H) (hx : Real.sqrt H ≤ x)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    (independentBridgeLaw (Fin 3)).real (besselCurvedCrossing T x H γ 0 T) ≤
      ((2 : ℝ) ^ γ + C * (3 : ℝ) ^ γ / (1 - (2 : ℝ) ^ (γ - 1 / 2))) *
        H ^ (γ - 1 / 2) := by
  have hs : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hi : (2 * H) ^ γ / x ≤ (2 : ℝ) ^ γ * H ^ (γ - 1 / 2) := by
    calc
      _ ≤ (2 * H) ^ γ / Real.sqrt H :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _) hs hx
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hH.le,
          Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hH]
  have hb := besselCurvedCrossing_uniform hInitial hHit C hMoment T x H γ
    hT (hs.trans_le hx) hH hγ hγhalf
  calc
    _ ≤ (2 : ℝ) ^ γ * H ^ (γ - 1 / 2) +
        C * (((3 : ℝ) ^ γ * H ^ (γ - 1 / 2)) / (1 - (2 : ℝ) ^ (γ - 1 / 2))) :=
      hb.trans (add_le_add hi le_rfl)
    _ = _ := by ring

end SRWTightness
