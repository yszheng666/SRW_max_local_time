import SRWTightness.SchauderTent
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- Covariance kernel of the bridge pinned at the endpoints of the unit interval. -/
noncomputable def unitBridgeKernel (s t : ℝ) : ℝ := min s t - s * t

theorem unitBridgeKernel_symm (s t : ℝ) : unitBridgeKernel s t = unitBridgeKernel t s := by
  simp [unitBridgeKernel, min_comm, mul_comm]

theorem schauderTent_left_half (s : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2) :
    schauderTent s = s := by
  rw [schauderTent, min_eq_left (by linarith), max_eq_right hs]

theorem schauderTent_right_half (s : ℝ) (hs : 1 / 2 ≤ s) (hs' : s ≤ 1) :
    schauderTent s = 1 - s := by
  rw [schauderTent, min_eq_right (by linarith), max_eq_right (by linarith)]

theorem unitBridgeKernel_left (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    unitBridgeKernel s t = schauderTent s * schauderTent t +
      unitBridgeKernel (2 * s) (2 * t) / 2 := by
  rw [schauderTent_left_half s hs hs', schauderTent_left_half t ht ht']
  unfold unitBridgeKernel
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : 2 * s ≤ 2 * t)]
    ring
  · rw [min_eq_right h, min_eq_right (by linarith : 2 * t ≤ 2 * s)]
    ring

theorem unitBridgeKernel_right (s t : ℝ) (hs : 1 / 2 ≤ s) (hs' : s ≤ 1)
    (ht : 1 / 2 ≤ t) (ht' : t ≤ 1) :
    unitBridgeKernel s t = schauderTent s * schauderTent t +
      unitBridgeKernel (2 * s - 1) (2 * t - 1) / 2 := by
  rw [schauderTent_right_half s hs hs', schauderTent_right_half t ht ht']
  unfold unitBridgeKernel
  rcases le_total s t with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : 2 * s - 1 ≤ 2 * t - 1)]
    ring
  · rw [min_eq_right h, min_eq_right (by linarith : 2 * t - 1 ≤ 2 * s - 1)]
    ring

theorem unitBridgeKernel_cross (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1 / 2)
    (ht : 1 / 2 ≤ t) (ht' : t ≤ 1) :
    unitBridgeKernel s t = schauderTent s * schauderTent t := by
  rw [schauderTent_left_half s hs hs', schauderTent_right_half t ht ht']
  rw [unitBridgeKernel, min_eq_left (by linarith)]
  ring

theorem unitBridgeKernel_bound (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) : |unitBridgeKernel s t| ≤ 1 / 4 := by
  rw [abs_le]
  unfold unitBridgeKernel
  rcases le_total s t with h | h
  · rw [min_eq_left h]
    constructor <;> nlinarith [mul_nonneg hs (sub_nonneg.mpr ht'),
      mul_nonneg hs (sub_nonneg.mpr h), sq_nonneg (s - 1 / 2)]
  · rw [min_eq_right h]
    constructor <;> nlinarith [mul_nonneg ht (sub_nonneg.mpr hs'),
      mul_nonneg ht (sub_nonneg.mpr h), sq_nonneg (t - 1 / 2)]

theorem unitBridgeKernel_split (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    unitBridgeKernel s t = schauderTent s * schauderTent t +
      (if s ≤ 1 / 2 ∧ t ≤ 1 / 2 then unitBridgeKernel (2 * s) (2 * t) / 2
       else if 1 / 2 ≤ s ∧ 1 / 2 ≤ t then
         unitBridgeKernel (2 * s - 1) (2 * t - 1) / 2 else 0) := by
  split_ifs with hl hr
  · exact unitBridgeKernel_left s t hs hl.1 ht hl.2
  · exact unitBridgeKernel_right s t hr.1 hs' hr.2 ht'
  · rw [add_zero]
    by_cases h : s ≤ 1 / 2
    · exact unitBridgeKernel_cross s t hs h (by grind) ht'
    · rw [unitBridgeKernel_symm, mul_comm]
      exact unitBridgeKernel_cross t s ht (by grind) (by linarith) hs'

/-- The recursive finite-depth covariance expansion. -/
noncomputable def bridgeKernelApprox : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | n + 1, s, t => schauderTent s * schauderTent t +
      (if s ≤ 1 / 2 ∧ t ≤ 1 / 2 then bridgeKernelApprox n (2 * s) (2 * t) / 2
       else if 1 / 2 ≤ s ∧ 1 / 2 ≤ t then
         bridgeKernelApprox n (2 * s - 1) (2 * t - 1) / 2 else 0)

theorem bridgeKernelApprox_error (n : ℕ) (s t : ℝ) (hs : 0 ≤ s) (hs' : s ≤ 1)
    (ht : 0 ≤ t) (ht' : t ≤ 1) :
    |unitBridgeKernel s t - bridgeKernelApprox n s t| ≤ (1 / 2 : ℝ) ^ n / 4 := by
  induction n generalizing s t with
  | zero => simpa [bridgeKernelApprox] using unitBridgeKernel_bound s t hs hs' ht ht'
  | succ n ih =>
    rw [bridgeKernelApprox, unitBridgeKernel_split s t hs hs' ht ht']
    split_ifs with hl hr
    · simp only [add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      calc
        _ ≤ ((1 / 2 : ℝ) ^ n / 4) / 2 :=
          div_le_div_of_nonneg_right
            (ih (2 * s) (2 * t) (by linarith) (by linarith [hl.1])
              (by linarith) (by linarith [hl.2])) (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) / 4 := by rw [pow_succ]; ring
    · simp only [add_sub_add_left_eq_sub, ← sub_div, abs_div, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      calc
        _ ≤ ((1 / 2 : ℝ) ^ n / 4) / 2 :=
          div_le_div_of_nonneg_right
            (ih (2 * s - 1) (2 * t - 1) (by linarith [hr.1]) (by linarith)
              (by linarith [hr.2]) (by linarith)) (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) / 4 := by rw [pow_succ]; ring
    · simp only [sub_self, abs_zero]
      positivity

end SRWTightness
