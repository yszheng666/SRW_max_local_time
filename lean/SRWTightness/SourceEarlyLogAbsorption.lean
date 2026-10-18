import SRWTightness.LogPowerDomination
import SRWTightness.SourceEarlyDistanceLevels

open Filter
namespace SRWTightness

/-- The precise ceiling gap has a uniform affine-logarithmic upper envelope. -/
theorem sourceEarlyDistanceGap_log_upper (a J₀ : ℕ) :
    (sourceEarlyDistanceGap a J₀ : ℝ) + 1 ≤
      20 * Real.log ((a : ℝ) + 2) + (J₀ : ℝ) + 2 := by
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 20 * Real.log ((a : ℝ) + 2) by
    apply mul_nonneg (by norm_num)
    exact Real.log_nonneg (by have ha := Nat.cast_nonneg (α := ℝ) a; linarith))
  simp only [sourceEarlyDistanceGap, Nat.cast_add]
  linarith only [hh]

/-- Polynomial prefactors and the fixed logarithmic-gap error fit inside one barrier deficit. -/
theorem source_early_log_prefactor_absorption (K C : ℝ) (hK : 0 < K) (hC : 0 ≤ C)
    (J₀ : ℕ) :
    ∃ a₀ : ℕ, 2 ≤ a₀ ∧ ∀ a ≥ a₀,
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      K * ((ν : ℝ) + 1) ^ 3 * (j : ℝ) ^ 2 * Real.exp (C * ((J : ℝ) + 1)) ≤
        Real.exp ((j : ℝ) ^ (2 / 5 : ℝ)) := by
  obtain ⟨ag, hag, hg⟩ := source_early_distance_gap_small J₀
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (affine_log_eventually_le_rpow (5 + 20 * C)
      (Real.log K + 3 * Real.log 3 + C * ((J₀ : ℝ) + 2)) (1 / 4) (2 / 5)
        (by norm_num) (by norm_num))
  let a₀ := max ag (max 2 ⌈T⌉₊)
  refine ⟨a₀, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro a ha
  dsimp only
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  have hag' : ag ≤ a := (le_max_left _ _).trans ha
  have ha2 : 2 ≤ a := (le_max_left _ _).trans ((le_max_right _ _).trans ha)
  have haT : ⌈T⌉₊ ≤ a := (le_max_right _ _).trans ((le_max_right _ _).trans ha)
  have har : (2 : ℝ) ≤ a := by exact_mod_cast ha2
  have hJ := hg a hag'
  have hJa : J ≤ a := by dsimp only [J]; omega
  have hj : 1 ≤ j := by dsimp only [j, J]; omega
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hJr : 2 * (J : ℝ) ≤ a := by exact_mod_cast hJ
  have hjhalf : (a : ℝ) / 2 ≤ (j : ℝ) := by
    dsimp only [j]
    rw [Nat.cast_sub hJa]
    linarith only [hJr]
  have hx : 0 < (a : ℝ) + 2 := by positivity
  have ht : T ≤ (a : ℝ) + 2 := by
    have hh := (Nat.le_ceil T).trans (Nat.cast_le.mpr haT : (⌈T⌉₊ : ℝ) ≤ a)
    linarith only [hh]
  have hbudget := hT ((a : ℝ) + 2) ht
  have hpower : ((a : ℝ) + 2) ^ (2 / 5 : ℝ) ≤ 4 * (j : ℝ) ^ (2 / 5 : ℝ) := by
    have hp := Real.rpow_le_rpow hx.le
      (show (a : ℝ) + 2 ≤ 4 * (j : ℝ) by linarith only [har, hjhalf])
      (by norm_num : (0 : ℝ) ≤ 2 / 5)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg j)] at hp
    have h4 := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : (2 / 5 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h4
    exact hp.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg (Nat.cast_nonneg j) _))
  have hν : (ν : ℝ) + 1 ≤ 3 * ((a : ℝ) + 2) := by
    dsimp only [ν]
    push_cast
    linarith only [hJr, har]
  have hνpos : 0 < (ν : ℝ) + 1 := by positivity
  have hlogν := Real.log_le_log hνpos hν
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hx.ne'] at hlogν
  have hjup : (j : ℝ) ≤ (a : ℝ) + 2 := by
    have hh : j ≤ a := Nat.sub_le _ _
    have hh' : (j : ℝ) ≤ a := by exact_mod_cast hh
    linarith only [hh']
  have hlogj := Real.log_le_log (by linarith only [hjr] : 0 < (j : ℝ)) hjup
  have hgap := mul_le_mul_of_nonneg_left (sourceEarlyDistanceGap_log_upper a J₀) hC
  have hexp : Real.log K + 3 * Real.log ((ν : ℝ) + 1) + 2 * Real.log (j : ℝ) +
      C * ((J : ℝ) + 1) ≤ (j : ℝ) ^ (2 / 5 : ℝ) := by
    change C * ((J : ℝ) + 1) ≤
      C * (20 * Real.log ((a : ℝ) + 2) + (J₀ : ℝ) + 2) at hgap
    nlinarith only [hlogν, hlogj, hgap, hbudget, hpower]
  calc
    _ = Real.exp (Real.log K + 3 * Real.log ((ν : ℝ) + 1) +
        2 * Real.log (j : ℝ) + C * ((J : ℝ) + 1)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hK,
        show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul,
        show (2 : ℝ) = (2 : ℕ) by norm_num, Real.exp_nat_mul,
        Real.exp_log hνpos, Real.exp_log (by linarith only [hjr] : 0 < (j : ℝ))]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

end SRWTightness
