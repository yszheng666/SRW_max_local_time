import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace SRWTightness

/-- A two-sided exponential comparison may be reversed with the same error. -/
theorem exponential_comparison_symm (p q E : ℝ)
    (h : Real.exp (-E) * p ≤ q ∧ q ≤ Real.exp E * p) :
    Real.exp (-E) * q ≤ p ∧ p ≤ Real.exp E * q := by
  constructor
  · have hh := mul_le_mul_of_nonneg_left h.2 (Real.exp_nonneg (-E))
    simpa only [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] using hh
  · have hh := mul_le_mul_of_nonneg_left h.1 (Real.exp_nonneg E)
    simpa only [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul] using hh

/-- Errors add when two-sided exponential comparisons are composed. -/
theorem exponential_comparison_trans (p q r E F : ℝ)
    (h : Real.exp (-E) * p ≤ q ∧ q ≤ Real.exp E * p)
    (k : Real.exp (-F) * q ≤ r ∧ r ≤ Real.exp F * q) :
    Real.exp (-(E + F)) * p ≤ r ∧ r ≤ Real.exp (E + F) * p := by
  constructor
  · have hh := (mul_le_mul_of_nonneg_left h.1 (Real.exp_nonneg (-F))).trans k.1
    simpa only [neg_add, Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using hh
  · have hh := k.2.trans (mul_le_mul_of_nonneg_left h.2 (Real.exp_nonneg F))
    simpa only [Real.exp_add, mul_assoc, mul_left_comm, mul_comm] using hh

end SRWTightness
