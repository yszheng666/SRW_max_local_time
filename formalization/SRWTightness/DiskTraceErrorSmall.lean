import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology
namespace SRWTightness

/-- Increasing the separation threshold makes the disk trace error uniformly small. -/
theorem disk_trace_error_small (C ε : ℝ) (hε : 0 < ε) :
    ∃ Λ : ℝ, 16 ≤ Λ ∧ ∀ a B : ℝ, 0 < a → Λ * a ≤ B →
      C * (a / B) * (1 + Real.log (B / a)) ≤ ε := by
  have h0 : Tendsto (fun r : ℝ ↦ 1 / r) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  have h1 : Tendsto (fun r : ℝ ↦ Real.log r / r) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hh : Tendsto (fun r : ℝ ↦ C * (1 / r + Real.log r / r)) atTop (𝓝 0) := by
    simpa using (h0.add h1).const_mul C
  obtain ⟨T, hT⟩ := eventually_atTop.1 ((tendsto_order.1 hh).2 ε hε)
  refine ⟨max 16 T, le_max_left _ _, ?_⟩
  intro a B ha hB
  have hΛ : 16 ≤ max 16 T := le_max_left _ _
  have hB0 : 0 < B := by nlinarith
  have hr : T ≤ B / a := (le_max_right 16 T).trans ((le_div_iff₀ ha).mpr hB)
  have hinv : a / B = 1 / (B / a) := by field_simp
  calc
    C * (a / B) * (1 + Real.log (B / a)) =
        C * (1 / (B / a) + Real.log (B / a) / (B / a)) := by rw [hinv]; ring
    _ ≤ ε := (hT (B / a) hr).le

end SRWTightness
