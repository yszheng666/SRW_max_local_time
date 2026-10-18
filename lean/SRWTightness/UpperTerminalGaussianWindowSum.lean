import SRWTightness.UpperTerminalGaussianWindow
import Mathlib.Analysis.SumIntegralComparisons

open Set MeasureTheory

namespace SRWTightness

/-- Every finitely truncated nonnegative shifted unit-window Gaussian sum is uniformly bounded. -/
theorem upper_terminal_gaussian_window_sum (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℝ, 1 ≤ d → ∀ v : ℝ, 0 ≤ v → v ≤ 1 → ∀ M : ℕ,
      (∑ J ∈ Finset.range M, upperTerminalGaussianKernel d c ((J : ℝ) + v)) ≤ C := by
  obtain ⟨C, hC, hIntegral⟩ := upper_terminal_gaussian_integral (c / 2) (by positivity)
  refine ⟨3 * Real.exp c * C, by positivity, ?_⟩
  intro d hd v hv hv1 M
  let g := fun x : ℝ ↦ (3 * Real.exp c) * upperTerminalGaussianKernel d (c / 2) x
  have hg : Continuous g := by
    dsimp [g, upperTerminalGaussianKernel]
    fun_prop
  have hh := sum_Ico_le_integral_of_le (a := 0) (b := M) (Nat.zero_le M)
    (f := fun x : ℝ ↦ upperTerminalGaussianKernel d c (x + v)) (g := g)
    (fun J _ x hx ↦ by
      have hx' : x ∈ Ico (J : ℝ) ((J : ℝ) + 1) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hx
      exact upper_terminal_gaussian_window d c (J + v) x hd hc
        (by positivity) (by linarith [hx'.1, Nat.cast_nonneg (α := ℝ) J])
        (abs_le.mpr ⟨by linarith [hx'.2], by linarith [hx'.1]⟩))
    (hg.integrableOn_Icc.mono_set Ico_subset_Icc_self)
  simp only [Nat.Ico_zero_eq_range, Nat.cast_zero, g,
    intervalIntegral.integral_const_mul] at hh
  obtain ⟨hI, hbound⟩ := hIntegral d (by linarith)
  have hf : (∫ x in (0 : ℝ)..(M : ℝ), upperTerminalGaussianKernel d (c / 2) x) ≤
      ∫ x : ℝ, upperTerminalGaussianKernel d (c / 2) x := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg M)]
    exact setIntegral_le_integral hI (ae_of_all _ (fun x ↦ by
      unfold upperTerminalGaussianKernel
      positivity))
  exact hh.trans (mul_le_mul_of_nonneg_left (hf.trans hbound) (by positivity))

end SRWTightness
