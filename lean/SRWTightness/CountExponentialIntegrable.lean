import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory
namespace SRWTightness

/-- Two counts bounded by one duration have an integrable joint square-root exponential whenever
that duration has the indicated square-root exponential moment. -/
theorem joint_count_exponential_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y N : Ω → ℕ) (hX : Measurable X) (hY : Measurable Y)
    (hMoment : Integrable (fun ω ↦ Real.exp (8 * Real.sqrt ((N ω : ℝ) + 1))) μ)
    (hXN : ∀ᵐ ω ∂μ, X ω ≤ N ω + 1) (hYN : ∀ᵐ ω ∂μ, Y ω ≤ N ω + 1) :
    Integrable (fun ω ↦ Real.exp (2 * Real.sqrt (2 * (X ω : ℝ)) +
      2 * Real.sqrt (2 * (Y ω : ℝ)))) μ := by
  have hm : Measurable (fun ω ↦ Real.exp (2 * Real.sqrt (2 * (X ω : ℝ)) +
      2 * Real.sqrt (2 * (Y ω : ℝ)))) :=
    (measurable_of_countable (fun q : ℕ × ℕ ↦
      Real.exp (2 * Real.sqrt (2 * (q.1 : ℝ)) + 2 * Real.sqrt (2 * (q.2 : ℝ))))).comp
      (hX.prodMk hY)
  apply hMoment.mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ ↦ (Real.exp_pos _).le))
  filter_upwards [hXN, hYN] with ω h₀ h₁
  apply Real.exp_le_exp.mpr
  have hc₀ : (X ω : ℝ) ≤ (N ω : ℝ) + 1 := by exact_mod_cast h₀
  have hc₁ : (Y ω : ℝ) ≤ (N ω : ℝ) + 1 := by exact_mod_cast h₁
  have hs := Real.sq_sqrt (show 0 ≤ (N ω : ℝ) + 1 by positivity)
  have hsq (k : ℕ) (hk : (k : ℝ) ≤ (N ω : ℝ) + 1) :
      Real.sqrt (2 * (k : ℝ)) ≤ 2 * Real.sqrt ((N ω : ℝ) + 1) := by
    apply (Real.sqrt_le_left (by positivity)).2
    nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  linarith [hsq _ hc₀, hsq _ hc₁]

end SRWTightness
