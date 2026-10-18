import SRWTightness.MaximumPrinciple
import SRWTightness.RecordExitSlice
import SRWTightness.ExitPayoffRangeComparison

open MeasureTheory

namespace SRWTightness

/-- Harmonic comparison needs bounds only on the actual finite-domain exit boundary. -/
theorem harmonic_comparison_on_boundary (D : Finset Site) (f g : Site → ℝ)
    (hf : ∀ y ∈ D, f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d))
    (hg : ∀ y ∈ D, g y = (1 / 4 : ℝ) * ∑ d : Direction, g (y + step d))
    (hb : ∀ y ∈ domainExitBoundary D, f y ≤ g y) (x : Site) (hx : x ∈ D) :
    f x ≤ g x := by
  rw [harmonic_eq_exitPayoff D f hf x, harmonic_eq_exitPayoff D g hg x]
  apply integral_mono_ae (integrable_domainExit_payoff D x f)
    (integrable_domainExit_payoff D x g)
  filter_upwards [domainExitLocation_mem_boundary_ae D x hx] with ω hω
  exact hb _ hω

/-- The relative boundary error propagates without a lower bound on the interior harmonic weight. -/
theorem harmonic_relative_error_on_boundary (D : Finset Site) (f q : Site → ℝ)
    (hf : ∀ y ∈ D, f y = (1 / 4 : ℝ) * ∑ d : Direction, f (y + step d))
    (hq : ∀ y ∈ D, q y = (1 / 4 : ℝ) * ∑ d : Direction, q (y + step d))
    (α δ : ℝ) (hb : ∀ y ∈ domainExitBoundary D, |f y - α * q y| ≤ δ * q y)
    (x : Site) (hx : x ∈ D) : |f x - α * q x| ≤ δ * q x := by
  have hscale (c : ℝ) : ∀ y ∈ D,
      c * q y = (1 / 4 : ℝ) * ∑ d : Direction, c * q (y + step d) := by
    intro y hy
    rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 / 4 : ℝ) c, mul_assoc, ← hq y hy]
  have hlo : (α - δ) * q x ≤ f x := by
    apply harmonic_comparison_on_boundary D (fun y ↦ (α - δ) * q y) f
      (hscale _) hf _ x hx
    intro y hy
    have hh := (abs_le.mp (hb y hy)).1
    nlinarith
  have hhi : f x ≤ (α + δ) * q x := by
    apply harmonic_comparison_on_boundary D f (fun y ↦ (α + δ) * q y)
      hf (hscale _) _ x hx
    intro y hy
    have hh := (abs_le.mp (hb y hy)).2
    nlinarith
  apply abs_le.mpr
  constructor <;> nlinarith

end SRWTightness
