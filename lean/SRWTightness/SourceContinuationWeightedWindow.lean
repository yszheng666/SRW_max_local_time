import SRWTightness.SourceContinuationScalarUpper
import SRWTightness.SourceContinuationWindowIntegral
import SRWTightness.SourceContinuationTerminalExponent

open Filter MeasureTheory
namespace SRWTightness

/-- A marked continuation window has a deficit-independent exponential majorant. -/
theorem source_continuation_weighted_window (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (ν L k : ℕ) (q a : ℝ) (P : GeometricGWRecord → ℝ) (S : Set GeometricGWRecord),
      ν ≤ 2 * sourceCoarseLowerLevel t →
      (ν : ℝ) + (L : ℝ) = (sourceCoarseGeneration t : ℝ) → 0 < k →
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
      Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν → 0 ≤ a →
      (∀ r, P r ∈ Set.Icc (0 : ℝ) 1) → S ⊆ sourceContinuationWindow t ν L q →
      (∀ r ∈ S,
        let d := sourceLowerTime (sourceLowerRadius t)
        let q' := sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - geometricGWHeight r L
        P r ≤ a * (Real.exp (-2 * d - 2 * q') / d)) →
      (∫ r in S, P r ∂geometricGWRecordLaw k L) ≤
        (C * a * ((ν : ℝ) + 1) * Real.sqrt (Real.sqrt (2 * (k : ℝ))) / t ^ 2 *
          Real.exp (-2 * sourceLowerTime (sourceLowerRadius t)) *
          Real.exp (-((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) -
            Real.sqrt (2 * (k : ℝ))) ^ 2 / (2 * (L : ℝ))))) *
          ((1 + q) / sourceLowerTime (sourceLowerRadius t)) := by
  obtain ⟨G, hG, hgw⟩ := source_continuation_scalar_upper hGW
  refine ⟨G * Real.exp 2 * Real.exp 1, by positivity, ?_⟩
  filter_upwards [hgw, source_continuation_terminal_exponent,
    eventually_ge_atTop (sourceScaleThreshold 4)] with t hgw he ht
  intro ν L k q a P S hν hN hk hq hq2 hx ha hP hS hpoint
  let d := sourceLowerTime (sourceLowerRadius t)
  let x := Real.sqrt (2 * (k : ℝ))
  let A := -((x - sourceTerminalRoot t q) ^ 2 / (2 * (L : ℝ)))
  let B := -((sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) - x) ^ 2 /
    (2 * (L : ℝ)))
  let W := ((ν : ℝ) + 1) * (1 + q) * Real.sqrt x / t ^ 2
  have hd : 0 < d := by dsimp [d]; linarith [sourceLowerTime_ge_one t ht]
  have hq0 : 0 ≤ q := (Real.sqrt_nonneg _).trans hq
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hexp : Real.exp A * Real.exp (-2 * d - 2 * q) ≤
      Real.exp 1 * Real.exp (-2 * d) * Real.exp B := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := he ν L x q hν hN (Real.sqrt_nonneg _) hq hq2
    change A - 2 * q ≤ B + 1 at hh
    linarith
  have hi := source_continuation_window_integral_upper t q a ν L k P S hd ha hP hS hpoint
  have hg : (geometricGWRecordLaw k L).real (sourceContinuationWindow t ν L q) ≤
      G * W * Real.exp A := by
    have hh := hgw q ν L k hν hN hk hq hq2 hx
    convert hh using 1 <;> dsimp [W, A, x] <;> ring
  calc
    _ ≤ (a * Real.exp 2 * (Real.exp (-2 * d - 2 * q) / d)) *
        (G * W * Real.exp A) :=
      hi.trans (mul_le_mul_of_nonneg_left hg (by positivity))
    _ = (G * a * Real.exp 2 * W / d) *
        (Real.exp A * Real.exp (-2 * d - 2 * q)) := by ring
    _ ≤ (G * a * Real.exp 2 * W / d) *
        (Real.exp 1 * Real.exp (-2 * d) * Real.exp B) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by dsimp [W, B, d, x]; ring

end SRWTightness
