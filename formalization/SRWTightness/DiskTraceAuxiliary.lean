import SRWTightness.DiskTracePositiveRadii
import SRWTightness.TraceAuxiliaryBounds
import SRWTightness.DiskTraceErrorSmall

open MeasureTheory
namespace SRWTightness

/-- The actual disk comparison applies to every measurable trace test with independent auxiliary randomness. -/
theorem disk_trace_auxiliary_comparison (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ C Λ : ℝ, 0 < C ∧ 16 ≤ Λ ∧ ∀ a B : ℝ, 0 < a → Λ * a ≤ B →
      ∀ (b x e : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) → x ∈ K →
      e ∉ translateFinset b (diskFinset B) →
      0 < traceExitProbability (translateFinset b (diskFinset B)) x e →
      ∀ (Ξ : Type*) [MeasurableSpace Ξ] [MeasurableSpace (List Site)]
        (ν : Measure Ξ) [IsProbabilityMeasure ν] (s : Set (List Site × Ξ)), MeasurableSet s →
      let D := translateFinset b (diskFinset B)
      let ε := C * (a / B) * (1 + Real.log (B / a))
      let event := {p : Sample × Ξ | (killedVisitTrace D K x p.1, p.2) ∈ s}
      let joint := ((pathLaw.restrict {ω | domainExitLocation D x ω = e}).prod ν).real event
      (1 - ε) * (pathLaw.prod ν).real event ≤ joint / traceExitProbability D x e ∧
        joint / traceExitProbability D x e ≤ (1 + ε) * (pathLaw.prod ν).real event := by
  obtain ⟨C, Λ, hC, hΛ, hh⟩ := disk_trace_ratio_positive_radii hP hH hM hT
  obtain ⟨Λ₀, hΛ₀, hsmall⟩ := disk_trace_error_small C 1 (by norm_num)
  refine ⟨C, max Λ Λ₀, hC, hΛ.trans (le_max_left _ _), ?_⟩
  intro a B ha hB b x e K hK hx he hep Ξ _ _ ν _ s hs
  have hBbase : Λ * a ≤ B :=
    (mul_le_mul_of_nonneg_right (le_max_left Λ Λ₀) ha.le).trans hB
  have hBsmall : Λ₀ * a ≤ B :=
    (mul_le_mul_of_nonneg_right (le_max_right Λ Λ₀) ha.le).trans hB
  have hε1 := hsmall a B ha hBsmall
  have hB0 : 0 < B := by nlinarith [hBbase]
  have hab : a < B := by nlinarith [hBbase]
  have hlog : 0 ≤ Real.log (B / a) := (Real.log_pos ((one_lt_div ha).mpr hab)).le
  exact trace_auxiliary_conditional_event_bounds _ K x e ν _ (by positivity) hε1 hep
    (hh a B ha hBbase b x e K hK hx he hep) s hs

end SRWTightness
