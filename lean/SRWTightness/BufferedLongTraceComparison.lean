import SRWTightness.BufferedLongTraceGeometry
import SRWTightness.DiskTraceAuxiliary
import SRWTightness.RelativeProbabilityExponential

open MeasureTheory
namespace SRWTightness

/-- Prescribing a long exit costs only an exponentially small factor for any retained-trace test. -/
theorem buffered_long_trace_comparison (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ C J₀ : ℝ, 0 < C ∧ 1 ≤ J₀ ∧ ∀ ρ H J : ℝ,
      2 ≤ ρ → 0 ≤ H → H ≤ ρ → J₀ ≤ J →
      ∀ (b x e : Site) (K : Finset Site),
      K ⊆ translateFinset b (diskFinset (Real.exp 1 * ρ + H + 2)) → x ∈ K →
      e ∉ translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)) →
      0 < traceExitProbability
        (translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))) x e →
      ∀ (Ξ : Type*) [MeasurableSpace Ξ] [MeasurableSpace (List Site)]
        (ν : Measure Ξ) [IsProbabilityMeasure ν] (s : Set (List Site × Ξ)), MeasurableSet s →
      let D := translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))
      let δ := C * (J + 1) * Real.exp (-J)
      let event := {p : Sample × Ξ | (killedVisitTrace D K x p.1, p.2) ∈ s}
      let joint := ((pathLaw.restrict {ω | domainExitLocation D x ω = e}).prod ν).real event
      Real.exp (-δ) * (pathLaw.prod ν).real event ≤ joint / traceExitProbability D x e ∧
        joint / traceExitProbability D x e ≤ Real.exp δ * (pathLaw.prod ν).real event := by
  obtain ⟨C, Λ, hC, hΛ, hh⟩ := disk_trace_auxiliary_comparison hP hH hM hT
  obtain ⟨Λ₁, hΛ₁, hsmall⟩ := disk_trace_error_small C (1 / 2) (by norm_num)
  let L := max Λ Λ₁
  have hL : 16 ≤ L := hΛ.trans (le_max_left _ _)
  have hL0 : 0 < L := by linarith
  refine ⟨4 * C * Real.exp 1, max 1 (Real.log L + 1), by positivity,
    le_max_left _ _, ?_⟩
  intro ρ H J hρ hH hHρ hJ b x e K hK hx he hep Ξ _ _ ν _ s hs
  let a := Real.exp 1 * ρ + H + 2
  let B := Real.exp (J + 1) * ρ + H
  have hJ1 : 1 ≤ J := (le_max_left _ _).trans hJ
  obtain ⟨ha, hB, hsep, herr⟩ := buffered_long_trace_geometry ρ H J hρ hH hHρ hJ1
  have hLexp : L ≤ Real.exp (J - 1) := by
    have hlog : Real.log L ≤ J - 1 := by
      have := (le_max_right 1 (Real.log L + 1)).trans hJ
      linarith
    simpa only [Real.exp_log hL0] using Real.exp_le_exp.mpr hlog
  have hLB : L * a ≤ B :=
    (mul_le_mul_of_nonneg_right hLexp ha.le).trans hsep
  have hΛB : Λ * a ≤ B :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) ha.le).trans hLB
  have hΛ₁B : Λ₁ * a ≤ B :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) ha.le).trans hLB
  let ε := C * (a / B) * (1 + Real.log (B / a))
  have hab : a < B := by nlinarith [hΛB]
  have hlog : 0 ≤ Real.log (B / a) := (Real.log_pos ((one_lt_div ha).mpr hab)).le
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hεsmall : ε ≤ 1 / 2 := hsmall a B ha hΛ₁B
  have hcomp := hh a B ha hΛB b x e K hK hx he hep Ξ ν s hs
  dsimp only at hcomp ⊢
  let q := (pathLaw.prod ν).real
    {p : Sample × Ξ | (killedVisitTrace (translateFinset b (diskFinset B)) K x p.1, p.2) ∈ s}
  have hq : 0 ≤ q := measureReal_nonneg
  have hr := relative_probability_exponential _ q ε hq hε hεsmall (by
    apply abs_le.mpr
    change (1 - ε) * q ≤ _ ∧ _ ≤ (1 + ε) * q at hcomp
    constructor <;> nlinarith [hcomp.1, hcomp.2])
  have hδ : 2 * ε ≤ (4 * C * Real.exp 1) * (J + 1) * Real.exp (-J) := by
    have hmul := mul_le_mul_of_nonneg_left herr (show 0 ≤ 2 * C by positivity)
    dsimp [ε, a, B]
    nlinarith [hmul]
  constructor
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hq).trans hr.1
  · exact hr.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hδ) hq)

end SRWTightness
