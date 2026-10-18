import SRWTightness.DiskTraceStopRelative
import SRWTightness.KilledTraceSupport

namespace SRWTightness

/-- Uniform actual trace comparison in the large-inner-radius disk regime used by the source. -/
theorem disk_trace_ratio (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ C Λ T : ℝ, 0 < C ∧ 16 ≤ Λ ∧ 2 ≤ T ∧ ∀ a B : ℝ, T ≤ a → Λ * a ≤ B →
      ∀ (b x e : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) → x ∈ K →
      e ∉ translateFinset b (diskFinset B) →
      0 < traceExitProbability (translateFinset b (diskFinset B)) x e → ∀ ξ : List Site,
      0 < pathLaw.real {ω | killedVisitTrace (translateFinset b (diskFinset B)) K x ω = ξ} →
      let D := translateFinset b (diskFinset B)
      |(pathLaw.real {ω | killedVisitTrace D K x ω = ξ ∧ domainExitLocation D x ω = e} /
        traceExitProbability D x e) / pathLaw.real {ω | killedVisitTrace D K x ω = ξ} - 1| ≤
        C * (a / B) * (1 + Real.log (B / a)) := by
  obtain ⟨G, T, hG, hT0, hg⟩ := disk_trace_stop_relative hP hH hM
  obtain ⟨H, hH0, hh⟩ := hH
  refine ⟨2 * (G + H), 16 + 2 * H, T, by positivity, by linarith, hT0, ?_⟩
  intro a B ha hB b x e K hK hx he hep ξ hξ
  let D := translateFinset b (diskFinset B)
  let s := traceExitProbability D b e
  let ε := G * (a / B) * Real.log (B / a)
  let δ := H * (a / B)
  have ha2 : 2 ≤ a := hT0.trans ha
  have ha0 : 0 < a := by linarith
  have hHa : 0 ≤ H * a := mul_nonneg hH0.le ha0.le
  have hsep : 16 * a ≤ B := by nlinarith
  have hB0 : 0 < B := by linarith
  have hab : a < B := by linarith
  have hKD : K ⊆ D := hK.trans
    (Finset.image_subset_image (diskFinset_mono a B ha0.le hab.le))
  have hlog : 0 ≤ Real.log (B / a) := (Real.log_pos ((one_lt_div ha0).mpr hab)).le
  have hδ : δ ≤ 1 / 2 := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hB0).mpr
    nlinarith
  have hcond : |traceExitProbability D x e - s| ≤ δ * s := by
    apply hh b a B (by linarith) (by linarith)
      (fun y ↦ traceExitProbability D y e) (fun _ ↦ MeasureTheory.measureReal_nonneg)
      (fun y hy ↦ trace_exit_probability_harmonic D e y hy)
    exact (Finset.image_subset_image (diskFinset_mono a (2 * a) ha0.le (by linarith))) (hK hx)
  have hlast := killed_trace_last_mem D K x hx ξ hξ
  have hterminal := hg a B ha hsep b (ξ.getLastD x) e K hK he hlast
  have hratio := killed_trace_relative_comparison hT D K hKD x e hx ξ hξ hep s ε δ
    (by dsimp [ε]; positivity) (by dsimp [δ]; positivity) hδ hcond hterminal
  have hscale : 2 * (ε + δ) ≤ (2 * (G + H)) * (a / B) * (1 + Real.log (B / a)) := by
    have h1 : 0 ≤ G * (a / B) := by positivity
    have h2 : 0 ≤ H * (a / B) * Real.log (B / a) := by positivity
    dsimp [ε, δ]
    nlinarith
  exact hratio.trans hscale

end SRWTightness
