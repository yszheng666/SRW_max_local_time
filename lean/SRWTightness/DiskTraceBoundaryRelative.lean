import SRWTightness.TraceBoundaryError
import SRWTightness.IntermediateEscapeLower

namespace SRWTightness

/-- The source intermediate-circle error is relative to the actual escape probability. -/
theorem disk_trace_boundary_relative (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput) :
    ∃ C T : ℝ, 0 < C ∧ 2 ≤ T ∧ ∀ a B : ℝ, T ≤ a → 16 * a ≤ B →
      ∀ (b v e : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      e ∉ translateFinset b (diskFinset B) →
      3 * a / 2 ≤ Real.sqrt (normSq (v - b)) →
      Real.sqrt (normSq (v - b)) ≤ 3 * a / 2 + 1 →
      let D := translateFinset b (diskFinset B)
      |traceExitProbability (D \ K) v e - traceExitProbability D b e * competingExitMass D K v| ≤
        (C * (a / B) * Real.log (B / a)) * traceExitProbability D b e * competingExitMass D K v := by
  obtain ⟨H, hH0, hh⟩ := hH
  obtain ⟨c, T, hc, hT, hesc⟩ := intermediate_escape_lower hP
  refine ⟨4 * H / c, T, by positivity, hT, ?_⟩
  intro a B ha hB b v e K hK he hvlo hvhi
  let D := translateFinset b (diskFinset B)
  let s := traceExitProbability D b e
  have ha2 : 2 ≤ a := hT.trans ha
  have ha0 : 0 < a := by linarith
  have hB0 : 0 < B := by linarith
  have hab : a < B := by linarith
  have hKD : K ⊆ D := hK.trans
    (Finset.image_subset_image (diskFinset_mono a B ha0.le hab.le))
  have hs : 0 ≤ s := MeasureTheory.measureReal_nonneg
  have hpoint (y : Site) (hy : Real.sqrt (normSq (y - b)) ≤ 3 * a / 2 + 1) :
      |traceExitProbability D y e - s| ≤ H * (2 * a / B) * s := by
    apply hh b (2 * a) B (by linarith) (by linarith)
      (fun z ↦ traceExitProbability D z e) (fun _ ↦ MeasureTheory.measureReal_nonneg)
      (fun z hz ↦ trace_exit_probability_harmonic D e z hz)
    simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    have hn := Real.sqrt_nonneg (normSq (y - b))
    have hsq := Real.sq_sqrt (normSq_nonneg (y - b))
    nlinarith
  have htarget : ∀ y ∈ K, |traceExitProbability D y e - s| ≤ H * (2 * a / B) * s := by
    intro y hy
    have hn : normSq (y - b) < a ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hK hy
    apply hpoint
    have hh' := (Real.sqrt_le_left ha0.le).mpr hn.le
    linarith
  have hbound := trace_boundary_subtraction_error hM D K hKD v e he s (H * (2 * a / B))
    hs (by positivity) (hpoint v hvhi) htarget
  have hvB : normSq (v - b) < B ^ 2 := by
    have hn := Real.sqrt_nonneg (normSq (v - b))
    have hsq := Real.sq_sqrt (normSq_nonneg (v - b))
    nlinarith
  have hescape := hesc a B ha hab b v K hK hvlo hvB
  rw [← competingExitMass_eq_one_sub_hit D K hKD v] at hescape
  have hlog : 0 < Real.log (B / a) := Real.log_pos ((one_lt_div ha0).mpr hab)
  have hmul := mul_le_mul_of_nonneg_left hescape
    (show 0 ≤ (4 * H / c * (a / B) * Real.log (B / a)) * s by positivity)
  have heq : (4 * H / c * (a / B) * Real.log (B / a) * s) * (c / Real.log (B / a)) =
      2 * (H * (2 * a / B)) * s := by
    field_simp
    <;> ring
  rw [heq] at hmul
  exact hbound.trans hmul

end SRWTightness
