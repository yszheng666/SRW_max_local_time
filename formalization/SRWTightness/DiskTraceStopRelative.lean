import SRWTightness.DiskTraceInteriorRelative
import SRWTightness.TraceStopRelative

namespace SRWTightness

/-- The actual terminal escape kernel has the source relative disk error uniformly on K. -/
theorem disk_trace_stop_relative (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput) :
    ∃ C T : ℝ, 0 < C ∧ 2 ≤ T ∧ ∀ a B : ℝ, T ≤ a → 16 * a ≤ B →
      ∀ (b x e : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      e ∉ translateFinset b (diskFinset B) → x ∈ K →
      let D := translateFinset b (diskFinset B)
      |traceStopExitProbability D K x e - traceExitProbability D b e * traceStopProbability D K x| ≤
        (C * (a / B) * Real.log (B / a)) * traceExitProbability D b e * traceStopProbability D K x := by
  classical
  obtain ⟨C, T, hC, hT, hi⟩ := disk_trace_interior_relative hP hH hM
  refine ⟨C, T, hC, hT, ?_⟩
  intro a B ha hB b x e K hK he hx
  let D := translateFinset b (diskFinset B)
  have ha2 : 2 ≤ a := hT.trans ha
  have hKD : K ⊆ D := hK.trans
    (Finset.image_subset_image (diskFinset_mono a B (by linarith) (by linarith)))
  apply trace_stop_relative_from_neighbors hM D K hKD x e hx he
    (traceExitProbability D b e) (C * (a / B) * Real.log (B / a))
  intro d
  by_cases hyK : x + step d ∈ K
  · have hyn : x + step d ∉ D \ K := fun h ↦ (Finset.mem_sdiff.mp h).2 hyK
    have hye : x + step d ≠ e := fun h ↦ he (h ▸ hKD hyK)
    have hU : traceExitProbability (D \ K) (x + step d) e = 0 := by
      rw [trace_exit_probability_eq_payoff, exitPayoff_eq_of_not_mem _ _ _ hyn]
      simp [hye]
    have hQ : competingExitMass D K (x + step d) = 0 := by
      rw [competingExitMass_eq_one_sub_hit D K hKD,
        setHitProbability_one D K _ (hKD hyK) hyK]
      norm_num
    simp [hU, hQ]
  · exact hi a B ha hB b (x + step d) e K hK he
      (Finset.mem_sdiff.mpr ⟨inner_disk_neighbor_mem_intermediate b x a ha2 (hK hx) d, hyK⟩)

end SRWTightness
