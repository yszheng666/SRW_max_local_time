import SRWTightness.DiskTraceBoundaryRelative
import SRWTightness.PuncturedLocalGeometry
import SRWTightness.RecordRadialSupport
import SRWTightness.BoundaryRelativeComparison

namespace SRWTightness

/-- The actual disk trace error propagates to every point of the local punctured disk. -/
theorem disk_trace_interior_relative (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput) :
    ∃ C T : ℝ, 0 < C ∧ 2 ≤ T ∧ ∀ a B : ℝ, T ≤ a → 16 * a ≤ B →
      ∀ (b v e : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      e ∉ translateFinset b (diskFinset B) →
      v ∈ translateFinset b (diskFinset (3 * a / 2)) \ K →
      let D := translateFinset b (diskFinset B)
      |traceExitProbability (D \ K) v e - traceExitProbability D b e * competingExitMass D K v| ≤
        (C * (a / B) * Real.log (B / a)) * traceExitProbability D b e * competingExitMass D K v := by
  classical
  obtain ⟨C, T, hC, hT, hb⟩ := disk_trace_boundary_relative hP hH hM
  refine ⟨C, T, hC, hT, ?_⟩
  intro a B ha hB b v e K hK he hv
  let D := translateFinset b (diskFinset B)
  let Ω := translateFinset b (diskFinset (3 * a / 2)) \ K
  have ha2 : 2 ≤ a := hT.trans ha
  have hKD : K ⊆ D := hK.trans
    (Finset.image_subset_image (diskFinset_mono a B (by linarith) (by linarith)))
  have hΩ : Ω ⊆ D \ K := by
    intro y hy
    exact Finset.mem_sdiff.mpr ⟨
      (Finset.image_subset_image (diskFinset_mono (3 * a / 2) B
        (by linarith) (by linarith))) (Finset.mem_sdiff.mp hy).1,
      (Finset.mem_sdiff.mp hy).2⟩
  apply harmonic_relative_error_on_boundary Ω
    (fun y ↦ traceExitProbability (D \ K) y e) (competingExitMass D K)
    (fun y hy ↦ trace_exit_probability_harmonic _ e y (hΩ hy)) ?_
    (traceExitProbability D b e) (C * (a / B) * Real.log (B / a) * traceExitProbability D b e)
    ?_ v hv
  · intro y hy
    simp_rw [competingExitMass_eq_one_sub_hit D K hKD]
    exact one_sub_setHitProbability_harmonic D K y
      (Finset.mem_sdiff.mp (hΩ hy)).1 (Finset.mem_sdiff.mp (hΩ hy)).2
  · intro y hy
    by_cases hyK : y ∈ K
    · have hyn : y ∉ D \ K := fun h ↦ (Finset.mem_sdiff.mp h).2 hyK
      have hye : y ≠ e := fun h ↦ he (h ▸ hKD hyK)
      have hU : traceExitProbability (D \ K) y e = 0 := by
        rw [trace_exit_probability_eq_payoff, exitPayoff_eq_of_not_mem _ _ y hyn]
        simp [hye]
      have hQ : competingExitMass D K y = 0 := by
        rw [competingExitMass_eq_one_sub_hit D K hKD,
          setHitProbability_one D K y (hKD hyK) hyK]
        norm_num
      simp [hU, hQ]
    · have hrad := translated_disk_boundary_radial b (3 * a / 2) (by linarith) y
        (punctured_boundary_outside_target _ K y hy hyK)
      exact hb a B ha hB b y e K hK he hrad.1 hrad.2

end SRWTightness
