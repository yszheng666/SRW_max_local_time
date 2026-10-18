import SRWTightness.ExternalTraceReconstruction
import SRWTightness.BufferedLongTraceGeometry
import SRWTightness.BufferedLongRecordGeometry

namespace SRWTightness

/-- The retained disk contains every complete short word, including its exit overshoot. -/
theorem buffered_long_child_trace_representation (hR : TraceExcursionReconstructionInput)
    {M : Type*} (ρ H J : ℝ) (hH : 1 ≤ H) (hρ : 8 * H ≤ ρ) (hJ : 1 ≤ J)
    (b x : Site) (F : Site → PathWord → M) :
    let D := translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H))
    let K := translateFinset b (diskFinset (ρ - H))
    let C := translateFinset b (diskFinset (Real.exp 1 * ρ + H))
    let E := translateFinset b (diskFinset (Real.exp 1 * ρ + H + 2))
    ∃ g : List Site → List M,
      killedChildRecords D K C x F =ᵐ[pathLaw] fun ω ↦ g (killedVisitTrace D E x ω) := by
  dsimp only
  have hρ0 : 0 ≤ ρ := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hshort : 0 ≤ Real.exp 1 * ρ + H := by positivity
  have hKC := (buffered_long_domains_nested ρ H J hH hρ hJ b).1
  have hCE : translateFinset b (diskFinset (Real.exp 1 * ρ + H)) ⊆
      translateFinset b (diskFinset (Real.exp 1 * ρ + H + 2)) :=
    Finset.image_subset_image (diskFinset_mono _ _ hshort (by linarith))
  obtain ⟨ha, _, hsep, _⟩ :=
    buffered_long_trace_geometry ρ H J (by linarith) hH0 (by linarith) hJ
  have hscale : 1 ≤ Real.exp (J - 1) := Real.one_le_exp_iff.mpr (by linarith)
  have hab : Real.exp 1 * ρ + H + 2 ≤ Real.exp (J + 1) * ρ + H := by
    nlinarith [mul_le_mul_of_nonneg_right hscale ha.le]
  have hED : translateFinset b (diskFinset (Real.exp 1 * ρ + H + 2)) ⊆
      translateFinset b (diskFinset (Real.exp (J + 1) * ρ + H)) :=
    Finset.image_subset_image (diskFinset_mono _ _ ha.le hab)
  apply killed_child_records_trace_representation hR _ _ _ _ x F hKC hCE hED
  intro z hz
  have hr := (translated_disk_boundary_radial b _ hshort z hz).2
  have hnon := Real.sqrt_nonneg (normSq (z - b))
  have hsquare := normSq_eq_sq_sqrt (z - b)
  simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
  nlinarith

end SRWTightness
