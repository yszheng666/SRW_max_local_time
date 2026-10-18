import SRWTightness.TranslatedDiskGeometry
import SRWTightness.RecordExitSlice
import SRWTightness.DirectionReversal

namespace SRWTightness

/-- A punctured-domain boundary point outside the removed target is an original boundary point. -/
theorem punctured_boundary_outside_target (B K : Finset Site) (y : Site)
    (hy : y ∈ domainExitBoundary (B \ K)) (hK : y ∉ K) : y ∈ domainExitBoundary B := by
  obtain ⟨hout, z, hz, d, he⟩ := hy
  exact ⟨fun hb ↦ hout (Finset.mem_sdiff.mpr ⟨hb, hK⟩), z,
    (Finset.mem_sdiff.mp hz).1, d, he⟩

/-- All neighbors of the inner disk lie strictly in the intermediate disk, including a=2. -/
theorem inner_disk_neighbor_mem_intermediate (b v : Site) (a : ℝ) (ha : 2 ≤ a)
    (hv : v ∈ translateFinset b (diskFinset a)) (d : Direction) :
    v + step d ∈ translateFinset b (diskFinset (3 * a / 2)) := by
  have hv' : normSq (v - b) < a ^ 2 := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hv
  have hd : normSq (step d) ≤ (1 : ℝ) ^ 2 := by fin_cases d <;> norm_num [step, normSq, Fin.ext_iff]
  have hh := normSq_add_lt_of_le_of_lt (step d) (v - b) (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 ≤ a) hd hv'
  have he : step d + (v - b) = v + step d - b := by abel
  rw [he] at hh
  simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
  nlinarith

/-- Incoming neighbors of the target belong to the local punctured comparison domain. -/
theorem incoming_neighbor_mem_local_puncture (D K : Finset Site) (b v y : Site)
    (a : ℝ) (ha : 2 ≤ a) (hK : K ⊆ translateFinset b (diskFinset a))
    (hv : v ∈ K) (hy : y ∈ D \ K) (hin : ∃ d : Direction, y + step d = v) :
    y ∈ translateFinset b (diskFinset (3 * a / 2)) \ K := by
  obtain ⟨d, hd⟩ := hin
  have he : y = v + step (reverseDirection d) := by
    rw [step_reverseDirection, ← hd]
    abel
  apply Finset.mem_sdiff.mpr
  exact ⟨he ▸ inner_disk_neighbor_mem_intermediate b v a ha (hK hv) (reverseDirection d),
    (Finset.mem_sdiff.mp hy).2⟩

end SRWTightness
