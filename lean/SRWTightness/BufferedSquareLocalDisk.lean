import SRWTightness.SquareBufferPerturbation
import SRWTightness.RecordRadialSupport

namespace SRWTightness

/-- A local disk and its exit layer retain half of both nested-square buffers. -/
theorem buffered_square_local_disk (δ : ℝ) (hδ : 0 < δ) (a b x : Site) (N M : ℕ)
    (hNM : N ≤ M) (hlarge : 8 ≤ δ * (N : ℝ))
    (hE : squareProportionalBuffer δ a N x) (hD : squareProportionalBuffer δ b M x)
    (z : Site) (hz : z ∈ translateFinset x (diskFinset (δ * N / 8)) ∨
      z ∈ domainExitBoundary (translateFinset x (diskFinset (δ * N / 8)))) :
    z ∈ latticeSquareInterior a N ∧ squareProportionalBuffer (δ / 2) a N z ∧
      squareProportionalBuffer (δ / 2) b M z := by
  have hR : 0 ≤ δ * (N : ℝ) / 8 := by positivity
  have hr : 0 ≤ δ * (N : ℝ) / 8 + 1 := by positivity
  have hn : normSq (z - x) ≤ (δ * (N : ℝ) / 8 + 1) ^ 2 := by
    rcases hz with hz | hz
    · have hh : normSq (z - x) < (δ * (N : ℝ) / 8) ^ 2 := by
        simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hz
      nlinarith
    · exact (Real.sqrt_le_iff.mp (translated_disk_boundary_radial x _ hR z hz).2).2
  have hside : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hscale := mul_le_mul_of_nonneg_left hside hδ.le
  have he := square_buffer_displacement δ (δ / 2) _ a x z N hr hE hn (by nlinarith)
  have hd := square_buffer_displacement δ (δ / 2) _ b x z M hr hD hn (by nlinarith)
  exact ⟨square_buffer_mem_interior (δ / 2) a z N (by nlinarith) he, he, hd⟩

end SRWTightness
