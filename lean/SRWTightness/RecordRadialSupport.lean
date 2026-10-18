import SRWTightness.CompetingEntranceLaw
import SRWTightness.LatticeTranslation
import SRWTightness.AnnulusExitGeometry

open MeasureTheory

namespace SRWTightness

/-- An actual disk exit lies in its outer unit radial layer, also after translation. -/
theorem translated_disk_boundary_radial (b : Site) (R : ℝ) (hR : 0 ≤ R) (y : Site)
    (hy : y ∈ domainExitBoundary (translateFinset b (diskFinset R))) :
    R ≤ Real.sqrt (normSq (y - b)) ∧ Real.sqrt (normSq (y - b)) ≤ R + 1 := by
  obtain ⟨hout, z, hz, d, he⟩ := hy
  have hyl : R ^ 2 ≤ normSq (y - b) := by
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hout
  have hzu : normSq (z - b) ≤ R ^ 2 := by
    have hz' : normSq (z - b) < R ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hz
    exact hz'.le
  have hyu : normSq (y - b) ≤ (R + 1) ^ 2 := by
    rw [he, show z + step d - b = (z - b) + step d by abel]
    exact normSq_step_le (z - b) d hR hzu
  exact ⟨(Real.le_sqrt hR (normSq_nonneg _)).mpr hyl,
    (Real.sqrt_le_left (by linarith)).mpr hyu⟩

/-- Competing entrance points lie in the inner disk's inner unit radial layer. -/
theorem competingEntranceLaw_radial_support (b : Site) (a R : ℝ) (ha : 1 ≤ a) (x : Site)
    (hx : x ∈ translateFinset b (diskFinset R) \ translateFinset b (diskFinset a)) :
    ∀ᵐ y ∂competingEntranceLaw (translateFinset b (diskFinset R))
      (translateFinset b (diskFinset a)) x,
      a - 1 ≤ Real.sqrt (normSq (y - b)) ∧ Real.sqrt (normSq (y - b)) ≤ a := by
  filter_upwards [competingEntranceLaw_supported_boundary _ _ x hx] with y hy
  obtain ⟨_, z, hz, d, he⟩ := hy.1
  have hzl : a ^ 2 ≤ normSq (z - b) := by
    have hn := (Finset.mem_sdiff.mp hz).2
    simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq, not_lt] using hn
  have hyl : (a - 1) ^ 2 ≤ normSq (y - b) := by
    rw [he, show z + step d - b = (z - b) + step d by abel]
    exact normSq_step_lower (z - b) d a ha hzl
  have hyu : normSq (y - b) ≤ a ^ 2 := by
    have hh : normSq (y - b) < a ^ 2 := by
      simpa only [Finset.mem_coe, mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hy.2
    exact hh.le
  exact ⟨(Real.le_sqrt (by linarith) (normSq_nonneg _)).mpr hyl,
    (Real.sqrt_le_left (by linarith)).mpr hyu⟩

/-- Conditioning on any child record retains the correct outer radial exit layer. -/
theorem recordExitSlice_radial_support {M : Type*} (b : Site) (R : ℝ) (hR : 0 ≤ R)
    (x : Site) (hx : x ∈ translateFinset b (diskFinset R)) (F : Sample → M) (r : M) :
    ∀ᵐ y ∂recordExitSlice (translateFinset b (diskFinset R)) x F r,
      R ≤ Real.sqrt (normSq (y - b)) ∧ Real.sqrt (normSq (y - b)) ≤ R + 1 := by
  filter_upwards [recordExitSlice_supported _ x hx F r] with y hy
  exact translated_disk_boundary_radial b R hR y hy

end SRWTightness
