import SRWTightness.DiskFiniteDomain
import Mathlib.Tactic.Linarith

open Filter
open scoped Topology

namespace SRWTightness

/-- The entire closed lattice annulus used for successful sites in the manuscript. -/
noncomputable def sourceCandidateAnnulus (R : ℝ) : Finset Site := by
  classical
  exact (diskFinset (|R| + 1)).filter
    (fun z ↦ R / 4 ≤ Real.sqrt (normSq z) ∧ Real.sqrt (normSq z) ≤ R / 3)

/-- The finite representation contains exactly the manuscript candidates at positive radius. -/
theorem mem_sourceCandidateAnnulus (R : ℝ) (hR : 0 < R) (z : Site) :
    z ∈ sourceCandidateAnnulus R ↔
      R / 4 ≤ Real.sqrt (normSq z) ∧ Real.sqrt (normSq z) ≤ R / 3 := by
  classical
  simp only [sourceCandidateAnnulus, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [mem_diskFinset]
    change normSq z < (|R| + 1) ^ 2
    rw [abs_of_pos hR]
    have hs := Real.sq_sqrt (normSq_nonneg z)
    have hp := Real.sqrt_nonneg (normSq z)
    nlinarith [h.2]

/-- Explicit standard lattice-count input; it is an assumption, not an internally proved result. -/
def LatticeAnnulusCountInput : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ R : ℝ in atTop,
    c * R ^ 2 ≤ (sourceCandidateAnnulus R).card ∧
      ((sourceCandidateAnnulus R).card : ℝ) ≤ C * R ^ 2

end SRWTightness
