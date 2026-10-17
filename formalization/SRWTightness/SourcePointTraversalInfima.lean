import SRWTightness.SourceTraversalStopping
import SRWTightness.SourceDiskObservables
import SRWTightness.GreenTranslation

namespace SRWTightness

/-- A point shell's finite lattice set is exactly the manuscript's open Euclidean ball. -/
theorem source_point_traversal_inner_iff (radius : ℝ) (hr : 0 < radius)
    (z x : Site) (ω : Sample) (n : ℕ) :
    x + position ω n ∈ translateFinset z (diskFinset radius) ↔
      Real.sqrt (normSq (x + position ω n - z)) < radius := by
  rw [mem_translateFinset_iff, mem_diskFinset]
  exact source_disk_region_iff radius hr _

/-- The source point-centered sigma/eta sequence has the literal Euclidean infimum formulas. -/
theorem source_point_traversal_infima (inner outer : ℝ) (hi : 0 < inner) (ho : 0 < outer)
    (z x : Site) (ω : Sample) :
    let K := translateFinset z (diskFinset inner)
    let C := translateFinset z (diskFinset outer)
    sourceTraversalSigma K C x ω 0 0 =
        sInf ((fun n : ℕ ↦ (n : WithTop ℕ)) ''
          {n | Real.sqrt (normSq (x + position ω n - z)) < inner}) ∧
      ∀ i, sourceTraversalEta K C x ω 0 i =
        sInf ((fun n : ℕ ↦ (n : WithTop ℕ)) ''
          {n | sourceTraversalSigma K C x ω 0 i ≤ n ∧
            outer ≤ Real.sqrt (normSq (x + position ω n - z))}) ∧
        sourceTraversalSigma K C x ω 0 (i + 1) =
          sInf ((fun n : ℕ ↦ (n : WithTop ℕ)) ''
            {n | sourceTraversalEta K C x ω 0 i ≤ n ∧
              Real.sqrt (normSq (x + position ω n - z)) < inner}) := by
  dsimp only
  have hin (n : ℕ) := source_point_traversal_inner_iff inner hi z x ω n
  have hout (n : ℕ) : x + position ω n ∉ translateFinset z (diskFinset outer) ↔
      outer ≤ Real.sqrt (normSq (x + position ω n - z)) := by
    rw [source_point_traversal_inner_iff outer ho z x ω n, not_lt]
  constructor
  · change sourceFirstHit _ 0 = _
    rw [sourceFirstHit_eq_sInf]
    simp only [hin, zero_le, true_and]
  · intro i
    constructor
    · unfold sourceTraversalEta
      rw [sourceFirstHit_eq_sInf]
      simp only [hout]
    · rw [sourceTraversalSigma_succ, sourceFirstHit_eq_sInf]
      simp only [hin]

end SRWTightness
