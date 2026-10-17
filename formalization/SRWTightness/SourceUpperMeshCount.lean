import SRWTightness.SourceUpperMarkParameters
import SRWTightness.KilledChildCountExponential

open MeasureTheory

namespace SRWTightness

/-- The unbuffered radius used for the upper point-centered traversals. -/
noncomputable def sourceUpperTraversalRadius (t : ℝ) (j : ℕ) : ℝ :=
  sourceRecordRadius (sourceUpperRadius t)
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) j

/-- The integer mesh spacing in the source spatial barrier argument. -/
noncomputable def sourceUpperMeshSpacing (t : ℝ) (j : ℕ) : ℕ :=
  ⌊sourceUpperTraversalRadius t (j + 1) / (1000 * ((j : ℝ) + 1))⌋₊

/-- The finite lattice mesh, with both coordinates divisible by its integer spacing. -/
noncomputable def sourceUpperMesh (t : ℝ) (j : ℕ) : Finset Site :=
  (diskFinset (3 * Real.exp t / 4)).filter fun z ↦
    (sourceUpperMeshSpacing t j : ℤ) ∣ z.1 ∧ (sourceUpperMeshSpacing t j : ℤ) ∣ z.2

noncomputable def sourceUpperMeshBuffer (t : ℝ) (j : ℕ) : ℝ :=
  2 * (sourceUpperMeshSpacing t j : ℝ) + 3

noncomputable def sourceUpperMeshInner (t : ℝ) (j : ℕ) (z : Site) : Finset Site :=
  translateFinset z (diskFinset
    (sourceUpperTraversalRadius t (j + 1) + sourceUpperMeshBuffer t j))

noncomputable def sourceUpperMeshOuter (t : ℝ) (j : ℕ) (z : Site) : Finset Site :=
  translateFinset z (diskFinset
    (sourceUpperTraversalRadius t j - sourceUpperMeshBuffer t j))

/-- Complete upper mesh segments, including a segment whose entrance is at time zero.
Identification with every entrance before killing requires the outer-domain containment. -/
noncomputable def sourceUpperMeshCount (t : ℝ) (j : ℕ) (z : Site) (ω : Sample) : ℕ :=
  (killedChildIntervals (diskFinset (Real.exp t))
    (sourceUpperMeshInner t j z) (sourceUpperMeshOuter t j z) 0 ω).length

/-- The actual mesh count has the local exponential tail under explicit geometry and return bounds.
These hypotheses are not assertions that the source mesh estimates have been discharged. -/
theorem source_upper_mesh_sqrt_count_tail (t : ℝ) (j : ℕ) (z : Site)
    (hinner : sourceUpperMeshInner t j z ⊆ sourceUpperMeshOuter t j z)
    (houter : sourceUpperMeshOuter t j z ⊆ diskFinset (Real.exp t))
    (K : ℝ) (hden : 0 < (j : ℝ) + K)
    (hreturn : ∀ ξ ∈ domainExitBoundary (sourceUpperMeshOuter t j z),
      setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) ξ ≤
        1 - 1 / ((j : ℝ) + K)) (u : ℝ) (hu : 0 < u) :
    pathLaw.real {ω | u ≤ Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))} ≤
      setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) 0 *
        Real.exp (1 / ((j : ℝ) + K) - u ^ 2 / (2 * ((j : ℝ) + K))) := by
  exact killedChildIntervals_sqrt_count_tail _ _ _ hinner houter _ hden hreturn 0 u hu

end SRWTightness
