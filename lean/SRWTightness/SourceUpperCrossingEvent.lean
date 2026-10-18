import SRWTightness.SourceUpperTraversalComparison
import SRWTightness.SourceUpperBarrierDefinition

open Filter MeasureTheory

namespace SRWTightness

/-- Actual point-centered barrier crossings in the source half-radius disk. -/
def sourceUpperCrossingEvent (t s : ℝ) : Set Sample :=
  ⋃ x ∈ diskFinset (Real.exp t / 2),
    ⋃ j ∈ Finset.range (sourceUpperCoarseDepth t + 1),
      {ω | sourceUpperBarrier t s j <
        Real.sqrt (2 * (sourceUpperTraversalCount t j x ω : ℝ))}

/-- The crossing event is measurable under the actual SRW path law. -/
theorem measurableSet_sourceUpperCrossingEvent (t s : ℝ) :
    MeasurableSet (sourceUpperCrossingEvent t s) := by
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro hj
  let F : PathWord → ℝ := fun w ↦ Real.sqrt (2 *
    ((wordChildIntervals
      (translateFinset x (diskFinset (sourceUpperTraversalRadius t (j + 1))))
      (translateFinset x (diskFinset (sourceUpperTraversalRadius t j))) 0 w).length : ℝ))
  exact (measurable_killedPathWord (diskFinset (Real.exp t)) 0)
    (Set.to_countable {w : PathWord | sourceUpperBarrier t s j < F w}).measurableSet

/-- Actual crossings are bounded by the finite sum of actual mesh crossing probabilities. -/
theorem source_upper_crossing_union_bound :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ,
      pathLaw.real (sourceUpperCrossingEvent t s) ≤
        ∑ j ∈ Finset.range (sourceUpperCoarseDepth t + 1),
          ∑ z ∈ sourceUpperMesh t j, pathLaw.real {ω |
            sourceUpperBarrier t s j ≤
              Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))} := by
  filter_upwards [source_upper_traversal_mesh_comparison] with t ht
  intro s
  let E := fun j z ↦ {ω : Sample | sourceUpperBarrier t s j ≤
    Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))}
  have hsub : sourceUpperCrossingEvent t s ⊆
      ⋃ j ∈ Finset.range (sourceUpperCoarseDepth t + 1), ⋃ z ∈ sourceUpperMesh t j, E j z := by
    intro ω hω
    simp only [sourceUpperCrossingEvent, Set.mem_iUnion, Set.mem_setOf_eq] at hω
    obtain ⟨x, hx, j, hj, hcross⟩ := hω
    have hjN : j ≤ sourceUpperCoarseDepth t := by
      have h := Finset.mem_range.mp hj
      omega
    obtain ⟨z, hz, _, _, _, hcount⟩ := ht j hjN x hx
    have hmono : Real.sqrt (2 * (sourceUpperTraversalCount t j x ω : ℝ)) ≤
        Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcount ω) (by norm_num))
    simp only [Set.mem_iUnion]
    exact ⟨j, hj, z, hz, hcross.le.trans hmono⟩
  calc
    _ ≤ pathLaw.real (⋃ j ∈ Finset.range (sourceUpperCoarseDepth t + 1),
        ⋃ z ∈ sourceUpperMesh t j, E j z) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ j ∈ Finset.range (sourceUpperCoarseDepth t + 1),
        pathLaw.real (⋃ z ∈ sourceUpperMesh t j, E j z) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun j _ ↦ measureReal_biUnion_finset_le _ _)

end SRWTightness
