import SRWTightness.SourceUpperMeshWeightSum
import SRWTightness.SourceUpperMeshLocalTail
import SRWTightness.SourceUpperBarrierSpatialSum

open Filter MeasureTheory

namespace SRWTightness

/-- The manuscript spatial barrier sum on the actual SRW mesh, with all local inputs discharged. -/
theorem source_upper_actual_barrier_sum (hinput : PotentialKernelAsymptoticInput)
    (hScale : ExponentialFloorScaleInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ j : ℕ, 1 ≤ j → j ≤ sourceUpperCoarseDepth t → ∀ v : ℝ, 0 ≤ v →
        (∑ z ∈ sourceUpperMesh t j, pathLaw.real {ω |
          sourceUpperBarrier t s j + v ≤ Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))}) ≤
          C * ((j : ℝ) + 1) ^ 3 *
            Real.exp (-3 * ((4 + s) + sourceUpperBarrierCurvature t j + v) / 2) := by
  obtain ⟨K, C₁, hK, hC₁, hlocal⟩ := source_upper_mesh_local_tail hinput
  obtain ⟨C₂, hC₂, hmesh⟩ := source_upper_mesh_weight_sum
  obtain ⟨C, hC, hsum⟩ := source_upper_barrier_spatial_sum hScale C₁ C₂ K hC₁ hC₂
    (by linarith)
  obtain ⟨B, _, hcond⟩ := source_upper_threshold_conditions hScale
  refine ⟨C, hC, ?_⟩
  filter_upwards [hlocal, hmesh, hsum, source_upper_barrier_slope_bounds hScale, hcond]
    with t hl hm hsumt hθ ht
  intro s hs hslog j hj hjN v hv
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hjT : (j : ℝ) ≤ sourceUpperTotalDepth t := by
    have hj' : (j : ℝ) ≤ (sourceUpperCoarseDepth t : ℝ) := by exact_mod_cast hjN
    have hd := ht.2.2.2.2.2.2.1
    unfold sourceUpperTotalDepth
    linarith
  have hw : 0 ≤ sourceUpperBarrierCurvature t j := by
    unfold sourceUpperBarrierCurvature
    exact Real.rpow_nonneg (le_min hj0 (sub_nonneg.mpr hjT)) _
  have hpos : 0 < sourceUpperBarrier t s j + v := by
    have hθ0 : 0 ≤ sourceUpperSlope t s := by have hh := (hθ s hs hslog).1; linarith
    unfold sourceUpperBarrier
    nlinarith [mul_nonneg hθ0 hj0]
  exact hsumt s hs hslog j hj hjN v hv (sourceUpperMesh t j)
    (fun z ↦ pathLaw.real {ω | sourceUpperBarrier t s j + v ≤
      Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))}) (sourceUpperMeshWeight t j)
    (fun z hz ↦ hl j hjN z hz _ hpos) (hm j hjN)

end SRWTightness
