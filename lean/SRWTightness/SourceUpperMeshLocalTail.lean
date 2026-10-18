import SRWTightness.SourceUpperMeshReturn
import SRWTightness.SourceUpperMeshFirstHit

open Filter MeasureTheory

namespace SRWTightness

/-- The manuscript local mesh tail with the actual weight, conditional on potential asymptotics. -/
theorem source_upper_mesh_local_tail (hinput : PotentialKernelAsymptoticInput) :
    ∃ K C : ℝ, 1 ≤ K ∧ 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t → ∀ z ∈ sourceUpperMesh t j,
        ∀ u : ℝ, 0 < u →
          pathLaw.real {ω | u ≤ Real.sqrt (2 * (sourceUpperMeshCount t j z ω : ℝ))} ≤
            C * sourceUpperMeshWeight t j z / ((j : ℝ) + 1) *
              Real.exp (-u ^ 2 / (2 * ((j : ℝ) + K))) := by
  obtain ⟨K, hK, hreturn⟩ := source_upper_mesh_return_rate hinput
  refine ⟨K, Real.exp 1, hK, Real.exp_pos 1, ?_⟩
  filter_upwards [source_upper_mesh_scale_conditions, source_upper_mesh_first_hit hinput,
    hreturn] with t ht hhit hret
  intro j hj z hz u hu
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hden : 0 < (j : ℝ) + K := by linarith
  have hinv : 1 / ((j : ℝ) + K) ≤ 1 := (div_le_one₀ hden).mpr (by linarith)
  have hr := (ht.2 j hj).1
  have hb := source_upper_mesh_sqrt_count_tail t j z
    (source_upper_mesh_inner_subset_outer t j z hr)
    (source_upper_mesh_outer_subset_killing t j z ht.1 hr hz)
    K hden (hret j hj z hz) u hu
  have hfirst := hhit j hj z hz
  have hp0 : 0 ≤ setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) 0 := by
    rw [setHitProbability_eq_probability]
    exact measureReal_nonneg
  have hcoef : 0 ≤ sourceUpperMeshWeight t j z / ((j : ℝ) + 1) := hp0.trans hfirst
  calc
    _ ≤ setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) 0 *
        Real.exp (1 / ((j : ℝ) + K) - u ^ 2 / (2 * ((j : ℝ) + K))) := hb
    _ ≤ (sourceUpperMeshWeight t j z / ((j : ℝ) + 1)) *
        Real.exp (1 / ((j : ℝ) + K) - u ^ 2 / (2 * ((j : ℝ) + K))) :=
      mul_le_mul_of_nonneg_right hfirst (Real.exp_pos _).le
    _ ≤ (sourceUpperMeshWeight t j z / ((j : ℝ) + 1)) *
        Real.exp (1 - u ^ 2 / (2 * ((j : ℝ) + K))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (sub_le_sub_right hinv _)) hcoef
    _ = _ := by
      rw [show 1 - u ^ 2 / (2 * ((j : ℝ) + K)) =
        1 + (-u ^ 2 / (2 * ((j : ℝ) + K))) by ring, Real.exp_add]
      ring

end SRWTightness
