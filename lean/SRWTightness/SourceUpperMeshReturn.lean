import SRWTightness.UpperMeshLogGap
import SRWTightness.SourceUpperMeshGrowth
import SRWTightness.SourceUpperTraversalComparison
import SRWTightness.SourceRootLogDenominator
import SRWTightness.DiskRootFineReturnBound
import SRWTightness.RecordRadialSupport

open Filter

namespace SRWTightness

/-- The actual upper mesh has the sharp reciprocal-level return deficit at all outer exits. -/
theorem source_upper_mesh_return_rate (hinput : PotentialKernelAsymptoticInput) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      ∀ z ∈ sourceUpperMesh t j, ∀ ξ ∈ domainExitBoundary (sourceUpperMeshOuter t j z),
        setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) ξ ≤
          1 - 1 / ((j : ℝ) + K) := by
  obtain ⟨E, A, hE, hA, hreturn⟩ := disk_root_fine_return_bound hinput
  let C : ℝ := Real.log 32 + 2 * Real.log 2 + 2
  have hC : 1 ≤ C := by
    have h32 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 32)
    have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    dsimp [C]
    linarith
  let M := max 1000 (max A (200 * E))
  have hM : 0 ≤ M := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨2 * C + 2, by linarith, ?_⟩
  filter_upwards [source_upper_mesh_scale_conditions,
    source_upper_mesh_fine_radius_growth M hM] with t ht hg
  intro j hj z hz ξ hξ
  let r := sourceUpperTraversalRadius t (j + 1)
  let H := sourceUpperMeshBuffer t j
  let b := r + H
  let c := sourceUpperTraversalRadius t j - H
  let δ : ℝ := 1 / (200 * ((j : ℝ) + 1))
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hJ : 0 < 200 * ((j : ℝ) + 1) := by positivity
  have hr10 : 10 ≤ r := (ht.2 j hj).1
  have hr : 0 < r := by linarith
  have hbnds := source_upper_mesh_buffer_bound t j hr10
  have hH : 0 ≤ H := hbnds.1
  have hHhalf : 2 * H ≤ r := hbnds.2
  have hbig := hg j hj
  change M * ((j : ℝ) + 1) ≤ r at hbig
  have h1000 : 1000 * ((j : ℝ) + 1) ≤ r :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans hbig
  have hAr : A ≤ r := by
    have hAM : A ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_right hAM (show 0 ≤ (j : ℝ) + 1 by positivity)
    nlinarith
  have hEr : 200 * E * ((j : ℝ) + 1) ≤ r :=
    (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans (le_max_right _ _))
      (by positivity)).trans hbig
  have hb : 0 < b := by dsimp [b]; linarith
  have he : Real.exp 1 * r = sourceUpperTraversalRadius t j :=
    sourceRecordRadius_successor _ _ j
  have hbc : b ≤ c := by dsimp [b, c]; nlinarith [Real.exp_one_gt_two]
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hδhalf : δ ≤ 1 / 2 := (div_le_iff₀ hJ).mpr (by linarith)
  have hsmall : H ≤ δ * r := by
    have hh := source_upper_mesh_relative_buffer t j h1000
    change H ≤ r / (200 * ((j : ℝ) + 1)) at hh
    dsimp [δ]
    convert hh using 1 <;> ring
  have hlog := upper_mesh_log_gap r H δ hr hH hδ hδhalf hsmall
  rw [he] at hlog
  change 1 - 3 * δ ≤ Real.log (c / b) at hlog
  have herr : E / b ≤ δ := by
    apply (div_le_div_iff₀ hb hJ).mpr
    dsimp [b]
    nlinarith
  have hnum : 1 - 1 / (4 * ((j : ℝ) + 1)) ≤ Real.log (c / b) - E / b := by
    have hid : 1 / (4 * ((j : ℝ) + 1)) = 50 * δ := by
      dsimp [δ]
      field_simp <;> ring
    rw [hid]
    linarith
  have hrad := source_upper_traversal_radius_bound t ht.1 (j + 1)
  change 32 * r ≤ Real.exp t at hrad
  have hbR : b < 2 * Real.exp t := by dsimp [b]; nlinarith [Real.exp_pos t]
  have hroot := (source_root_depth_bracket (Real.exp t) (sourceUpperRadius t)
    (Real.exp_pos _) ht.1).2.le
  have hden := source_root_log_denominator (Real.exp t) (sourceUpperRadius t) (-H)
    (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) j
    (Real.exp_pos _) (Real.exp_pos _) (by change 2 * -H ≤ r; linarith) hroot
  change Real.log (2 * Real.exp t / (r - -H)) ≤ (j : ℝ) + C at hden
  rw [sub_neg_eq_add] at hden
  change Real.log (2 * Real.exp t / b) ≤ (j : ℝ) + C at hden
  have hd : 0 < Real.log (2 * Real.exp t / b) :=
    Real.log_pos ((one_lt_div hb).mpr hbR)
  have hgap := upper_mesh_shifted_return_gap (j : ℝ) C _ _ hj0 hC hd hden hnum
  by_cases hξD : ξ ∈ diskFinset (Real.exp t)
  · have hz0 : normSq z ≤ (Real.exp t) ^ 2 := by
      have hzz := (mem_diskFinset _ _).mp (Finset.mem_filter.mp hz).1
      change normSq z < (3 * Real.exp t / 4) ^ 2 at hzz
      nlinarith [sq_nonneg (Real.exp t)]
    have hc : 0 ≤ c := hb.le.trans hbc
    have hξrad := (translated_disk_boundary_radial z c hc ξ hξ).1
    have hp := hreturn b (Real.exp t) c (by dsimp [b]; linarith) hbR hbc z ξ hz0 hξD hξrad
    change setHitProbability (diskFinset (Real.exp t)) (translateFinset z (diskFinset b)) ξ ≤ _
    linarith
  · rw [setHitProbability_zero_of_not_mem _ _ ξ hξD]
    have hh : 1 / ((j : ℝ) + (2 * C + 2)) ≤ 1 :=
      (div_le_one₀ (by linarith)).mpr (by linarith)
    linarith

end SRWTightness
