import SRWTightness.SourceUpperMeshGrowth
import SRWTightness.SourceUpperMeshLogLower
import SRWTightness.SourceUpperTraversalComparison
import SRWTightness.DiskRootFineReturnBound

open Filter MeasureTheory

namespace SRWTightness

/-- The actual spatial weight in the manuscript upper mesh sum. -/
noncomputable def sourceUpperMeshWeight (t : ℝ) (j : ℕ) (z : Site) : ℝ :=
  1 + Real.log (2 * Real.exp t / max (Real.sqrt (normSq z))
    (sourceUpperTraversalRadius t (j + 1) + sourceUpperMeshBuffer t j))

/-- The actual first entrance is controlled by the source weight, including centers near zero. -/
theorem source_upper_mesh_first_hit (hinput : PotentialKernelAsymptoticInput) :
    ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      ∀ z ∈ sourceUpperMesh t j,
        setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) 0 ≤
          sourceUpperMeshWeight t j z / ((j : ℝ) + 1) := by
  obtain ⟨E, A, hE, hA, hreturn⟩ := disk_root_fine_return_bound hinput
  let M := max A E
  have hM : 0 ≤ M := le_trans (by linarith) (le_max_left _ _)
  filter_upwards [source_upper_mesh_scale_conditions, source_upper_coarse_range_eventually,
    source_upper_mesh_fine_radius_growth M hM] with t ht hcoarse hg
  intro j hj z hz
  let r := sourceUpperTraversalRadius t (j + 1)
  let H := sourceUpperMeshBuffer t j
  let b := r + H
  let q := Real.sqrt (normSq z)
  let d := Real.log (2 * Real.exp t / b)
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have hJ : 0 < (j : ℝ) + 1 := by positivity
  have hr10 : 10 ≤ r := (ht.2 j hj).1
  have hr : 0 < r := by linarith
  have hbnds := source_upper_mesh_buffer_bound t j hr10
  have hH : 0 ≤ H := hbnds.1
  have hhalf : 2 * H ≤ r := hbnds.2
  have hb : 0 < b := by dsimp [b]; linarith
  have hMr : M ≤ r := by
    have hh := hg j hj
    change M * ((j : ℝ) + 1) ≤ r at hh
    nlinarith
  have hAr : A ≤ r := (le_max_left _ _).trans hMr
  have hEr : E ≤ r := (le_max_right _ _).trans hMr
  have herr : E / b ≤ 1 := (div_le_one₀ hb).mpr (by dsimp [b]; linarith)
  have hrad := source_upper_traversal_radius_bound t ht.1 (j + 1)
  change 32 * r ≤ Real.exp t at hrad
  have hbR : b < 2 * Real.exp t := by dsimp [b]; nlinarith [Real.exp_pos t]
  have hden := source_upper_mesh_log_lower t j hcoarse hr10
  change (j : ℝ) + 1 + Real.log 32 ≤ d at hden
  have h32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
  have hdJ : (j : ℝ) + 1 ≤ d := by linarith
  have hd : 0 < d := hJ.trans_le hdJ
  have hpone : setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) 0 ≤ 1 := by
    rw [setHitProbability_eq_probability]
    exact measureReal_le_one
  by_cases hnear : q ≤ 2 * b
  · have hmax : max q b ≤ 2 * b := max_le hnear (by linarith)
    have hmax0 : 0 < max q b := hb.trans_le (le_max_right _ _)
    have hw := Real.log_le_log (div_pos (by positivity : 0 < 2 * Real.exp t)
      (show 0 < 2 * b by positivity))
      (div_le_div_of_nonneg_left (by positivity) hmax0 hmax)
    have hid : Real.log (2 * Real.exp t / (2 * b)) = d - Real.log 2 := by
      dsimp [d]
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) hb.ne',
        Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hb.ne']
      ring
    rw [hid] at hw
    have hlogcmp : Real.log (2 : ℝ) ≤ Real.log 32 :=
      Real.log_le_log (by norm_num) (by norm_num)
    have hweight : (j : ℝ) + 1 ≤ sourceUpperMeshWeight t j z := by
      change (j : ℝ) + 1 ≤ 1 + Real.log (2 * Real.exp t / max q b)
      linarith
    exact hpone.trans ((one_le_div hJ).mpr hweight)
  · have hq : 0 < q := by linarith
    have hbq : b ≤ q := by linarith
    have hz0 : normSq z ≤ (Real.exp t) ^ 2 := by
      have hzz := (mem_diskFinset _ _).mp (Finset.mem_filter.mp hz).1
      change normSq z < (3 * Real.exp t / 4) ^ 2 at hzz
      nlinarith [sq_nonneg (Real.exp t)]
    have hqR : q ≤ Real.exp t := (Real.sqrt_le_left (Real.exp_pos t).le).mpr hz0
    have hlogpos : 0 ≤ Real.log (2 * Real.exp t / q) :=
      Real.log_nonneg ((one_le_div hq).mpr (by linarith [Real.exp_pos t]))
    have hweight : sourceUpperMeshWeight t j z = 1 + Real.log (2 * Real.exp t / q) := by
      change 1 + Real.log (2 * Real.exp t / max q b) = _
      rw [max_eq_left hbq]
    have hw0 : 0 ≤ sourceUpperMeshWeight t j z := by rw [hweight]; linarith
    have hp := hreturn b (Real.exp t) q (by dsimp [b]; linarith) hbR hbq z 0 hz0
      (zero_mem_diskFinset (Real.exp t) (Real.exp_pos t))
      (by simp only [zero_sub, normSq_neg, q, le_refl])
    have hid : Real.log (2 * Real.exp t / q) = d - Real.log (q / b) := by
      dsimp [d]
      rw [Real.log_div (by positivity) hq.ne', Real.log_div (by positivity) hb.ne',
        Real.log_div hq.ne' hb.ne']
      ring
    have hp' : setHitProbability (diskFinset (Real.exp t)) (sourceUpperMeshInner t j z) 0 ≤
        (Real.log (2 * Real.exp t / q) + E / b) / d := by
      calc
        _ ≤ 1 - (Real.log (q / b) - E / b) / d := hp
        _ = _ := by rw [one_sub_div hd.ne', hid]; congr 1; ring
    calc
      _ ≤ (Real.log (2 * Real.exp t / q) + E / b) / d := hp'
      _ ≤ sourceUpperMeshWeight t j z / d :=
        div_le_div_of_nonneg_right (by rw [hweight]; linarith) hd.le
      _ ≤ _ := div_le_div_of_nonneg_left hw0 hJ hdJ

end SRWTightness
