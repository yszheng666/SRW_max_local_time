import SRWTightness.SourcePairShellCount
import SRWTightness.SourceSiteBridgeLaw

open MeasureTheory

namespace SRWTightness

/-- The actual common-space probability for an ordered pair of candidate centers. -/
noncomputable def sourcePairSuccessWeight (t A γ : ℝ) (I : ℕ)
    (z : ∀ b : Site, translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (p : Site × Site) : ℝ :=
  sourceEnlargedLaw.real
    (sourceSiteSuccessEvent t A γ p.1 I (z p.1) ∩ sourceSiteSuccessEvent t A γ p.2 I (z p.2))

theorem sourcePairSuccessWeight_nonneg (t A γ : ℝ) (I : ℕ)
    (z : ∀ b : Site, translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I)))
    (p : Site × Site) : 0 ≤ sourcePairSuccessWeight t A γ I z p := measureReal_nonneg

/-- Every actual shell pair meets the site-support and annular conditions of both probability bounds. -/
theorem source_pair_shell_sites (t A : ℝ) (I i : ℕ) (hi : i ≤ I)
    (hA : 4 * diskEnergyGapRatio ≤ A) (p : Site × Site)
    (hp : p ∈ sourcePairShell (sourceCandidateAnnulus (Real.exp t)) A i) :
    1 ≤ Real.sqrt (normSq (p.2 - p.1)) ∧
    p.2 ∈ translateFinset p.1 (diskFinset (A * diskEnergyGapRatio ^ I)) ∧
    Real.exp t / 4 ≤ Real.sqrt (normSq p.1) ∧
    Real.sqrt (normSq p.1) ≤ Real.exp t / 3 := by
  classical
  obtain ⟨hpZ, hlo, hhi⟩ := Finset.mem_filter.mp hp
  have hB := diskEnergyGapRatio_gt_four
  have hpow : 1 ≤ diskEnergyGapRatio ^ i := one_le_pow₀ (by linarith)
  have hpowI : 1 ≤ diskEnergyGapRatio ^ I := one_le_pow₀ (by linarith)
  have ha : 0 < A := by linarith
  have hr : 1 ≤ Real.sqrt (normSq (p.2 - p.1)) := by
    nlinarith
  have hai : A * diskEnergyGapRatio ^ i ≤ A * diskEnergyGapRatio ^ I :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) hi) ha.le
  have hlt : Real.sqrt (normSq (p.2 - p.1)) < A * diskEnergyGapRatio ^ I := by
    nlinarith
  have hmem : p.2 ∈ translateFinset p.1 (diskFinset (A * diskEnergyGapRatio ^ I)) := by
    simp only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq]
    have hs := Real.sq_sqrt (normSq_nonneg (p.2 - p.1))
    have hm := mul_pos (sub_pos.mpr hlt)
      (show 0 < A * diskEnergyGapRatio ^ I + Real.sqrt (normSq (p.2 - p.1)) by positivity)
    nlinarith
  have hb := (mem_sourceCandidateAnnulus (Real.exp t) (Real.exp_pos t) p.1).mp
    (Finset.mem_product.mp hpZ).1
  exact ⟨hr, hmem, hb⟩

end SRWTightness
