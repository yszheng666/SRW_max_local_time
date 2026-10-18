import SRWTightness.AnnulusFineReturnBound
import SRWTightness.SourceBufferedHalf
import SRWTightness.HitTargetMonotonicity
import SRWTightness.FirstEntranceWordMark
import SRWTightness.LatticeTranslation
import SRWTightness.DiskCapacityLogBound

open MeasureTheory
namespace SRWTightness

/-- The actual zero terminal mark has uniformly positive mass for all enclosed observation sets. -/
theorem source_terminal_zero_mass (hinput : PotentialKernelAsymptoticInput) :
    ∃ c T : ℝ, 0 < c ∧ 128 ≤ T ∧ ∀ (m H a : ℝ), T ≤ m →
      0 ≤ H → H ≤ m / 8 → 0 ≤ a → a ≤ m / 2 →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ z : Site, m - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ m - H + 1 →
      c ≤ (firstEntranceWordMarkLaw
        (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real {none} := by
  obtain ⟨L, A, hL, hA, hh⟩ := annulus_fine_return_bound hinput
  let q : ℝ := Real.log (3 / 2 : ℝ)
  let d : ℝ := Real.log (2 * Real.exp 1 + 2)
  have hq : 0 < q := Real.log_pos (by norm_num)
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hd : 0 < d := Real.log_pos (by linarith)
  refine ⟨q / (2 * d), max 128 (max (2 * A) (4 * L / q)), by positivity,
    le_max_left _ _, ?_⟩
  intro m H a hm hH hHm ha ham b K hK z hzlo hzhi
  have hm128 : 128 ≤ m := (le_max_left _ _).trans hm
  have hAm : 2 * A ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hLm : 4 * L / q ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm0 : 0 < m := by linarith
  let R : ℝ := Real.exp 1 * m + H
  have hR : m / 2 < R := by dsimp [R]; nlinarith
  have hden : 0 < Real.log (R / (m / 2)) :=
    Real.log_pos ((one_lt_div (by positivity : 0 < m / 2)).mpr hR)
  have hdenmax : Real.log (R / (m / 2)) ≤ d := by
    apply Real.log_le_log (div_pos (by dsimp [R]; positivity) (by positivity))
    apply (div_le_iff₀ (by positivity : 0 < m / 2)).mpr
    dsimp [R]
    nlinarith
  have herr : L / (m / 2) ≤ q / 2 := by
    have hl := (div_le_iff₀ hq).mp hLm
    apply (div_le_iff₀ (by positivity : 0 < m / 2)).mpr
    nlinarith
  have hr : normSq (z - b) ≤ R ^ 2 := by
    have hs := Real.sq_sqrt (normSq_nonneg (z - b))
    have hn := Real.sqrt_nonneg (normSq (z - b))
    have hxR : Real.sqrt (normSq (z - b)) ≤ R := by dsimp [R]; nlinarith
    have hR0 : 0 ≤ R := by dsimp [R]; positivity
    simpa only [hs] using (sq_le_sq₀ hn hR0).mpr hxR
  have hp := hh (m / 2) R (3 * m / 4) (by linarith) hR (by linarith)
    (z - b) (by linarith) hr
  have hratio : (3 * m / 4) / (m / 2) = (3 / 2 : ℝ) := by
    field_simp
    <;> ring
  rw [hratio] at hp
  have hgap : q / (2 * d) ≤ (q - L / (m / 2)) / Real.log (R / (m / 2)) := by
    calc
      _ = (q / 2) / d := by ring
      _ ≤ (q / 2) / Real.log (R / (m / 2)) :=
        div_le_div_of_nonneg_left (by positivity) hden hdenmax
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hden.le
  have hKL : K ⊆ translateFinset b (diskFinset (m / 2)) := hK.trans
    (Finset.image_subset_image (diskFinset_mono a (m / 2) ha ham))
  have hLD : translateFinset b (diskFinset (m / 2)) ⊆
      translateFinset b (diskFinset R) := Finset.image_subset_image
    (diskFinset_mono (m / 2) R (by positivity) hR.le)
  have hmono := setHitProbability_mono_target (translateFinset b (diskFinset R))
    K (translateFinset b (diskFinset (m / 2))) hKL z
  have ht := setHitProbability_translate b (diskFinset R) (diskFinset (m / 2)) (z - b)
  rw [show b + (z - b) = z by abel] at ht
  rw [ht] at hmono
  rw [firstEntranceWordMarkLaw_none, competingExitMass_eq_one_sub_hit _ _ (hKL.trans hLD)]
  change setHitProbability (diskFinset R) (diskFinset (m / 2)) (z - b) ≤
    1 - (q - L / (m / 2)) / Real.log (R / (m / 2)) at hp
  linarith

end SRWTightness
