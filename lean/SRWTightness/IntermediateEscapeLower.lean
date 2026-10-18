import SRWTightness.SourceAnnulusFormula
import SRWTightness.HitTargetMonotonicity
import SRWTightness.DiskCapacityLogBound

namespace SRWTightness

/-- Avoiding the enclosing inner ball gives a uniform escape lower bound beyond radius 3a/2. -/
theorem intermediate_escape_lower (hinput : PotentialKernelAsymptoticInput) :
    ∃ c T : ℝ, 0 < c ∧ 2 ≤ T ∧ ∀ (a R : ℝ), T ≤ a → a < R →
      ∀ (b x : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        3 * a / 2 ≤ Real.sqrt (normSq (x - b)) → normSq (x - b) < R ^ 2 →
        c / Real.log (R / a) ≤
          1 - setHitProbability (translateFinset b (diskFinset R)) K x := by
  obtain ⟨B, a₀, hB, ha₀, hh⟩ := source_annulus_probability_formula hinput
  let ℓ : ℝ := Real.log (3 / 2 : ℝ)
  have hℓ : 0 < ℓ := Real.log_pos (by norm_num)
  let T := a₀ + 2 * B / ℓ
  refine ⟨ℓ / 2, T, by positivity, by
    have hn : 0 ≤ 2 * B / ℓ := by positivity
    dsimp [T]
    linarith, ?_⟩
  intro a R ha hR b x K hK hxl hxu
  have ha₀a : a₀ ≤ a := by
    have hn : 0 ≤ 2 * B / ℓ := by positivity
    dsimp [T] at ha
    linarith
  have ha0 : 0 < a := by linarith
  have hBa : B / a ≤ ℓ / 2 := by
    have ht : 2 * B / ℓ ≤ a := by dsimp [T] at ha; linarith
    have he := (div_le_iff₀ hℓ).mp ht
    apply (div_le_iff₀ ha0).mpr
    nlinarith
  have hinner : a ^ 2 < normSq (x - b) := by
    have hs := Real.sq_sqrt (normSq_nonneg (x - b))
    nlinarith
  obtain ⟨ε, hε, hp⟩ := hh a R ha₀a hR b x hinner hxu
  have hlog : ℓ ≤ Real.log (Real.sqrt (normSq (x - b)) / a) := by
    apply Real.log_le_log (by norm_num : (0 : ℝ) < 3 / 2)
    apply (le_div_iff₀ ha0).mpr
    linarith
  have hden : 0 < Real.log (R / a) := Real.log_pos ((one_lt_div ha0).mpr hR)
  have hnum : ℓ / 2 ≤ Real.log (Real.sqrt (normSq (x - b)) / a) + ε := by
    have he := (abs_le.mp hε).1
    linarith
  have hball : translateFinset b (diskFinset a) ⊆ translateFinset b (diskFinset R) :=
    Finset.image_subset_image (diskFinset_mono a R ha0.le hR.le)
  rw [exit_before_hit_probability _ _ hball x] at hp
  have hm := setHitProbability_mono_target (translateFinset b (diskFinset R)) K
    (translateFinset b (diskFinset a)) hK x
  have hl := div_le_div_of_nonneg_right hnum hden.le
  rw [← hp] at hl
  linarith

end SRWTightness
