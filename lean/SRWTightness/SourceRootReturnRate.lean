import SRWTightness.SourceRootLogDenominator
import SRWTightness.ReturnGapReciprocal
import SRWTightness.DiskRootFineReturnBound

namespace SRWTightness

/-- Fixed additive shift in the source-level return decay. -/
noncomputable def sourceRootReturnShift : ℝ := Real.log 32 + 2 * Real.log 2 + 3

/-- The source root has the required reciprocal-level return rate once its numerator error is small. -/
theorem source_root_return_rate (hinput : PotentialKernelAsymptoticInput) :
    ∃ K A : ℝ, 0 ≤ K ∧ 2 ≤ A ∧ ∀ (R m H : ℝ) (ℓ k : ℕ),
      0 < m → 0 < R → 0 ≤ H → 2 * H ≤ sourceRecordRadius m ℓ (k + 1) →
      R ≤ 32 * Real.exp 1 * sourceRecordRadius m ℓ 0 →
      A ≤ sourceRecordRadius m ℓ (k + 1) - H →
      sourceRecordRadius m ℓ (k + 1) - H < 2 * R →
      K * ((k : ℝ) + sourceRootReturnShift) ≤ sourceRecordRadius m ℓ (k + 1) - H →
      ∀ b x : Site, normSq b ≤ R ^ 2 → x ∈ diskFinset R →
      sourceRecordRadius m ℓ k + H ≤ Real.sqrt (normSq (x - b)) →
      setHitProbability (diskFinset R)
        (translateFinset b (diskFinset (sourceRecordRadius m ℓ (k + 1) - H))) x ≤
          1 - 1 / ((k : ℝ) + sourceRootReturnShift) := by
  obtain ⟨K, A, hK, hA, hh⟩ := disk_root_fine_return_bound hinput
  refine ⟨K, A, hK, hA, ?_⟩
  intro R m H ℓ k hm hR hH hhalf houter hthreshold hRa hsmall b x hb hx hxc
  let a := sourceRecordRadius m ℓ (k + 1) - H
  let c := sourceRecordRadius m ℓ k + H
  have ha : 0 < a := by dsimp [a]; linarith
  have he : Real.exp 1 * a ≤ c := by
    dsimp [a, c]
    rw [← sourceRecordRadius_successor m ℓ k]
    nlinarith [Real.exp_pos (1 : ℝ)]
  have hexp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hac : a ≤ c := by nlinarith
  have hp := hh a R c hthreshold hRa hac b x hb hx hxc
  have hn : 1 ≤ Real.log (c / a) := by
    have hl := Real.log_le_log (Real.exp_pos 1) ((le_div_iff₀ ha).mpr he)
    simpa only [Real.log_exp] using hl
  have hd : 0 < Real.log (2 * R / a) := Real.log_pos ((one_lt_div ha).mpr hRa)
  let v := (k : ℝ) + sourceRootReturnShift - 1
  have hv : 0 ≤ v := by
    have h32 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 32)
    have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    dsimp [v, sourceRootReturnShift]
    linarith
  have hden : Real.log (2 * R / a) ≤ v := by
    have ht := source_root_log_denominator R m H ℓ k hm hR hhalf houter
    dsimp [v, sourceRootReturnShift, a]
    linarith
  have hs : K * (v + 1) ≤ a := by simpa only [v, sub_add_cancel, a] using hsmall
  have hg := return_gap_reciprocal K a (Real.log (2 * R / a)) v ha hd hv hden hs
  have hg' : 1 / (v + 1) ≤ (Real.log (c / a) - K / a) / Real.log (2 * R / a) :=
    hg.trans (div_le_div_of_nonneg_right (by linarith) hd.le)
  have hv1 : v + 1 = (k : ℝ) + sourceRootReturnShift := by dsimp [v]; ring
  rw [hv1] at hg'
  linarith

end SRWTightness
