import SRWTightness.SourceRootReturnRate
import SRWTightness.DiskRootUniversalReturnBound
import SRWTightness.BufferedLogSurplus

namespace SRWTightness

/-- The buffer absorbs the numerator error in the reciprocal-level root return rate. -/
theorem source_root_return_rate_universal (hinput : PotentialKernelAsymptoticInput) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ (R m H : ℝ) (ℓ k : ℕ),
      0 < m → 0 < R → 8 ≤ H → 2 * H ≤ sourceRecordRadius m ℓ (k + 1) →
      R ≤ 32 * Real.exp 1 * sourceRecordRadius m ℓ 0 →
      A ≤ sourceRecordRadius m ℓ (k + 1) - H →
      sourceRecordRadius m ℓ (k + 1) - H < 2 * R →
      ∀ b x : Site, normSq b ≤ R ^ 2 → x ∈ diskFinset R →
      sourceRecordRadius m ℓ k + H ≤ Real.sqrt (normSq (x - b)) →
      setHitProbability (diskFinset R)
        (translateFinset b (diskFinset (sourceRecordRadius m ℓ (k + 1) - H))) x ≤
          1 - 1 / ((k : ℝ) + sourceRootReturnShift) := by
  obtain ⟨A, hA, hh⟩ := disk_root_universal_return_bound hinput
  refine ⟨A, hA, ?_⟩
  intro R m H ℓ k hm hR hH hhalf houter hthreshold hRa b x hb hx hxc
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
  have hn : 1 + 4 / a ≤ Real.log (c / a) := by
    apply buffered_log_surplus a H c ha hH (by dsimp [a]; linarith)
    dsimp [a, c]
    rw [← sourceRecordRadius_successor m ℓ k]
    nlinarith [Real.exp_pos (1 : ℝ)]
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
  have hg : 1 / (v + 1) ≤ 1 / Real.log (2 * R / a) :=
    one_div_le_one_div_of_le hd (by linarith)
  have hg' : 1 / (v + 1) ≤ (Real.log (c / a) - 4 / a) / Real.log (2 * R / a) :=
    hg.trans (div_le_div_of_nonneg_right (by linarith) hd.le)
  have hv1 : v + 1 = (k : ℝ) + sourceRootReturnShift := by dsimp [v]; ring
  rw [hv1] at hg'
  linarith

end SRWTightness
