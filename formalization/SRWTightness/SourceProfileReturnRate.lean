import SRWTightness.SourceReturnErrorSmall
import SRWTightness.SourceRootDepthTime
import SRWTightness.SourceExcursionDomains

namespace SRWTightness

/-- The actual H=14 source profile satisfies the reciprocal-level return bound uniformly. -/
theorem source_profile_return_rate (hinput : PotentialKernelAsymptoticInput) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ R : ℝ,
      32 * sourceLowerRadius t ≤ R → R ≤ Real.exp t →
      let ℓ := sourceRootDepth R (sourceLowerRadius t)
      ∀ k : ℕ, k < ℓ → ∀ b x : Site, normSq b ≤ R ^ 2 → x ∈ diskFinset R →
      sourceRecordRadius (sourceLowerRadius t) ℓ k + 14 ≤ Real.sqrt (normSq (x - b)) →
      setHitProbability (diskFinset R) (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b k) x ≤
        1 - 1 / ((k : ℝ) + sourceRootReturnShift) := by
  obtain ⟨K, A, hK, hA, hh⟩ := source_root_return_rate hinput
  obtain ⟨T, hsmall⟩ := source_return_error_small K A hK
  refine ⟨max T (sourceScaleThreshold 4), ?_⟩
  intro t ht R hscale htime
  dsimp only
  intro k hk b x hb hx hxc
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_right _ _).trans ht
  have hm := sourceLowerRadius_pos t
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).2.2.1
  have hR : 0 < R := by linarith
  have hdepth := source_root_depth_le_time R (sourceLowerRadius t) t hm hscale (by linarith) htime
  have hkt : (k : ℝ) ≤ t := (Nat.cast_le.mpr hk.le).trans hdepth
  have hs := hsmall t htT k hkt
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) hm.le
    (sourceRootDepth R (sourceLowerRadius t)) (k + 1) (by omega)
  have hbr := source_root_depth_bracket R (sourceLowerRadius t) hm hscale
  have hmono := sourceRecordRadius_antitone (sourceLowerRadius t) hm.le
    (sourceRootDepth R (sourceLowerRadius t)) (Nat.zero_le (k + 1))
  have hreturn := hh R (sourceLowerRadius t) 14 (sourceRootDepth R (sourceLowerRadius t)) k
    hm hR (by norm_num) (by linarith) hbr.2.le (by linarith) (by linarith)
    (by linarith) b x hb hx hxc
  simpa only [sourceEntranceDomain, sourceRecordBuffer, show (4 : ℝ) * 1 + 10 = 14 by norm_num]
    using hreturn

end SRWTightness
