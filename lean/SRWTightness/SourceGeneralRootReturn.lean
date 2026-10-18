import SRWTightness.SourceRootReturnRate
import SRWTightness.SourceForestApplicationGeometry

namespace SRWTightness

/-- One explicit depth-dependent separation condition gives the return bound at every root level. -/
theorem source_general_root_return (hinput : PotentialKernelAsymptoticInput) :
    ∃ K A : ℝ, 0 ≤ K ∧ 2 ≤ A ∧ ∀ (R m H : ℝ),
      0 < m → 0 ≤ H → 2 * H ≤ m → 32 * m ≤ R →
      let ℓ := sourceRootDepth R m
      A + K * ((ℓ : ℝ) + sourceRootReturnShift) ≤ m - H →
      ∀ k : ℕ, k < ℓ → ∀ b x : Site, normSq b ≤ R ^ 2 → x ∈ diskFinset R →
      sourceRecordRadius m ℓ k + H ≤ Real.sqrt (normSq (x - b)) →
      setHitProbability (diskFinset R)
        (translateFinset b (diskFinset (sourceRecordRadius m ℓ (k + 1) - H))) x ≤
          1 - 1 / ((k : ℝ) + sourceRootReturnShift) := by
  obtain ⟨K, A, hK, hA, hh⟩ := source_root_return_rate hinput
  refine ⟨K, A, hK, hA, ?_⟩
  intro R m H hm hH hhalf hscale
  dsimp only
  intro hlarge k hk b x hb hx hxc
  have hC : 0 < sourceRootReturnShift := by
    have h32 := Real.log_nonneg (show (1 : ℝ) ≤ 32 by norm_num)
    have h2 := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    dsimp [sourceRootReturnShift]
    linarith
  have hKdepth : 0 ≤ K * ((sourceRootDepth R m : ℝ) + sourceRootReturnShift) := by
    positivity
  have hAsep : A ≤ m - H := by linarith
  have hkle : (k : ℝ) ≤ sourceRootDepth R m := Nat.cast_le.mpr hk.le
  have hsmall : K * ((k : ℝ) + sourceRootReturnShift) ≤ m - H := by
    have hmul := mul_le_mul_of_nonneg_left (add_le_add_right hkle sourceRootReturnShift) hK
    linarith
  have hrad := sourceRecordRadius_ge_terminal m hm.le (sourceRootDepth R m) (k + 1)
    (by omega)
  have hmono := sourceRecordRadius_antitone m hm.le (sourceRootDepth R m)
    (Nat.zero_le (k + 1))
  have hbr := source_root_depth_bracket R m hm hscale
  exact hh R m H (sourceRootDepth R m) k hm (by linarith) hH (by linarith)
    hbr.2.le (by linarith) (by linarith [hbr.1]) (by linarith) b x hb hx hxc

end SRWTightness
