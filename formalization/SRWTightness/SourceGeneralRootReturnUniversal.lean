import SRWTightness.SourceRootReturnUniversal
import SRWTightness.SourceForestApplicationGeometry

namespace SRWTightness

/-- A fixed radius threshold gives the return bound at every root level. -/
theorem source_general_root_return_universal (hinput : PotentialKernelAsymptoticInput) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ (R m H : ℝ),
      0 < m → 8 ≤ H → 2 * H ≤ m → 32 * m ≤ R →
      let ℓ := sourceRootDepth R m
      A ≤ m - H →
      ∀ k : ℕ, k < ℓ → ∀ b x : Site, normSq b ≤ R ^ 2 → x ∈ diskFinset R →
      sourceRecordRadius m ℓ k + H ≤ Real.sqrt (normSq (x - b)) →
      setHitProbability (diskFinset R)
        (translateFinset b (diskFinset (sourceRecordRadius m ℓ (k + 1) - H))) x ≤
          1 - 1 / ((k : ℝ) + sourceRootReturnShift) := by
  obtain ⟨A, hA, hh⟩ := source_root_return_rate_universal hinput
  refine ⟨A, hA, ?_⟩
  intro R m H hm hH hhalf hscale
  dsimp only
  intro hlarge k hk b x hb hx hxc
  have hrad := sourceRecordRadius_ge_terminal m hm.le (sourceRootDepth R m) (k + 1)
    (by omega)
  have hmono := sourceRecordRadius_antitone m hm.le (sourceRootDepth R m)
    (Nat.zero_le (k + 1))
  have hbr := source_root_depth_bracket R m hm hscale
  exact hh R m H (sourceRootDepth R m) k hm (by linarith) hH (by linarith)
    hbr.2.le (by linarith) (by linarith [hbr.1]) b x hb hx hxc

end SRWTightness
