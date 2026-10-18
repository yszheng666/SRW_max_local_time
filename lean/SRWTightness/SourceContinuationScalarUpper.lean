import SRWTightness.ContinuationScalarUpper

open Filter MeasureTheory
namespace SRWTightness

/-- Source continuation windows have the normalized prefactor needed for terminal summation. -/
theorem source_continuation_scalar_upper (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (q : ℝ) (ν L k : ℕ),
      ν ≤ 2 * sourceCoarseLowerLevel t →
      (ν : ℝ) + (L : ℝ) = (sourceCoarseGeneration t : ℝ) → 0 < k →
      Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
      q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
      Real.sqrt (2 * (k : ℝ)) ≤ 4 + sourceBarrierSlope t * ν →
      (geometricGWRecordLaw k L).real (sourceContinuationWindow t ν L q) ≤
        C * ((ν : ℝ) + 1) * (1 + q) * Real.sqrt (Real.sqrt (2 * (k : ℝ))) / t ^ 2 *
          Real.exp (-((Real.sqrt (2 * (k : ℝ)) - sourceTerminalRoot t q) ^ 2 /
            (2 * (L : ℝ)))) := by
  obtain ⟨C, hC, hu⟩ := source_continuation_upper hGW
  refine ⟨C * 100, by positivity, ?_⟩
  filter_upwards [hu, source_continuation_remaining_time, source_deficit_large_conditions]
    with t hu htime ht
  intro q ν L k hν hN hk hq hq2 hx
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht.1).1
  have hL : t / 2 ≤ (L : ℝ) := by linarith [htime ν hν]
  have hy := sourceTerminalRoot_bounds t q ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hq hq2
  have hq0 : 0 ≤ q := (Real.sqrt_nonneg _).trans hq
  have hs := continuation_scalar_upper t (L : ℝ) (Real.sqrt (2 * (k : ℝ)))
    (sourceTerminalRoot t q) q (ν : ℝ) (sourceBarrierSlope t)
    (by linarith) hL hy.1 hq0 (Nat.cast_nonneg _)
    (sourceBarrierSlope_bounds t ht.1 ht.2.1).2 (Real.sqrt_nonneg _) hx
  have hmargin : 1 + (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) -
      sourceTerminalRoot t q = 5 + q := by unfold sourceTerminalRoot; ring
  have hbound := hu q ν L k hν hN hk hq hq2 hx
  unfold gwBarrierPrefactor at hbound
  rw [hmargin] at hbound
  have he : 1 + (4 + sourceBarrierSlope t * ν) - Real.sqrt (2 * (k : ℝ)) =
      5 + sourceBarrierSlope t * ν - Real.sqrt (2 * (k : ℝ)) := by ring
  rw [he] at hbound
  have hs' := mul_le_mul_of_nonneg_left hs hC.le
  calc
    _ ≤ C * (((5 + sourceBarrierSlope t * ν - Real.sqrt (2 * (k : ℝ))) * (5 + q) /
        (L : ℝ)) * Real.exp (-((Real.sqrt (2 * (k : ℝ)) - sourceTerminalRoot t q) ^ 2 /
        (2 * (L : ℝ)))) * Real.sqrt (Real.sqrt (2 * (k : ℝ)) /
        (sourceTerminalRoot t q * L))) := by simpa only [mul_assoc] using hbound
    _ ≤ C * (100 * ((ν : ℝ) + 1) * (1 + q) * Real.sqrt (Real.sqrt (2 * (k : ℝ))) /
        t ^ 2 * Real.exp (-((Real.sqrt (2 * (k : ℝ)) - sourceTerminalRoot t q) ^ 2 /
        (2 * (L : ℝ))))) := hs'
    _ = _ := by ring

end SRWTightness
