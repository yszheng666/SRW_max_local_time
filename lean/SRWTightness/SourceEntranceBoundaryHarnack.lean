import SRWTightness.AnnularFrameEntrance
import SRWTightness.SourceEntranceFrameGeometry

open MeasureTheory
namespace SRWTightness

/-- All actual terminal entrance atoms are uniformly comparable throughout the entrance layer. -/
theorem source_entrance_boundary_harnack (hinput : PositiveHarmonicRelativeInput) :
    ∃ C T : ℝ, 0 < C ∧ 128 ≤ T ∧ ∀ (m H a : ℝ), T ≤ m →
      0 ≤ H → H ≤ m / 8 → 0 ≤ a → a ≤ m / 2 →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ (v : Site), v ∈ K → ∀ z y : Site,
      m - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ m - H + 1 →
      m - H - 1 ≤ Real.sqrt (normSq (y - b)) →
      Real.sqrt (normSq (y - b)) ≤ m - H + 1 →
      Real.exp (-C) *
          (competingEntranceLaw
            (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real {v} ≤
        (competingEntranceLaw
            (translateFinset b (diskFinset (Real.exp 1 * m + H))) K y).real {v} ∧
      (competingEntranceLaw
            (translateFinset b (diskFinset (Real.exp 1 * m + H))) K y).real {v} ≤
        Real.exp C *
          (competingEntranceLaw
            (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real {v} := by
  obtain ⟨C, hC, hh⟩ := annular_frame_entrance hinput
  refine ⟨400 * C, max 128 (32 * C), by positivity, le_max_left _ _, ?_⟩
  intro m H a hm hH hHm ha ham b K hK v hv z y hzlo hzhi hylo hyhi
  have hm128 : 128 ≤ m := (le_max_left _ _).trans hm
  have hCm : 32 * C ≤ m := (le_max_right _ _).trans hm
  obtain ⟨M, hmM, hMm, hframe⟩ := source_entrance_frame_geometry m H hm128 hH hHm
  have hz := hframe (z - b) hzlo hzhi
  have hy := hframe (y - b) hylo hyhi
  have hexp : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp := hh m a (Real.exp 1 * m + H) hm128 hCm ha ham (by nlinarith)
    M hmM hMm b K hK v hv (z - b) (y - b)
    hz.1 hz.2.1 hy.1 hy.2.1 hz.2.2 hy.2.2
  simpa only [show b + (z - b) = z by abel,
    show b + (y - b) = y by abel] using hp

end SRWTightness
