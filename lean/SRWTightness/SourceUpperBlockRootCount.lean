import SRWTightness.SourceUpperBlockReturn
import SRWTightness.SourceUpperBlockDomainGeometry

open Filter MeasureTheory

namespace SRWTightness

/-- Actual complete root excursions for a selected source upper block. -/
noncomputable def sourceUpperBlockRootCount (t : ℝ) (b : Site) (ω : Sample) : ℕ :=
  (killedChildIntervals (diskFinset (Real.exp t))
    (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b)
    (sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b) 0 ω).length

/-- The actual block root count has the exponential tail with all geometric inputs supplied. -/
theorem source_upper_block_root_count_tail (hinput : PotentialKernelAsymptoticInput) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t, ∀ n : ℕ,
      pathLaw.real {ω | n + 1 ≤ sourceUpperBlockRootCount t b ω} ≤
        Real.exp (-(n : ℝ) / ((sourceUpperBlockRoot t b : ℝ) + K)) := by
  obtain ⟨K, hK, hreturn⟩ := source_upper_selected_root_return_rate hinput
  refine ⟨K, hK, ?_⟩
  filter_upwards [hreturn, source_upper_block_domain_geometry,
    source_upper_block_root_coarse_range] with t hr hg hk
  intro b hb n
  have hgeom := hg (sourceUpperBlockRoot t b) (hk b hb) b hb
  have h := killedChildIntervals_count_exp_tail (diskFinset (Real.exp t))
    (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b)
    (sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b) hgeom.1 hgeom.2
    ((sourceUpperBlockRoot t b : ℝ) + K) (hr b hb) n 0
  have hp : setHitProbability (diskFinset (Real.exp t))
      (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b) 0 ≤ 1 := by
    rw [setHitProbability_eq_probability]
    exact measureReal_le_one
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)

end SRWTightness
