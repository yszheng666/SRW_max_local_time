import SRWTightness.SourceGWUpperEvent

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Upper GW input applied to the actual complete source coarse-window event. -/
theorem source_gw_coarse_upper_probability (hGW : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let u := sourceTerminalRoot t q
        (geometricGWRecordLaw 1 L).real (sourceGWCoarseWindowEvent t L q) ≤
          C * gwBarrierPrefactor L (Real.sqrt 2) u 4
            (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) *
            Real.sqrt (Real.sqrt 2 / (u * L)) := by
  obtain ⟨C, hC, hb⟩ := hGW 1 1 4 (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  filter_upwards [source_gw_lower_conditions, source_gw_natural_generation,
    source_deficit_large_conditions, source_gw_coarse_subset_upper] with t hc hN ht hsub
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  dsimp only
  intro q hql hqu
  let L := (sourceCoarseGeneration t).toNat
  obtain ⟨hLn, hxL, hyl, hyL, hxa, hyb, hprod, hmax, hlat, htube⟩ := hc L hN.1 q hql hqu
  have hu := sourceTerminalRoot_bounds t q ht htE hdsmall hlog hql hqu
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hx0 := Real.sqrt_nonneg (2 : ℝ)
  have hxsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hul : Real.sqrt 2 ≤ sourceTerminalRoot t q := by nlinarith [hu.1]
  have huh : sourceTerminalRoot t q ≤ 4 * L := by linarith
  have hub : sourceTerminalRoot t q ≤
      4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ) := by
    unfold sourceTerminalRoot
    linarith [Real.sqrt_nonneg (sourceLowerTime (sourceLowerRadius t))]
  have hh := hb L 1 4
    (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ))
    (sourceTerminalRoot t q) hLn (by norm_num)
  simp only [Nat.cast_one, mul_one] at hh
  exact (measureReal_mono (hsub q)).trans (hh hxL hul huh hxa hub)

end SRWTightness
