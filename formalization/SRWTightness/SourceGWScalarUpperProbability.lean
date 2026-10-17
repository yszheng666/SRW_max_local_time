import SRWTightness.SourceGWCoarseUpperProbability
import SRWTightness.GWScalarUpper
import SRWTightness.SourceGWScalarConditions

open MeasureTheory Filter

namespace SRWTightness

/-- The normalized coarse-window upper bound uses only the upper GW input. -/
theorem source_gw_scalar_upper_probability (hUpper : GWBarrierUpperInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        (geometricGWRecordLaw 1 L).real (sourceGWCoarseWindowEvent t L q) ≤
          C * ((1 + q) / (L : ℝ) ^ 2 *
            Real.exp (-(sourceTerminalRoot t q ^ 2 / (2 * (L : ℝ))))) := by
  obtain ⟨C, hC, hhi⟩ := source_gw_coarse_upper_probability hUpper
  refine ⟨C * (40 * Real.exp 8), by positivity, ?_⟩
  have hx0 := Real.sqrt_nonneg (2 : ℝ)
  have hxsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hx1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hx2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  filter_upwards [hhi, source_gw_scalar_conditions] with t hhi hs
  dsimp only
  intro q hql hqu
  let L := (sourceCoarseGeneration t).toNat
  let u := sourceTerminalRoot t q
  obtain ⟨hL, hu, hyL, hLu, hq, hm⟩ := hs q hql hqu
  have hsu := gw_scalar_upper (L : ℝ) (Real.sqrt 2) u q hL hx1 hx2 hLu
    (by linarith) hq
  have hpu := hhi q hql hqu
  have hmargin : 1 + (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) - u =
      5 + q := by dsimp [u, sourceTerminalRoot]; ring
  have hfactor : gwBarrierPrefactor L (Real.sqrt 2) u 4
      (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) =
      ((5 - Real.sqrt 2) * (5 + q) / (L : ℝ)) *
        Real.exp (-((Real.sqrt 2 - u) ^ 2 / (2 * (L : ℝ)))) := by
    unfold gwBarrierPrefactor
    rw [hmargin]
    norm_num
  calc
    _ ≤ C * gwBarrierPrefactor L (Real.sqrt 2) u 4
        (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) *
        Real.sqrt (Real.sqrt 2 / (u * L)) := hpu
    _ = C * ((((5 - Real.sqrt 2) * (5 + q) / (L : ℝ)) *
        Real.exp (-((Real.sqrt 2 - u) ^ 2 / (2 * (L : ℝ))))) *
        Real.sqrt (Real.sqrt 2 / (u * L))) := by rw [hfactor]; ring
    _ ≤ C * ((40 * Real.exp 8) *
        ((1 + q) / (L : ℝ) ^ 2 * Real.exp (-(u ^ 2 / (2 * (L : ℝ)))))) :=
      mul_le_mul_of_nonneg_left hsu hC.le
    _ = _ := by ring

end SRWTightness
