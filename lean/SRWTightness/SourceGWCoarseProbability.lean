import SRWTightness.GWScalarLower
import SRWTightness.GWScalarUpper
import SRWTightness.SourceGWScalarConditions

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- Manuscript (7.24): two-sided source coarse-window probability on the actual geometric GW law. -/
theorem source_gw_coarse_probability (hLower : GWBarrierLowerInput) (hUpper : GWBarrierUpperInput) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ t : ℝ in atTop,
      let L := (sourceCoarseGeneration t).toNat
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let u := sourceTerminalRoot t q
        let w := (1 + q) / (L : ℝ) ^ 2 * Real.exp (-(u ^ 2 / (2 * (L : ℝ))))
        c * w ≤ (geometricGWRecordLaw 1 L).real (sourceGWCoarseWindowEvent t L q) ∧
          (geometricGWRecordLaw 1 L).real (sourceGWCoarseWindowEvent t L q) ≤ C * w := by
  obtain ⟨c, hc, hlo⟩ := source_gw_coarse_lower_probability hLower
  obtain ⟨C, hC, hhi⟩ := source_gw_coarse_upper_probability hUpper
  refine ⟨c / 2, C * (40 * Real.exp 8), by positivity, by positivity, ?_⟩
  have hx0 := Real.sqrt_nonneg (2 : ℝ)
  have hxsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hx1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hx2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  filter_upwards [hlo, hhi, source_gw_scalar_conditions] with t hlo hhi hs
  dsimp only
  intro q hql hqu
  let L := (sourceCoarseGeneration t).toNat
  let u := sourceTerminalRoot t q
  let b := sourceGWLowerEndpoint t
  obtain ⟨hL, hu, hyL, hLu, hq, hm⟩ := hs q hql hqu
  have hsl := gw_scalar_lower (L : ℝ) (Real.sqrt 2) u b q hL hx1 hx2 hu hyL hq hm
  have hsu := gw_scalar_upper (L : ℝ) (Real.sqrt 2) u q hL hx1 hx2 hLu
    (by linarith) hq
  have hpl := hlo q hql hqu
  have hpu := hhi q hql hqu
  have hlowfactor : gwBarrierPrefactor L (Real.sqrt 2) (u + 1 / 4) 4 b =
      ((5 - Real.sqrt 2) * (1 + b - (u + 1 / 4)) / (L : ℝ)) *
        Real.exp (-((Real.sqrt 2 - (u + 1 / 4)) ^ 2 / (2 * (L : ℝ)))) := by
    unfold gwBarrierPrefactor
    norm_num
  have hmargin : 1 + (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) - u =
      5 + q := by
    dsimp [u, sourceTerminalRoot]
    ring
  have hupperfactor : gwBarrierPrefactor L (Real.sqrt 2) u 4
      (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) =
      ((5 - Real.sqrt 2) * (5 + q) / (L : ℝ)) *
        Real.exp (-((Real.sqrt 2 - u) ^ 2 / (2 * (L : ℝ)))) := by
    unfold gwBarrierPrefactor
    rw [hmargin]
    norm_num
  constructor
  · calc
      _ = c * ((1 + q) / (2 * (L : ℝ) ^ 2) * Real.exp (-(u ^ 2 / (2 * (L : ℝ))))) := by
        ring
      _ ≤ c * ((((5 - Real.sqrt 2) * (1 + b - (u + 1 / 4)) / (L : ℝ)) *
          Real.exp (-((Real.sqrt 2 - (u + 1 / 4)) ^ 2 / (2 * (L : ℝ))))) *
          min (Real.sqrt (Real.sqrt 2 / ((u + 1 / 4) * L))) 1) :=
        mul_le_mul_of_nonneg_left hsl hc.le
      _ = c * gwBarrierPrefactor L (Real.sqrt 2) (u + 1 / 4) 4 b *
          min (Real.sqrt (Real.sqrt 2 / ((u + 1 / 4) * L))) 1 := by
        rw [hlowfactor]
        ring
      _ ≤ _ := hpl
  · calc
      _ ≤ C * gwBarrierPrefactor L (Real.sqrt 2) u 4
          (4 + sourceBarrierSlope t * (sourceCoarseGeneration t : ℝ)) *
          Real.sqrt (Real.sqrt 2 / (u * L)) := hpu
      _ = C * ((((5 - Real.sqrt 2) * (5 + q) / (L : ℝ)) *
          Real.exp (-((Real.sqrt 2 - u) ^ 2 / (2 * (L : ℝ))))) *
          Real.sqrt (Real.sqrt 2 / (u * L))) := by
        rw [hupperfactor]
        ring
      _ ≤ C * ((40 * Real.exp 8) *
          ((1 + q) / (L : ℝ) ^ 2 * Real.exp (-(u ^ 2 / (2 * (L : ℝ)))))) :=
        mul_le_mul_of_nonneg_left hsu hC.le
      _ = _ := by ring

end SRWTightness
