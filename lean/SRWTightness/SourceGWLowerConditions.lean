import SRWTightness.SourceGWEndpointMargins
import SRWTightness.SourceGWTerminalLattice

open Filter
open scoped Topology

namespace SRWTightness

/-- All nonconstant hypotheses for the source application of the external lower GW estimate. -/
def SourceGWLowerConditions (t : ℝ) (L : ℕ) (q : ℝ) : Prop :=
  let x := Real.sqrt 2
  let y := sourceTerminalRoot t q + 1 / 4
  let b := sourceGWLowerEndpoint t
  0 < L ∧ x ≤ 4 * L ∧ Real.sqrt 2 ≤ y ∧ y ≤ 4 * L ∧ x ≤ 4 ∧ y ≤ b ∧
    (1 + 4 - x) * (1 + b - y) ≤ 4 * L ∧
    (L : ℝ) / 4 ≤ max (x * y) |y - x| ∧
    gwPositiveLatticeIntersects y (y + 1 / 2) ∧
    ∀ j : ℕ, 0 < j → j < L → gwPositiveLatticeIntersects
      (gwBarrierLine x y j L - 10 * gwBarrierCurvature (1 / 2 + 1 / 10) j L)
      (gwBarrierLine 4 b j L - gwBarrierCurvature (1 / 2 - 1 / 10) j L)

/-- The actual source deficit band satisfies every parameter and lattice hypothesis of the lower input. -/
theorem source_gw_lower_conditions :
    ∀ᶠ t : ℝ in atTop, ∀ L : ℕ, (L : ℝ) = (sourceCoarseGeneration t : ℝ) →
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        SourceGWLowerConditions t L q := by
  filter_upwards [source_deficit_large_conditions, source_gw_endpoint_margins,
    source_gw_terminal_lattice, source_gw_tube_upper] with t ht hm hlat htube
  obtain ⟨ht, htE, hdsmall, hlog⟩ := ht
  have ht2 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht).1
  have hd := sourceLowerTime_ge_one t ht
  have hT := sourceTotalTime_ge_half t ht htE
  have hTerr := (abs_le.mp (sourceTotalTime_error t ht)).2
  unfold sourceTotalTime at hT hTerr
  have hN : 5 * sourceLowerTime (sourceLowerRadius t) ≤
      (sourceCoarseGeneration t : ℝ) := by linarith
  have hs := sourceBarrierSlope_bounds t ht htE
  have hx0 := Real.sqrt_nonneg (2 : ℝ)
  have hxsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hx1 : (1 : ℝ) ≤ Real.sqrt 2 := by nlinarith
  have hx2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  intro L hL q hql hqu
  have hL0 : (0 : ℝ) < L := by rw [hL]; linarith
  have hLn : 0 < L := by exact_mod_cast hL0
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hLn
  have hu := sourceTerminalRoot_bounds t q ht htE hdsmall hlog hql hqu
  have hm' := hm q hql hqu
  have hylo : Real.sqrt 2 ≤ sourceTerminalRoot t q + 1 / 4 := by linarith [hu.1]
  have hq1 : 1 ≤ q := by
    have hh := Real.sq_sqrt (show 0 ≤ sourceLowerTime (sourceLowerRadius t) by linarith)
    have hh0 := Real.sqrt_nonneg (sourceLowerTime (sourceLowerRadius t))
    nlinarith
  have hyhi : sourceTerminalRoot t q + 1 / 4 ≤ 4 * L := by
    unfold sourceTerminalRoot
    rw [← hL]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) hL0.le]
  have hxy : (L : ℝ) / 4 ≤ Real.sqrt 2 * (sourceTerminalRoot t q + 1 / 4) := by
    rw [hL]
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1)
      (show 0 ≤ sourceTerminalRoot t q + 1 / 4 by linarith [hu.1])]
  have hlat' := (hlat q hql hqu).1
  have hend : sourceTerminalRoot t q + 1 / 4 + 1 / 2 =
      sourceTerminalRoot t q + 3 / 4 := by ring
  refine ⟨hLn, by nlinarith, hylo, hyhi, by linarith, hm'.1, ?_,
    hxy.trans (le_max_left _ _), ?_, ?_⟩
  · rw [hL]
    exact hm'.2.2.2
  · rw [hend]
    exact hlat'
  · intro j hj hjL
    apply gw_tube_lattice_of_upper L j hj hjL (Real.sqrt 2)
      (sourceTerminalRoot t q + 1 / 4) 4 (sourceGWLowerEndpoint t) (by linarith) hm'.1
    have hh := htube L hL j hj hjL
    simpa only [sourceGWLowerEndpoint, hL] using hh

end SRWTightness
