import SRWTightness.SourceGWLowerConditions

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

/-- The source lower tube with its closed terminal subwindow. -/
def sourceGWLowerTubeEvent (t : ℝ) (L : ℕ) (q : ℝ) : Set GeometricGWRecord :=
  gwTubeEvent L (Real.sqrt 2) (sourceTerminalRoot t q + 1 / 4) 4
    (sourceGWLowerEndpoint t) (1 / 2) 1 10 (1 / 10)

/-- All source-specific lower GW hypotheses are discharged; only the external estimate remains. -/
theorem source_gw_lower_tube_probability (hGW : GWBarrierLowerInput) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop, ∀ L : ℕ,
      (L : ℝ) = (sourceCoarseGeneration t : ℝ) →
      ∀ q : ℝ, Real.sqrt (sourceLowerTime (sourceLowerRadius t)) ≤ q →
        q ≤ 2 * Real.sqrt (sourceLowerTime (sourceLowerRadius t)) →
        let y := sourceTerminalRoot t q + 1 / 4
        c * gwBarrierPrefactor L (Real.sqrt 2) y 4 (sourceGWLowerEndpoint t) *
            min (Real.sqrt (Real.sqrt 2 / (y * L))) 1 ≤
          (geometricGWRecordLaw 1 L).real (sourceGWLowerTubeEvent t L q) := by
  obtain ⟨c, hc, hbound⟩ := hGW (1 / 2) 1 10 4 (1 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [source_gw_lower_conditions] with t ht
  intro L hL q hql hqu
  obtain ⟨hLn, hxL, hyl, hyL, hxa, hyb, hprod, hmax, hlat, htube⟩ := ht L hL q hql hqu
  have hh := hbound L 1 4 (sourceGWLowerEndpoint t) (sourceTerminalRoot t q + 1 / 4)
    hLn (by norm_num)
  simp only [Nat.cast_one, mul_one] at hh
  have hprob := hh hxL hyl hyL hxa hyb hprod hmax hlat (by
    intro j hj hjL
    simpa only [one_mul] using htube j hj hjL)
  exact hprob

end SRWTightness
