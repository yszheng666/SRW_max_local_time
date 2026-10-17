import SRWTightness.ExternalKilledExitDecomposition
import SRWTightness.MaximumPrinciple

open MeasureTheory

namespace SRWTightness

/-- Every finite-domain boundary payoff is additive, since its actual exit range is finite. -/
theorem exit_payoff_add (D : Finset Site) (f g : Site → ℝ) (x : Site) :
    exitPayoff D (fun y ↦ f y + g y) x = exitPayoff D f x + exitPayoff D g x :=
  integral_add (integrable_domainExit_payoff D x f) (integrable_domainExit_payoff D x g)

/-- Integrating the actual competing entrance law is its inner-set indicator boundary payoff. -/
theorem integral_competing_entrance_eq_payoff (D K : Finset Site) (x : Site) (f : Site → ℝ) :
    (∫ y, f y ∂competingEntranceLaw D K x) =
      exitPayoff (D \ K) (fun y ↦ if y ∈ K then f y else 0) x := by
  classical
  unfold competingEntranceLaw exitPayoff
  rw [← integral_indicator (Finset.measurableSet K)]
  simpa only [Set.indicator, Finset.mem_coe] using
    (integral_map (measurable_domainExitLocation (D \ K) x).aemeasurable
      (measurable_of_countable ((K : Set Site).indicator f)).aestronglyMeasurable)

/-- The actual parent exit atom decomposes into direct exit and the competing inner entrance law. -/
theorem trace_exit_competing_decomposition_internal (D K : Finset Site) (hKD : K ⊆ D)
    (x e : Site) (he : e ∉ D) :
    traceExitProbability D x e = traceExitProbability (D \ K) x e +
      ∫ y, traceExitProbability D y e ∂competingEntranceLaw D K x := by
  classical
  let f : Site → ℝ := fun y ↦ traceExitProbability D y e
  have hh : f x = exitPayoff (D \ K) f x := by
    apply harmonic_eq_exitPayoff
    intro y hy
    exact trace_exit_probability_harmonic D e y (Finset.mem_sdiff.mp hy).1
  have hb : exitPayoff (D \ K) f x = exitPayoff (D \ K)
      (fun y ↦ (if y = e then 1 else 0) + (if y ∈ K then f y else 0)) x := by
    apply exitPayoff_congr_on_compl
    intro y hy
    by_cases hK : y ∈ K
    · have hne : y ≠ e := fun h ↦ he (h ▸ hKD hK)
      simp only [hK, hne, if_true, if_false, zero_add]
    · have hD : y ∉ D := fun h ↦ hy (Finset.mem_sdiff.mpr ⟨h, hK⟩)
      change traceExitProbability D y e = _
      rw [trace_exit_probability_eq_payoff, exitPayoff_eq_of_not_mem D _ y hD]
      simp only [if_neg hK, add_zero]
  calc
    _ = exitPayoff (D \ K) f x := hh
    _ = _ := hb.trans (by
      rw [exit_payoff_add, ← trace_exit_probability_eq_payoff,
        ← integral_competing_entrance_eq_payoff])

end SRWTightness
