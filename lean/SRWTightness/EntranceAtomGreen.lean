import SRWTightness.CompetingEntranceLaw
import SRWTightness.PoissonBoundary

open MeasureTheory

namespace SRWTightness

/-- An actual entrance atom is the singleton payoff at exit from the punctured domain. -/
theorem competingEntranceLaw_atom_payoff (D K : Finset Site) (x v : Site) (hv : v ∈ K) :
    (competingEntranceLaw D K x).real {v} =
      exitPayoff (D \ K) (fun y ↦ if y = v then 1 else 0) x := by
  classical
  have he : ({v} : Set Site) ∩ (K : Set Site) = {v} := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Finset.mem_coe]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h ▸ hv⟩⟩
  unfold competingEntranceLaw
  rw [measureReal_def, Measure.restrict_apply (measurableSet_singleton v), he]
  change (pathLaw.map (domainExitLocation (D \ K) x)).real {v} = _
  rw [map_measureReal_apply (measurable_domainExitLocation (D \ K) x)
    (measurableSet_singleton v)]
  change pathLaw.real {ω | domainExitLocation (D \ K) x ω = v} = _
  have hm : MeasurableSet {ω | domainExitLocation (D \ K) x ω = v} :=
    measurableSet_eq_fun (measurable_domainExitLocation (D \ K) x) measurable_const
  simpa [exitPayoff, Set.indicator] using
    (integral_indicator_one (μ := pathLaw) hm).symm

/-- Last-step entrance formula with the actual punctured Green kernel and all directions retained. -/
theorem competingEntranceLaw_atom_green (D K : Finset Site) (x v : Site)
    (hx : x ∉ K) (hv : v ∈ K) :
    (competingEntranceLaw D K x).real {v} =
      ∑ y ∈ D \ K, killedGreen (D \ K) x y *
        ((1 / 4 : ℝ) * ∑ d : Direction, if y + step d = v then 1 else 0) := by
  classical
  rw [competingEntranceLaw_atom_payoff D K x v hv]
  have hxv : x ≠ v := fun h ↦ hx (h ▸ hv)
  have hh := poisson_boundary_formula (D \ K) (fun y ↦ if y = v then 1 else 0) x
  simp only [if_neg hxv, sub_zero] at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro y hy
  have hyv : y ≠ v := fun h ↦ (Finset.mem_sdiff.mp hy).2 (h ▸ hv)
  simp only [if_neg hyv, sub_zero]

end SRWTightness
