import SRWTightness.Law

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem steps_independent :
    iIndepFun (fun n (ω : Sample) ↦ step (ω n)) pathLaw :=
  directions_independent.comp (fun _ ↦ step) (fun _ ↦ measurable_of_countable step)

 theorem position_indep_next (n : ℕ) :
    IndepFun (fun ω ↦ position ω n) (fun ω ↦ step (ω n)) pathLaw := by
  have h := steps_independent.indepFun_finsetSum_of_notMem
    (fun i ↦ (measurable_of_countable step).comp (measurable_pi_apply i))
    (s := Finset.range n) (i := n) (by simp)
  convert h using 1
  funext ω
  simp only [Finset.sum_apply, position_eq_sum]

/-- The whole observed past, not just the current position, is independent of the next direction. -/
theorem prefix_indep_next (n : ℕ) :
    IndepFun (fun ω : Sample ↦ fun k : Fin n ↦ ω k) (fun ω ↦ ω n) pathLaw := by
  have hd : Disjoint (Finset.range n) {n} := by simp
  have h := directions_independent.indepFun_finset (Finset.range n) {n} hd
    (fun i ↦ measurable_pi_apply i)
  exact h.comp
    (measurable_of_countable (fun w : (i : Finset.range n) → Direction ↦
      fun k : Fin n ↦ w ⟨k, Finset.mem_range.mpr k.isLt⟩))
    (measurable_of_countable (fun w : (i : ({n} : Finset ℕ)) → Direction ↦
      w ⟨n, Finset.mem_singleton_self n⟩))

end SRWTightness
