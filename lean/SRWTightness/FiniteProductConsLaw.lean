import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fin.Tuple.Basic

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- A finite family of independent laws splits exactly into its first coordinate and its tail. -/
theorem finite_product_cons_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (n : ℕ) (μ : Fin (n + 1) → Measure M)
    [∀ i, IsProbabilityMeasure (μ i)] :
    ((μ 0).prod (Measure.pi (fun i : Fin n ↦ μ i.succ))).map
      (fun q ↦ Fin.cons q.1 q.2) = Measure.pi μ := by
  apply Measure.ext_of_singleton
  intro ξ
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hs : (fun q : M × (Fin n → M) ↦ Fin.cons q.1 q.2) ⁻¹' {ξ} =
      {(ξ 0, Fin.tail ξ)} := by
    ext q
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hq
      apply Prod.ext
      · simpa using congrFun hq 0
      · funext i
        simpa [Fin.tail] using congrFun hq i.succ
    · intro hq
      subst q
      exact Fin.cons_self_tail ξ
  rw [hs, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.pi_singleton, Measure.pi_singleton, Fin.prod_univ_succ]
  rfl

end SRWTightness
