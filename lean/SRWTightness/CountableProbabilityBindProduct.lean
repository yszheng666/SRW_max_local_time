import SRWTightness.CountableMeasureBindSum
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory

namespace SRWTightness

/-- Independent countable probability mixtures equal the product-source mixture of their kernels. -/
theorem countable_probability_bind_product {A B X Y : Type*}
    [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]
    [MeasurableSpace B] [MeasurableSingletonClass B] [Countable B]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : A → Measure X) (g : B → Measure Y)
    [∀ a, IsProbabilityMeasure (f a)] [∀ b, IsProbabilityMeasure (g b)] :
    (μ.bind f).prod (ν.bind g) = (μ.prod ν).bind (fun q ↦ (f q.1).prod (g q.2)) := by
  rw [countable_measure_bind_sum μ f, countable_measure_bind_sum ν g,
    Measure.prod_sum, countable_measure_bind_sum (μ.prod ν)]
  apply congrArg Measure.sum
  funext q
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hs : (μ.prod ν) {q} = μ {q.1} * ν {q.2} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [hs]

end SRWTightness
