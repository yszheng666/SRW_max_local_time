import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory

namespace SRWTightness

/-- Binding a countable probability kernel equals its exact singleton-weighted measure sum. -/
theorem countable_measure_bind_sum {A B : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [Countable A] [MeasurableSpace B]
    (μ : Measure A) (f : A → Measure B) :
    μ.bind f = Measure.sum (fun x ↦ μ {x} • f x) := by
  have hf : Measurable f := measurable_of_countable f
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  rw [Measure.bind_sum _ _ hf.aemeasurable]
  apply congrArg Measure.sum
  funext x
  rw [Measure.bind_smul, Measure.dirac_bind hf]

end SRWTightness
