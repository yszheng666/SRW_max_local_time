import Mathlib.MeasureTheory.Measure.GiryMonad

open MeasureTheory

namespace SRWTightness

/-- Mapping the output of a measurable measure-valued kernel commutes with binding. -/
theorem measure_bind_map_output {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (f : A → Measure B) (g : B → C)
    (hf : Measurable f) (hg : Measurable g) :
    (μ.bind f).map g = μ.bind (fun x ↦ (f x).map g) := by
  have hd : Measurable (fun x ↦ Measure.dirac (g x)) := Measure.measurable_dirac.comp hg
  rw [← Measure.bind_dirac_eq_map _ hg, Measure.bind_bind hf.aemeasurable hd.aemeasurable]
  simp only [Measure.bind_dirac_eq_map _ hg]

/-- Mapping the input of a measurable measure-valued kernel is substitution inside its bind. -/
theorem measure_map_bind_input {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (g : A → B) (f : B → Measure C)
    (hg : Measurable g) (hf : Measurable f) :
    (μ.map g).bind f = μ.bind (fun x ↦ f (g x)) := by
  have hd : Measurable (fun x ↦ Measure.dirac (g x)) := Measure.measurable_dirac.comp hg
  rw [← Measure.bind_dirac_eq_map _ hg, Measure.bind_bind hd.aemeasurable hf.aemeasurable]
  simp only [Measure.dirac_bind hf]

end SRWTightness
