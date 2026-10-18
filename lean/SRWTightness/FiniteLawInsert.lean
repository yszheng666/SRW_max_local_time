import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory
namespace SRWTightness

/-- A finite-coordinate law is determined by the old coordinates together with one added value. -/
theorem finite_law_insert {Ω Ω' ι E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E] [DecidableEq ι]
    (μ : Measure Ω) (ν : Measure Ω') (F : Ω → ι → E) (G : Ω' → ι → E)
    (hF : Measurable F) (hG : Measurable G) (I : Finset ι) (a : ι)
    (h : μ.map (fun ω ↦ (I.restrict (F ω), F ω a)) =
      ν.map (fun ω ↦ (I.restrict (G ω), G ω a))) :
    μ.map (fun ω ↦ (insert a I).restrict (F ω)) =
      ν.map (fun ω ↦ (insert a I).restrict (G ω)) := by
  let H : (I → E) × E → ↥(insert a I) → E := fun p i ↦
    if hi : (i : ι) = a then p.2 else p.1 ⟨i, (Finset.mem_insert.mp i.property).resolve_left hi⟩
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro i
    dsimp [H]
    split_ifs
    · exact measurable_snd
    · exact (measurable_pi_apply _).comp measurable_fst
  have hmF : Measurable (fun ω ↦ (I.restrict (F ω), F ω a)) :=
    ((Finset.measurable_restrict I).comp hF).prodMk ((measurable_pi_apply a).comp hF)
  have hmG : Measurable (fun ω ↦ (I.restrict (G ω), G ω a)) :=
    ((Finset.measurable_restrict I).comp hG).prodMk ((measurable_pi_apply a).comp hG)
  have heF : H ∘ (fun ω ↦ (I.restrict (F ω), F ω a)) =
      fun ω ↦ (insert a I).restrict (F ω) := by
    funext ω i
    dsimp [H, Function.comp_def, Finset.restrict_def]
    split_ifs with hi
    · exact congrArg (F ω) hi.symm
    · rfl
  have heG : H ∘ (fun ω ↦ (I.restrict (G ω), G ω a)) =
      fun ω ↦ (insert a I).restrict (G ω) := by
    funext ω i
    dsimp [H, Function.comp_def, Finset.restrict_def]
    split_ifs with hi
    · exact congrArg (G ω) hi.symm
    · rfl
  have he := congrArg (fun ρ : Measure ((I → E) × E) ↦ ρ.map H) h
  rw [Measure.map_map hH hmF, Measure.map_map hH hmG, heF, heG] at he
  exact he

end SRWTightness
