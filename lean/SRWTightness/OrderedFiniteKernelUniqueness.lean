import SRWTightness.FiniteLawInsert
import SRWTightness.JointLawFromPastKernel
import SRWTightness.FiniteRectangleMeasureExt
import Mathlib.Data.Finset.Max

open MeasureTheory
namespace SRWTightness

/-- Ordered finite-dimensional laws are determined by their marginals
and past transition kernels. -/
theorem ordered_finite_kernel_uniqueness {Ω Ω' ι E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [LinearOrder ι] [DecidableEq ι]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω → ι → E) (G : Ω' → ι → E) (hF : Measurable F) (hG : Measurable G)
    (K : ι → ι → Set E → E → ℝ)
    (hK : ∀ r t B, MeasurableSet B → Measurable (K r t B))
    (hmarg : ∀ a, μ.map (fun ω ↦ F ω a) = ν.map (fun ω ↦ G ω a))
    (hμ : ∀ (I : Finset ι) (hne : I.Nonempty) a, (∀ i ∈ I, i < a) →
      ∀ (A : Set (I → E)) B, MeasurableSet A → MeasurableSet B →
      μ.real {ω | I.restrict (F ω) ∈ A ∧ F ω a ∈ B} =
        ∫ ω in {ω | I.restrict (F ω) ∈ A}, K (I.max' hne) a B (F ω (I.max' hne)) ∂μ)
    (hν : ∀ (I : Finset ι) (hne : I.Nonempty) a, (∀ i ∈ I, i < a) →
      ∀ (A : Set (I → E)) B, MeasurableSet A → MeasurableSet B →
      ν.real {ω | I.restrict (G ω) ∈ A ∧ G ω a ∈ B} =
        ∫ ω in {ω | I.restrict (G ω) ∈ A}, K (I.max' hne) a B (G ω (I.max' hne)) ∂ν)
    (I : Finset ι) :
    μ.map (fun ω ↦ I.restrict (F ω)) = ν.map (fun ω ↦ I.restrict (G ω)) := by
  induction I using Finset.induction_on_max with
  | empty =>
    apply finite_rectangle_measure_ext
    intro A hA
    have hs : Set.pi Set.univ A = Set.univ := by
      ext p
      simp
    have hF0 : Measurable (fun ω ↦ (∅ : Finset ι).restrict (F ω)) :=
      (Finset.measurable_restrict ∅).comp hF
    have hG0 : Measurable (fun ω ↦ (∅ : Finset ι).restrict (G ω)) :=
      (Finset.measurable_restrict ∅).comp hG
    rw [hs, Measure.map_apply hF0 MeasurableSet.univ,
      Measure.map_apply hG0 MeasurableSet.univ]
    simp
  | insert a I hlt ih =>
    rcases I.eq_empty_or_nonempty with hI | hne
    · subst I
      let H := fun z : E ↦ fun _ : ({a} : Finset ι) ↦ z
      have hH : Measurable H := measurable_pi_lambda _ (fun _ ↦ measurable_id)
      have he := congrArg (fun ρ : Measure E ↦ ρ.map H) (hmarg a)
      have hFa : Measurable (fun ω ↦ F ω a) := (measurable_pi_apply a).comp hF
      have hGa : Measurable (fun ω ↦ G ω a) := (measurable_pi_apply a).comp hG
      rw [Measure.map_map hH hFa, Measure.map_map hH hGa] at he
      have heF : H ∘ (fun ω ↦ F ω a) = fun ω ↦ ({a} : Finset ι).restrict (F ω) := by
        funext ω i
        exact congrArg (F ω) (Finset.mem_singleton.mp i.property).symm
      have heG : H ∘ (fun ω ↦ G ω a) = fun ω ↦ ({a} : Finset ι).restrict (G ω) := by
        funext ω i
        exact congrArg (G ω) (Finset.mem_singleton.mp i.property).symm
      rw [heF, heG] at he
      exact he
    · apply finite_law_insert μ ν F G hF hG I a
      let e : I := ⟨I.max' hne, I.max'_mem hne⟩
      apply joint_law_from_past_kernel μ ν
        (fun ω ↦ I.restrict (F ω)) (fun ω ↦ I.restrict (G ω))
        (fun ω ↦ F ω a) (fun ω ↦ G ω a)
        ((Finset.measurable_restrict I).comp hF) ((Finset.measurable_restrict I).comp hG)
        ((measurable_pi_apply a).comp hF) ((measurable_pi_apply a).comp hG)
        (fun B p ↦ K (I.max' hne) a B (p e))
        (fun B hB ↦ (hK _ _ B hB).comp (measurable_pi_apply e)) ih
      · exact hμ I hne a hlt
      · exact hν I hne a hlt

end SRWTightness
