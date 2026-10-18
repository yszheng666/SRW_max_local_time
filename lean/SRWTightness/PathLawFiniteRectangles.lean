import SRWTightness.FiniteRectangleMeasureExt
import Mathlib.Probability.Process.FiniteDimensionalLaws

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Whole measurable path laws agree once every finite measurable rectangle has the same mass. -/
theorem path_law_eq_of_finite_rectangles {Ω Ω' ι E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : Ω → ι → E) (G : Ω' → ι → E) (hF : Measurable F) (hG : Measurable G)
    (h : ∀ (I : Finset ι) (A : I → Set E), (∀ i, MeasurableSet (A i)) →
      μ {ω | ∀ i : I, F ω i ∈ A i} = ν {ω | ∀ i : I, G ω i ∈ A i}) :
    μ.map F = ν.map G := by
  have he (I : Finset ι) : μ.map (fun ω ↦ I.restrict (F ω)) =
      ν.map (fun ω ↦ I.restrict (G ω)) := by
    have hmF : Measurable (fun ω ↦ I.restrict (F ω)) :=
      (Finset.measurable_restrict I).comp hF
    have hmG : Measurable (fun ω ↦ I.restrict (G ω)) :=
      (Finset.measurable_restrict I).comp hG
    apply finite_rectangle_measure_ext
    intro A hA
    have hbox : MeasurableSet (Set.pi Set.univ A) :=
      MeasurableSet.pi Set.countable_univ (fun i _ ↦ hA i)
    rw [Measure.map_apply hmF hbox, Measure.map_apply hmG hbox]
    have hpF : (fun ω ↦ I.restrict (F ω)) ⁻¹' Set.pi Set.univ A =
        {ω | ∀ i : I, F ω i ∈ A i} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
        Finset.restrict_def, Set.mem_setOf_eq]
    have hpG : (fun ω ↦ I.restrict (G ω)) ⁻¹' Set.pi Set.univ A =
        {ω | ∀ i : I, G ω i ∈ A i} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const,
        Finset.restrict_def, Set.mem_setOf_eq]
    rw [hpF, hpG]
    exact h I A hA
  have hμ : IsProjectiveLimit (μ.map F)
      (fun I : Finset ι ↦ μ.map (fun ω ↦ I.restrict (F ω))) :=
    isProjectiveLimit_map hF.aemeasurable
  have hν : IsProjectiveLimit (ν.map G)
      (fun I : Finset ι ↦ μ.map (fun ω ↦ I.restrict (F ω))) := by
    intro I
    exact (isProjectiveLimit_map hG.aemeasurable I).trans (he I).symm
  exact hμ.unique hν

end SRWTightness
