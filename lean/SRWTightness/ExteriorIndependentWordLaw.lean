import SRWTightness.KilledWordBridgeLaw
import SRWTightness.ExteriorReachableExit
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.List.OfFn

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

instance exteriorWordListMeasurableSpace : MeasurableSpace (List PathWord) := ⊤
instance exteriorWordListMeasurableSingletonClass : MeasurableSingletonClass (List PathWord) :=
  ⟨fun _ ↦ trivial⟩

/-- The independent component bridges in the fixed chronological order of the exterior headers. -/
noncomputable def exteriorIndependentWordLaw (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) : Measure (List PathWord) :=
  (Measure.pi (fun i : Fin h.1.length ↦ killedWordBridgeLaw
    (if (h.1.get i).2.1 then C₁ else C₀) (h.1.get i).2.2.1 (h.1.get i).2.2.2)).map List.ofFn

/-- Reachable selected exits make the ordered independent word law a probability law. -/
theorem exteriorIndependentWordLaw_isProbabilityMeasure (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord)
    (he : ∀ s ∈ h.1, 0 < traceExitProbability (if s.2.1 then C₁ else C₀) s.2.2.1 s.2.2.2) :
    IsProbabilityMeasure (exteriorIndependentWordLaw C₀ C₁ h) := by
  letI (i : Fin h.1.length) : IsProbabilityMeasure (killedWordBridgeLaw
      (if (h.1.get i).2.1 then C₁ else C₀) (h.1.get i).2.2.1 (h.1.get i).2.2.2) :=
    killedWordBridgeLaw_isProbabilityMeasure _ _ _ (he _ (List.get_mem _ _))
  exact Measure.isProbabilityMeasure_map (measurable_of_countable List.ofFn).aemeasurable

/-- Singleton masses of the ordered independent word law are exactly the labeled bridge products. -/
theorem exteriorIndependentWordLaw_ofFn (C₀ C₁ : Finset Site)
    (h : ExteriorPathRecord) (f : Fin h.1.length → PathWord) :
    (exteriorIndependentWordLaw C₀ C₁ h).real {List.ofFn f} =
      ∏ i, killedWordBridgeProbability (if (h.1.get i).2.1 then C₁ else C₀)
        (h.1.get i).2.2.1 (h.1.get i).2.2.2 (f i) := by
  letI (i : Fin h.1.length) : IsFiniteMeasure (killedWordBridgeLaw
      (if (h.1.get i).2.1 then C₁ else C₀) (h.1.get i).2.2.1 (h.1.get i).2.2.2) := by
    unfold killedWordBridgeLaw
    infer_instance
  rw [exteriorIndependentWordLaw, map_measureReal_apply (measurable_of_countable List.ofFn)
    (measurableSet_singleton _)]
  have hs : List.ofFn ⁻¹' {List.ofFn f} = {f} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, List.ofFn_inj]
  rw [hs]
  unfold Measure.real
  rw [Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact killedWordBridgeLaw_singleton _ _ _ _

end SRWTightness
