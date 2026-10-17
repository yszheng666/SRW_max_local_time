import SRWTightness.SourceExteriorRecordValues
import SRWTightness.SourceSelectedFineError
import SRWTightness.ExteriorWordAlignment
import Mathlib.Algebra.BigOperators.Ring.List

open scoped BigOperators
namespace SRWTightness

/-- The error attached to the complete tagged tuple is exactly the original path's selected error. -/
theorem source_exterior_fine_error_alignment (A C B W t a₀ a₁ : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) :
    let m := sourceLowerRadius t
    let ℓ := sourceRootDepth (Real.exp t) m
    let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
    let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
    ∀ (h : ExteriorPathRecord),
    0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
    ∀ (ω : Sample) (us : List PathWord), sourcePairExteriorRecord t b w ν J ω = h →
    killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
      0 (fun _ u ↦ u) ω = us →
    ((h.1.zip us).map (fun p ↦ sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J
      (sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2))).sum =
      sourceSelectedFineError A C B W t a₀ a₁ b w K₀ K₁ ν J ω := by
  dsimp only
  intro h hh ω us hω hu
  unfold sourceSelectedFineError
  dsimp only
  rw [← exterior_word_fiber_records _ _ _ _ 0 ω h us hω hu]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hl := (exterior_atom_slot _ _ _ _ 0 h hh p.1 (List.of_mem_zip hp).1).2.2
  unfold sourceExteriorFineError sourceExteriorFineRecord sourceLongFineListError
  dsimp only
  rw [← hl]
  cases p.1.2.1 <;> rfl

/-- On each actual record-tuple fiber, the finite summed exponent is the already bounded path error. -/
theorem source_exterior_record_error_fiber (A C B W t a₀ a₁ : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) :
    let m := sourceLowerRadius t
    let ℓ := sourceRootDepth (Real.exp t) m
    let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
    let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
    ∀ (h : ExteriorPathRecord),
    0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
    ∀ (ω : Sample) (us : List PathWord), sourcePairExteriorRecord t b w ν J ω = h →
    killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
      0 (fun _ u ↦ u) ω = us →
    ∀ r : Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν,
    (h.1.zip us).map (fun p ↦ sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2) = List.ofFn r →
    (∑ i, sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J (r i)) =
      sourceSelectedFineError A C B W t a₀ a₁ b w K₀ K₁ ν J ω := by
  dsimp only
  intro h hh ω us hω hu r hr
  have he := source_exterior_fine_error_alignment A C B W t a₀ a₁ b w K₀ K₁ ν J h hh ω us hω hu
  have hc := congrArg (fun vs ↦ (vs.map (sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J)).sum) hr
  simp only [List.map_map, Function.comp_def, List.map_ofFn, List.sum_ofFn] at hc
  exact hc.symm.trans he

end SRWTightness
