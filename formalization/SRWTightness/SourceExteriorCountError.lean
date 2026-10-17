import SRWTightness.SourceExteriorRecordError
import SRWTightness.SourceExteriorCountProduct
import SRWTightness.SourceSelectedCountError

open scoped BigOperators
namespace SRWTightness

/-- Zero fine coefficients leave exactly the root-count cost of the selected short intervals. -/
theorem source_exterior_count_error_word (A C t a₀ a₁ : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (s : ExteriorSlot) (u : PathWord) :
    sourceExteriorFineError A C 0 0 t a₀ a₁ K₀ K₁ ν J
      (sourceExteriorFineRecord t b w K₀ K₁ ν s u) =
    A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14) *
        (sourceExteriorRootCount t b w ν s u : ℝ) := by
  have hz₀ : sourceLongFineError 0 0 t a₀ K₀ ν = fun _ ↦ 0 := by
    funext r
    exact source_long_fine_error_zero t a₀ K₀ ν r
  have hz₁ : sourceLongFineError 0 0 t a₁ K₁ ν = fun _ ↦ 0 := by
    funext r
    exact source_long_fine_error_zero t a₁ K₁ ν r
  cases hl : s.2.1 <;>
    simp [sourceExteriorFineError, sourceExteriorFineRecord, sourceLongFineListError,
      sourceExteriorRootCount, wordChildRecords, hl, hz₀, hz₁, Function.comp_def, List.map_const']

/-- On an actual count-tuple fiber, the exponent is exactly the original count-only selected error. -/
theorem source_exterior_count_error_fiber (A C t a₀ a₁ : ℝ) (b w : Site)
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
    ∀ k : Fin h.1.length → ℕ,
    (h.1.zip us).map (fun p ↦ sourceExteriorRootCount t b w ν p.1 p.2) =
      List.ofFn (fun i ↦ k i + 1) →
    (∑ i : Fin h.1.length, (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
      C * 15 / (sourceRecordRadius m ℓ (ν + 1) - 14) * ((k i : ℝ) + 1))) =
      sourceSelectedFineError A C 0 0 t a₀ a₁ b w K₀ K₁ ν J ω := by
  dsimp only
  intro h hh ω us hω hu k hk
  have he := source_exterior_fine_error_alignment A C 0 0 t a₀ a₁ b w K₀ K₁ ν J h hh ω us hω hu
  simp only [source_exterior_count_error_word] at he
  let cost : ℕ → ℝ := fun n ↦ A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
    C * 15 / (sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14) * (n : ℝ)
  calc
    _ = ((List.ofFn (fun i : Fin h.1.length ↦ k i + 1)).map cost).sum := by
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def, cost, Nat.cast_add, Nat.cast_one]
    _ = (((h.1.zip us).map (fun p ↦ sourceExteriorRootCount t b w ν p.1 p.2)).map cost).sum :=
      congrArg (fun ns : List ℕ ↦ (ns.map cost).sum) hk.symm
    _ = ((h.1.zip us).map (fun p ↦ cost (sourceExteriorRootCount t b w ν p.1 p.2))).sum := by
      rw [List.map_map]
      rfl
    _ = _ := he

end SRWTightness
