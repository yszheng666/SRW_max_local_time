import SRWTightness.SourceTaggedRemainingError
import SRWTightness.OrderedTupleErrorDomination

open Filter
open scoped BigOperators
namespace SRWTightness

/-- Compatible tuples with capped roots and the two remaining barriers lie in the region where
the complete conditional record error is uniformly bounded. -/
theorem source_tuple_remaining_region (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ,
      ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (A C a₀ a₁ : ℝ) (K₀ K₁ : Finset Site), 0 ≤ A → 0 ≤ C →
      1 ≤ a₀ → a₀ ≤ sourceLowerRadius t / t ^ 6 →
      1 ≤ a₁ → a₁ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ (n : ℕ) (label : Fin n → Bool) (r : Fin n → SourceExteriorFineValue t K₀ K₁ ν)
        (k l : ℕ),
      orderedTaggedCompatible label r →
      (orderedTaggedForests r).1.length = k → (orderedTaggedForests r).2.length = l →
      k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      forestPopulationList _ (orderedTaggedForests r).1 ∈ sourceContinuationBand t ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      forestPopulationList _ (orderedTaggedForests r).2 ∈ sourceContinuationBand t ν
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)) →
      r ∈ orderedTupleErrorRegion label k l
        (fun s ↦ ∑ i, sourceExteriorFineError A C B W t a₀ a₁ K₀ K₁ ν J (s i))
        (16 * ((ν : ℝ) + 1) ^ 2 *
          (A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
            C * 15 / (sourceRecordRadius (sourceLowerRadius t)
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)) +
          2 * sourceForestQuadraticError B W 8 t) := by
  filter_upwards [source_tagged_remaining_error_bound B W hB hW] with t ht
  intro ν J hν A C a₀ a₁ K₀ K₁ hA hC ha₀ hc₀ ha₁ hc₁ n label r k l hr hk hl
    hkcap hlcap hb₀ hb₁
  refine ⟨hr, hk, hl, ?_⟩
  have hne : ∀ s ∈ List.ofFn r, s.elim (fun us ↦ us ≠ []) (fun us ↦ us ≠ []) := by
    intro s hs
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hs
    have hi := hr i
    cases hri : r i with
    | inl us =>
      rw [hri] at hi
      exact hi.2
    | inr us =>
      rw [hri] at hi
      exact hi.2
  have he := ht ν J hν A C a₀ a₁ K₀ K₁ hA hC ha₀ hc₀ ha₁ hc₁
    (List.ofFn r) hne (hk ▸ hkcap) (hl ▸ hlcap) hb₀ hb₁
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using he

end SRWTightness
