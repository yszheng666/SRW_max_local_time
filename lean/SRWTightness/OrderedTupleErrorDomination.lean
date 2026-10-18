import SRWTightness.OrderedTaggedForestMixture
import SRWTightness.CountableRecordDomination

open MeasureTheory
namespace SRWTightness

/-- The record region on which both root totals and the full logarithmic error are controlled. -/
def orderedTupleErrorRegion {α β : Type*} {n : ℕ} (label : Fin n → Bool) (k l : ℕ)
    (err : (Fin n → Sum (List α) (List β)) → ℝ) (E : ℝ) :
    Set (Fin n → Sum (List α) (List β)) :=
  {r | orderedTaggedCompatible label r ∧ (orderedTaggedForests r).1.length = k ∧
    (orderedTaggedForests r).2.length = l ∧ err r ≤ E}

/-- The pointwise exponential record comparison gives the restricted reference measure bound. -/
theorem ordered_tuple_error_domination {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    {n : ℕ} (μ : Measure (Fin n → Sum (List α) (List β))) [IsFiniteMeasure μ]
    (μ₀ : Measure α) (μ₁ : Measure β) (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (label : Fin n → Bool) (k l : ℕ) (err : (Fin n → Sum (List α) (List β)) → ℝ) (E : ℝ)
    (hpoint : ∀ r, orderedTaggedCompatible label r →
      μ.real {r} ≤ Real.exp (err r) *
        ∏ i, (r i).elim (orderedForestBlockWeight p μ₀) (orderedForestBlockWeight p μ₁)) :
    μ.restrict (orderedTupleErrorRegion label k l err E) ≤
      ENNReal.ofReal (Real.exp E) • orderedTaggedCountMeasure p label μ₀ μ₁ k l := by
  classical
  apply restricted_record_domination
  intro r hr
  obtain ⟨hc, hk, hl, hE⟩ := hr
  have hw : orderedTaggedCountWeight p label μ₀ μ₁ k l r =
      ∏ i, (r i).elim (orderedForestBlockWeight p μ₀) (orderedForestBlockWeight p μ₁) := by
    simp only [orderedTaggedCountWeight, hc, hk, hl, and_self, if_true]
  have hnon := orderedTaggedCountWeight_nonneg p label μ₀ μ₁ k l hp hp₁ r
  rw [hw] at hnon
  rw [orderedTaggedCountMeasure_singleton, hw,
    ← ENNReal.ofReal_mul (Real.exp_pos E).le,
    ← ofReal_measureReal (measure_ne_top μ {r})]
  exact ENNReal.ofReal_le_ofReal ((hpoint r hc).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hE) hnon))

/-- The same error-region bound holds after adjoining an independent auxiliary law. -/
theorem ordered_tuple_auxiliary_error_domination {α β Γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable α] [Countable β]
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    [MeasurableSpace Γ] {n : ℕ}
    (μ : Measure (Fin n → Sum (List α) (List β))) [IsFiniteMeasure μ]
    (μ₀ : Measure α) (μ₁ : Measure β) (σ : Measure Γ) [SFinite σ]
    (p : ℝ) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (label : Fin n → Bool) (k l : ℕ)
    (err : (Fin n → Sum (List α) (List β)) → ℝ) (E : ℝ)
    (hpoint : ∀ r, orderedTaggedCompatible label r →
      μ.real {r} ≤ Real.exp (err r) *
        ∏ i, (r i).elim (orderedForestBlockWeight p μ₀) (orderedForestBlockWeight p μ₁)) :
    (μ.prod σ).restrict (orderedTupleErrorRegion label k l err E ×ˢ Set.univ) ≤
      ENNReal.ofReal (Real.exp E) • ((orderedTaggedCountMeasure p label μ₀ μ₁ k l).prod σ) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ, ← Measure.prod_smul_left]
  exact Measure.prod_mono
    (ordered_tuple_error_domination μ μ₀ μ₁ p hp hp₁ label k l err E hpoint) le_rfl

end SRWTightness
