import SRWTightness.SourceLiteralForestComparison
import SRWTightness.ReferenceWordMark

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- The full ordered marked forest retains all joint events and the exterior return factor. -/
theorem ordered_literal_forest_upper (Dref K : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity Dref K ≤ 1) (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord WordMark n)]
    [MeasurableSingletonClass (FiniteExcursionRecord WordMark n)]
    [MeasurableSpace (List (FiniteExcursionRecord WordMark n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark n))]
    (R : ℝ) (b : Site) (a c : ℝ) (ha : 1 ≤ a) (hac : a ≤ c)
    (hfit : Real.sqrt (normSq b) + c + 1 < R) (hout : a ≤ Real.sqrt (normSq b))
    (F : Site → PathWord → FiniteExcursionRecord WordMark n) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (η : FiniteExcursionRecord WordMark n → ℝ)
    (hreturn : ∀ y : Site, c ≤ Real.sqrt (normSq (y - b)) →
      Real.sqrt (normSq (y - b)) ≤ c + 1 →
      setHitProbability (diskFinset R) (translateFinset b (diskFinset a)) y ≤ ρ)
    (hrecord : ∀ z : Site, a - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ a → ∀ r,
      pathLaw.real {ω | F z (killedPathWord (translateFinset b (diskFinset c)) z ω) = r} ≤
        Real.exp (η r) * finiteRecordReferenceWeight
          (fun v ↦ (referenceWordMarkLaw Dref K α).real {v}) n r)
    (j : ℕ) (hj : 1 ≤ j) (s : Set (List (FiniteExcursionRecord WordMark n)))
    (E : ℝ) (herr : ∀ rs ∈ s, rs.length = j → (rs.map η).sum ≤ E) :
    let μ := finiteRecordReferenceMeasure (referenceWordMarkLaw Dref K α) n
    pathLaw.real {ω |
      (killedChildRecords (diskFinset R) (translateFinset b (diskFinset a))
        (translateFinset b (diskFinset c)) 0 F ω).length = j ∧
      killedChildRecords (diskFinset R) (translateFinset b (diskFinset a))
        (translateFinset b (diskFinset c)) 0 F ω ∈ s} ≤
      ρ ^ (j - 1) * Real.exp E * (independentForestLaw μ j).real s := by
  dsimp only
  letI := finiteExcursionRecord_countable WordMark n
  letI := referenceWordMarkLaw_probability Dref K α hα hcap
  letI := finite_record_reference_measure_probability_internal (referenceWordMarkLaw Dref K α) n
  let s' := {rs : List (FiniteExcursionRecord WordMark n) | rs.length = j ∧ rs ∈ s}
  have hpoint : ∀ z : Site, a - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ a → ∀ r,
      pathLaw.real {ω | F z (killedPathWord (translateFinset b (diskFinset c)) z ω) = r} ≤
        Real.exp (η r) *
          (finiteRecordReferenceMeasure (referenceWordMarkLaw Dref K α) n).real {r} := by
    intro z hzlo hzhi r
    rw [finiteRecordReferenceMeasure_real_singleton]
    exact hrecord z hzlo hzhi r
  have hh := disk_forest_reference_upper R b a c ha hac hfit hout F ρ hρ η
    (finiteRecordReferenceMeasure (referenceWordMarkLaw Dref K α) n) hreturn hpoint j hj s' E
    (fun _ h ↦ h.1) (fun _ h ↦ herr _ h.2 h.1)
  rw [independentForestLaw_length_intersection] at hh
  have hfin : ENNReal.ofReal (ρ ^ (j - 1) * Real.exp E) *
      independentForestLaw (finiteRecordReferenceMeasure
        (referenceWordMarkLaw Dref K α) n) j s ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have ht := ENNReal.toReal_mono hfin hh
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at ht
  exact ht

end SRWTightness
