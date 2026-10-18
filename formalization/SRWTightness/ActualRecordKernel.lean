import SRWTightness.ChildRecordEntrance
import SRWTightness.OrderedRecordComparison

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The exact real-valued U-S recurrence, ready for the existing exponential record comparisons. -/
theorem killedChildRecords_cons_probability_real (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) {R : Type*} (x : Site) (F : Site → PathWord → R)
    (r : R) (rs : List R) :
    pathLaw.real {ω | killedChildRecords D K C x F ω = r :: rs} =
      ∫ z, ∫ ξ, pathLaw.real {ω | killedChildRecords D K C ξ F ω = rs}
        ∂recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r
        ∂competingEntranceLaw D K x := by
  let S : Site → Measure Site := fun z ↦
    recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r
  let p : Site → ℝ≥0∞ := fun ξ ↦ pathLaw {ω | killedChildRecords D K C ξ F ω = rs}
  have hi : ∀ z, (∫ ξ, (p ξ).toReal ∂S z) = (∫⁻ ξ, p ξ ∂S z).toReal := by
    intro z
    exact integral_toReal (measurable_of_countable p).aemeasurable
      (Filter.Eventually.of_forall (fun ξ ↦ measure_lt_top pathLaw _))
  have hf : ∀ z, (∫⁻ ξ, p ξ ∂S z) < ⊤ := by
    intro z
    have hb : (∫⁻ ξ, p ξ ∂S z) ≤ S z Set.univ := by
      calc
        _ ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂S z := lintegral_mono (fun _ ↦ prob_le_one)
        _ = _ := by simp
    exact lt_of_le_of_lt hb (measure_lt_top (S z) Set.univ)
  have ho := integral_toReal (μ := competingEntranceLaw D K x)
    (f := fun z ↦ ∫⁻ ξ, p ξ ∂S z) (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall hf)
  calc
    _ = (∫⁻ z, ∫⁻ ξ, p ξ ∂S z ∂competingEntranceLaw D K x).toReal :=
      congrArg ENNReal.toReal (killedChildRecords_cons_probability D K C hKC hCD x F r rs)
    _ = ∫ z, (∫⁻ ξ, p ξ ∂S z).toReal ∂competingEntranceLaw D K x := ho.symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z ↦ (hi z).symm)

/-- The actual ordered child-record probability is exactly the iterated U-S-V kernel weight. -/
theorem actual_ordered_record_kernel (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    {R : Type*} (F : Site → PathWord → R) (rs : List R) (x : Site) :
    pathLaw.real {ω | killedChildRecords D K C x F ω = rs} =
      orderedRecordWeight (competingEntranceLaw D K)
        (fun z r ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
        (competingExitMass D K) rs x := by
  induction rs generalizing x with
  | nil => exact killedChildRecords_nil_competing_mass D K C hKC hCD x F
  | cons r rs ih =>
    rw [killedChildRecords_cons_probability_real D K C hKC hCD x F r rs, orderedRecordWeight]
    apply integral_congr_ae
    filter_upwards [] with z
    apply integral_congr_ae
    filter_upwards [] with ξ
    exact ih ξ

/-- Projection preserves the exact number of complete extracted segments. -/
theorem killedChildRecords_length {R : Type*} (D K C : Finset Site) (x : Site)
    (F : Site → PathWord → R) (ω : Sample) :
    (killedChildRecords D K C x F ω).length = (killedChildIntervals D K C x ω).length := by
  simp [killedChildRecords, wordChildRecords, killedChildIntervals]

/-- Specifying the ordered list also specifies the exact number of extracted segments. -/
theorem actual_ordered_record_kernel_with_count (D K C : Finset Site) (hKC : K ⊆ C)
    (hCD : C ⊆ D) {R : Type*} (F : Site → PathWord → R) (rs : List R) (x : Site) :
    pathLaw.real {ω | (killedChildIntervals D K C x ω).length = rs.length ∧
      killedChildRecords D K C x F ω = rs} =
      orderedRecordWeight (competingEntranceLaw D K)
        (fun z r ↦ recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) r)
        (competingExitMass D K) rs x := by
  rw [← actual_ordered_record_kernel D K C hKC hCD F rs x]
  apply congrArg (fun s : Set Sample ↦ pathLaw.real s)
  ext ω
  constructor
  · exact fun h ↦ h.2
  · intro h
    refine ⟨?_, h⟩
    rw [← killedChildRecords_length D K C x F ω, h]

end SRWTightness
