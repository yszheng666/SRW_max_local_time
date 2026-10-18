import SRWTightness.PoissonizationBound
import SRWTightness.ContinuousOccupation

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace SRWTightness

 theorem markProductLaw_prefix (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (k : ℕ) :
    MeasurePreserving (fun Y : MarkSamples A (k + 1) ↦ fun i : Fin k ↦ Y i.castSucc)
      (markProductLaw D A α (k + 1)) (markProductLaw D A α k) := by
  letI := referenceMarkLaw_isProbabilityMeasure D A α hα hcap
  have h := (measurePreserving_snd (μ := referenceMarkLaw D A α)
    (ν := markProductLaw D A α k)).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ referenceMarkLaw D A α)
        (Fin.last k))
  change MeasurePreserving (fun Y : MarkSamples A (k + 1) ↦
    fun i : Fin k ↦ Y ((Fin.last k).succAbove i)) _ _ at h
  simpa only [Fin.succAbove_last, markProductLaw] using h

noncomputable def fixedMarkExceedance (D A : Finset Site) (α : ℝ) (k a : ℕ) : ℝ :=
  (markProductLaw D A α k).real {Y | ∃ z : A, a ≤ sumMarks A k Y z}

 theorem fixedMarkExceedance_mono (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (a : ℕ) :
    Monotone (fun k ↦ fixedMarkExceedance D A α k a) := by
  apply monotone_nat_of_le_succ
  intro k
  letI := markProductLaw_isProbabilityMeasure D A α hα hcap (k + 1)
  unfold fixedMarkExceedance
  rw [← (markProductLaw_prefix D A α hα hcap k).measureReal_preimage
    (MeasurableSet.of_discrete.nullMeasurableSet)]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro Y ⟨z, hz⟩
  refine ⟨z, hz.trans ?_⟩
  change (∑ i : Fin k, Y i.castSucc z) ≤ ∑ i : Fin (k + 1), Y i z
  rw [Fin.sum_univ_castSucc]
  exact Nat.le_add_right _ _

/-- The Poissonization step for the actual maximum-count event, uniformly in the observation set. -/
theorem fixedMarkExceedance_le_poissonized (D A : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (k a : ℕ) (hk : 1 ≤ k) :
    fixedMarkExceedance D A α k a ≤
      16 * ∫ n : ℕ, fixedMarkExceedance D A α n a ∂poissonMeasure (k : ℝ≥0) := by
  apply monotone_poissonization_bound _ (fun n ↦ measureReal_nonneg) _
    (fixedMarkExceedance_mono D A α hα hcap a) k hk
  intro n
  letI := markProductLaw_isProbabilityMeasure D A α hα hcap n
  exact (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans_eq (by simp)

end SRWTightness
