import SRWTightness.ReferenceSecondMoment
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory

namespace SRWTightness

abbrev MarkSamples (K : Finset Site) (k : ℕ) := Fin k → Mark K

noncomputable def markProductLaw (D K : Finset Site) (α : ℝ) (k : ℕ) :
    Measure (MarkSamples K k) := Measure.pi (fun _ : Fin k ↦ referenceMarkLaw D K α)

 theorem markProductLaw_isProbabilityMeasure (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) :
    IsProbabilityMeasure (markProductLaw D K α k) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  unfold markProductLaw
  infer_instance

 theorem mark_eval_measurePreserving (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) (i : Fin k) :
    MeasurePreserving (fun Y : MarkSamples K k ↦ Y i) (markProductLaw D K α k)
      (referenceMarkLaw D K α) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  exact measurePreserving_eval (fun _ : Fin k ↦ referenceMarkLaw D K α) i

 theorem independent_marks (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) :
    iIndepFun (fun i (Y : MarkSamples K k) ↦ Y i) (markProductLaw D K α k) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  exact iIndepFun_pi (X := fun _ Y ↦ Y) (fun _ ↦ measurable_id.aemeasurable)

 theorem mark_coordinate_memLp_two (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) (i : Fin k) (z : K) :
    MemLp (fun Y : MarkSamples K k ↦ (Y i z : ℝ)) 2 (markProductLaw D K α k) :=
  (referenceMark_coordinate_memLp_two D K α z).comp_measurePreserving
    (mark_eval_measurePreserving D K α hα hcap k i)

 theorem mark_cross_covariance (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) (i j : Fin k) (y z : K) :
    covariance (fun Y : MarkSamples K k ↦ (Y i y : ℝ)) (fun Y : MarkSamples K k ↦ (Y j z : ℝ))
      (markProductLaw D K α k) =
      if i = j then 2 * α * killedGreen D y z - α * (if y = z then 1 else 0) - α ^ 2 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hy : Measurable (fun Y : Mark K ↦ (Y y : ℝ)) :=
      (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply y)
    have hz : Measurable (fun Y : Mark K ↦ (Y z : ℝ)) :=
      (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z)
    have he := covariance_map_fun (μ := markProductLaw D K α k)
      (Z := fun Y : MarkSamples K k ↦ Y i) hy.aestronglyMeasurable hz.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable
    rw [(mark_eval_measurePreserving D K α hα hcap k i).map_eq] at he
    rw [← he, referenceMark_covariance D K hKD α hα hcap y z]
  · rw [if_neg hij]
    have hi := (independent_marks D K α hα hcap k).indepFun hij
    have hc := hi.comp
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply y))
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z))
    exact hc.covariance_eq_zero (mark_coordinate_memLp_two D K α hα hcap k i y)
      (mark_coordinate_memLp_two D K α hα hcap k j z)

 theorem mark_sum_covariance (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) (y z : K) :
    covariance (fun Y : MarkSamples K k ↦ ∑ i : Fin k, (Y i y : ℝ))
      (fun Y : MarkSamples K k ↦ ∑ i : Fin k, (Y i z : ℝ)) (markProductLaw D K α k) =
      k * (2 * α * killedGreen D y z - α * (if y = z then 1 else 0) - α ^ 2) := by
  letI := markProductLaw_isProbabilityMeasure D K α hα hcap k
  rw [covariance_fun_sum_fun_sum (fun i ↦ mark_coordinate_memLp_two D K α hα hcap k i y)
    (fun j ↦ mark_coordinate_memLp_two D K α hα hcap k j z)]
  simp_rw [mark_cross_covariance D K hKD α hα hcap k]
  by_cases h : y = z <;> simp [h] <;> ring

end SRWTightness
