import SRWTightness.ReferenceIntegral
import SRWTightness.TailGeometric

open MeasureTheory

namespace SRWTightness

noncomputable def markTailIndicator {K : Finset Site} (z : K) (k : ℕ) (Y : Mark K) : ℝ :=
  if k ≤ Y z then 1 else 0

 theorem measurable_markTailIndicator {K : Finset Site} (z : K) (k : ℕ) :
    Measurable (markTailIndicator z k) :=
  (measurable_of_countable (fun n : ℕ ↦ if k ≤ n then (1 : ℝ) else 0)).comp (measurable_pi_apply z)

 theorem integrable_markTailIndicator {K : Finset Site} (z : K) (k : ℕ)
    (μ : Measure (Mark K)) [IsFiniteMeasure μ] : Integrable (markTailIndicator z k) μ := by
  refine ⟨(measurable_markTailIndicator z k).aestronglyMeasurable,
    HasFiniteIntegral.of_bounded (C := 1) ?_⟩
  filter_upwards [] with Y
  unfold markTailIndicator
  split_ifs <;> norm_num

 theorem integral_killedMark_tail (D K : Finset Site) (x : Site) (z : K) (k : ℕ) :
    ∫ Y, markTailIndicator z k Y ∂killedMarkLaw D K x = occupationTail D z k x := by
  exact integral_map (measurable_killedMark D K x).aemeasurable
    (measurable_markTailIndicator z k).aestronglyMeasurable

 theorem referenceMark_tail (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (z : K) (k : ℕ) (hk : 1 ≤ k) :
    (referenceMarkLaw D K α).real {Y | k ≤ Y z} =
      α / killedGreen D z z * (1 - 1 / killedGreen D z z) ^ (k - 1) := by
  have hi : (referenceMarkLaw D K α).real {Y | k ≤ Y z} =
      ∫ Y, markTailIndicator z k Y ∂referenceMarkLaw D K α := by
    have hs : MeasurableSet {Y : Mark K | k ≤ Y z} := (measurable_pi_apply z) measurableSet_Ici
    simpa [markTailIndicator, Set.indicator] using
      (integral_indicator_one (μ := referenceMarkLaw D K α)
        hs).symm
  rw [hi, integral_referenceMark D K α hα hcap _
    (fun x _ ↦ integrable_markTailIndicator z k (killedMarkLaw D K x))]
  have hz0 : markTailIndicator z k 0 = 0 := by
    simp [markTailIndicator, show ¬ k ≤ 0 by omega]
  rw [hz0, mul_zero, zero_add]
  simp only [integral_killedMark_tail, occupationTail_eq_probability]
  simp_rw [occupation_probability_ge D _ z (hKD z.property) k hk]
  calc
    _ = (α / killedGreen D z z * (1 - 1 / killedGreen D z z) ^ (k - 1)) *
        ∑ x ∈ K, equilibriumMeasure D K x * killedGreen D x z := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ = _ := by rw [equilibrium_green_on_set D K hKD z z.property, mul_one]

 theorem referenceMark_zero_mass (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (z : K) :
    (referenceMarkLaw D K α).real {Y | Y z = 0} = 1 - α / killedGreen D z z := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have he : {Y : Mark K | Y z = 0} = {Y : Mark K | 1 ≤ Y z}ᶜ := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    omega
  have hs : MeasurableSet {Y : Mark K | 1 ≤ Y z} := (measurable_pi_apply z) measurableSet_Ici
  rw [he, probReal_compl_eq_one_sub hs,
    referenceMark_tail D K hKD α hα hcap z 1 (by omega)]
  simp

 theorem referenceMark_positive_mass (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (z : K) (l : ℕ) (hl : 1 ≤ l) :
    (referenceMarkLaw D K α).real {Y | Y z = l} =
      α * (killedGreen D z z)⁻¹ ^ 2 * (1 - 1 / killedGreen D z z) ^ (l - 1) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have he : {Y : Mark K | Y z = l} = {Y : Mark K | l ≤ Y z} \ {Y : Mark K | l + 1 ≤ Y z} := by
    ext Y
    simp only [Set.mem_setOf_eq, Set.mem_sdiff]
    omega
  have hs : {Y : Mark K | l + 1 ≤ Y z} ⊆ {Y : Mark K | l ≤ Y z} := by
    intro Y hY
    change l + 1 ≤ Y z at hY
    change l ≤ Y z
    omega
  rw [he, measureReal_sdiff hs ((measurable_pi_apply z) measurableSet_Ici),
    referenceMark_tail D K hKD α hα hcap z l hl,
    referenceMark_tail D K hKD α hα hcap z (l + 1) (by omega)]
  simp only [Nat.add_sub_cancel]
  have hp : l = (l - 1) + 1 := by omega
  conv_lhs => rhs; rw [hp, pow_succ]
  ring

end SRWTightness
