import SRWTightness.Capacity

open MeasureTheory

namespace SRWTightness

abbrev Mark (K : Finset Site) := K → ℕ

noncomputable def killedMark (D K : Finset Site) (x : Site) (ω : Sample) : Mark K :=
  fun z ↦ domainLocalTime D x z ω

 theorem measurable_killedMark (D K : Finset Site) (x : Site) :
    Measurable (killedMark D K x) :=
  measurable_pi_lambda _ (fun z ↦ measurable_domainLocalTime D x z)

noncomputable def killedMarkLaw (D K : Finset Site) (x : Site) : Measure (Mark K) :=
  pathLaw.map (killedMark D K x)

instance killedMarkLaw_isProbabilityMeasure (D K : Finset Site) (x : Site) :
    IsProbabilityMeasure (killedMarkLaw D K x) :=
  Measure.isProbabilityMeasure_map (measurable_killedMark D K x).aemeasurable

/-- Manuscript (2.14), including the additional zero atom. -/
noncomputable def referenceMarkLaw (D K : Finset Site) (α : ℝ) : Measure (Mark K) :=
  ENNReal.ofReal (1 - α * capacity D K) • Measure.dirac 0 +
    ∑ x ∈ K, ENNReal.ofReal (α * equilibriumMeasure D K x) • killedMarkLaw D K x

 theorem referenceMarkLaw_isProbabilityMeasure (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) :
    IsProbabilityMeasure (referenceMarkLaw D K α) := by
  constructor
  have hn (x : Site) : 0 ≤ α * equilibriumMeasure D K x :=
    mul_nonneg hα (equilibriumMeasure_nonneg D K x)
  have hs : (∑ x ∈ K, ENNReal.ofReal (α * equilibriumMeasure D K x)) =
      ENNReal.ofReal (α * capacity D K) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ hn x), ← Finset.mul_sum]
    rfl
  simp only [referenceMarkLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    Measure.finsetSum_apply, measure_univ]
  rw [hs, ← ENNReal.ofReal_add (sub_nonneg.mpr hcap) (mul_nonneg hα (capacity_nonneg D K))]
  simp

 theorem integrable_killedMark_coordinate (D K : Finset Site) (x : Site) (z : K) :
    Integrable (fun Y : Mark K ↦ (Y z : ℝ)) (killedMarkLaw D K x) := by
  apply (integrable_map_measure
    (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z)).aestronglyMeasurable)
    (measurable_killedMark D K x).aemeasurable).mpr
  exact integrable_domainLocalTime D x z

 theorem integral_killedMark_coordinate (D K : Finset Site) (x : Site) (z : K) :
    ∫ Y, (Y z : ℝ) ∂killedMarkLaw D K x = killedGreen D x z := by
  exact integral_map (measurable_killedMark D K x).aemeasurable
    (((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp
      (measurable_pi_apply z)).aestronglyMeasurable)


end SRWTightness
