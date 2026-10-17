import SRWTightness.WordMark

open MeasureTheory
namespace SRWTightness

/-- The common reference mark with full crossing order: an additional empty atom and the
same equilibrium-weighted killed walks used by the occupation reference law. -/
noncomputable def referenceWordMarkLaw (D K : Finset Site) (α : ℝ) : Measure WordMark :=
  ENNReal.ofReal (1 - α * capacity D K) • Measure.dirac none +
    ∑ x ∈ K, ENNReal.ofReal (α * equilibriumMeasure D K x) • killedWordMarkLaw D x

/-- The ordered reference mark has the same normalization criterion as its occupation projection. -/
theorem referenceWordMarkLaw_probability (D K : Finset Site) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) :
    IsProbabilityMeasure (referenceWordMarkLaw D K α) := by
  constructor
  have hn (x : Site) : 0 ≤ α * equilibriumMeasure D K x :=
    mul_nonneg hα (equilibriumMeasure_nonneg D K x)
  have hs : (∑ x ∈ K, ENNReal.ofReal (α * equilibriumMeasure D K x)) =
      ENNReal.ofReal (α * capacity D K) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ ↦ hn x), ← Finset.mul_sum]
    rfl
  simp only [referenceWordMarkLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one,
    Measure.finsetSum_apply, measure_univ]
  rw [hs, ← ENNReal.ofReal_add (sub_nonneg.mpr hcap)
    (mul_nonneg hα (capacity_nonneg D K))]
  simp

end SRWTightness
