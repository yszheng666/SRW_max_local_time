import SRWTightness.CountableRecordEventComparison
import SRWTightness.IndependentForestLaw

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Single-root atom comparisons extend to every permitted joint event, retaining the lower constant. -/
theorem single_root_event_comparison {Ω M : Type*} [MeasurableSpace Ω] [Countable M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    (P : Measure Ω) [IsFiniteMeasure P] (F : Ω → List M)
    (μ : Measure M) [IsProbabilityMeasure μ] (η : M → ℝ) (c E : ℝ) (hc : 0 ≤ c)
    (s : Set (List M)) (hlen : ∀ rs ∈ s, rs.length = 1)
    (hf : ∀ rs ∈ s, MeasurableSet (F ⁻¹' {rs}))
    (herr : ∀ r, [r] ∈ s → η r ≤ E)
    (hpoint : ∀ r, [r] ∈ s →
      c * Real.exp (-η r) * μ.real {r} ≤ P.real {ω | F ω = [r]} ∧
        P.real {ω | F ω = [r]} ≤ Real.exp (η r) * μ.real {r}) :
    ENNReal.ofReal (c * Real.exp (-E)) * independentForestLaw μ 1 s ≤ P (F ⁻¹' s) ∧
      P (F ⁻¹' s) ≤ ENNReal.ofReal (Real.exp E) * independentForestLaw μ 1 s := by
  rw [independentForestLaw_event μ 1 s hlen]
  apply countable_record_event_comparison P F
    (fun rs ↦ ENNReal.ofReal ((rs.map (fun v ↦ μ.real {v})).prod)) s _ _ hf
  intro rs hrs
  cases rs with
  | nil => have hh := hlen [] hrs; simp only [List.length_nil] at hh; omega
  | cons r rs =>
    have hz : rs = [] := by
      cases rs with
      | nil => rfl
      | cons z zs =>
        have hh := hlen (r :: z :: zs) hrs
        simp only [List.length_cons] at hh
        omega
    subst rs
    have hpoint' := hpoint r hrs
    have hlo : c * Real.exp (-E) * μ.real {r} ≤ P.real {ω | F ω = [r]} :=
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg (herr r hrs))) hc)
        (measureReal_nonneg)).trans hpoint'.1
    have hhi : P.real {ω | F ω = [r]} ≤ Real.exp E * μ.real {r} :=
      hpoint'.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (herr r hrs))
        measureReal_nonneg)
    have hset : F ⁻¹' {[r]} = {ω | F ω = [r]} := by ext ω; rfl
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hset]
    constructor
    · simpa only [ENNReal.ofReal_mul (mul_nonneg hc (Real.exp_nonneg _)),
        ofReal_measureReal (measure_ne_top P _)] using ENNReal.ofReal_le_ofReal hlo
    · simpa only [ENNReal.ofReal_mul (Real.exp_nonneg _),
        ofReal_measureReal (measure_ne_top P _)] using ENNReal.ofReal_le_ofReal hhi

end SRWTightness
