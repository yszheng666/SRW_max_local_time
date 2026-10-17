import SRWTightness.CountableRecordFunctional

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Nonnegative functionals of the actual stopped SRW inherit uniform record error bounds. -/
theorem killed_record_functional_exponential {R : Type*} [Countable R]
    (D : Finset Site) (x : Site) (F : PathWord → R) (q e : R → ℝ)
    (s : Set R) (g : R → ℝ≥0∞) (E : ℝ) (hq : ∀ r, 0 ≤ q r)
    (hg : ∀ r, r ∉ s → g r = 0) (he : ∀ r ∈ s, e r ≤ E)
    (h : ∀ r ∈ s,
      Real.exp (-e r) * q r ≤ pathLaw.real {ω | F (killedPathWord D x ω) = r} ∧
      pathLaw.real {ω | F (killedPathWord D x ω) = r} ≤ Real.exp (e r) * q r) :
    ENNReal.ofReal (Real.exp (-E)) * (∑' r, g r * ENNReal.ofReal (q r)) ≤
      ∫⁻ ω, g (F (killedPathWord D x ω)) ∂pathLaw ∧
    (∫⁻ ω, g (F (killedPathWord D x ω)) ∂pathLaw) ≤
      ENNReal.ofReal (Real.exp E) * (∑' r, g r * ENNReal.ofReal (q r)) := by
  letI : MeasurableSpace R := ⊤
  letI : MeasurableSingletonClass R := ⟨fun _ ↦ trivial⟩
  apply countable_record_functional_comparison pathLaw
    (fun ω ↦ F (killedPathWord D x ω)) (measurable_killed_word_record D x F)
    (fun r ↦ ENNReal.ofReal (q r)) g s hg
  intro r hr
  have hlo := (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (neg_le_neg (he r hr))) (hq r)).trans (h r hr).1
  have hhi := (h r hr).2.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (he r hr)) (hq r))
  have hset : (fun ω ↦ F (killedPathWord D x ω)) ⁻¹' {r} =
      {ω | F (killedPathWord D x ω) = r} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [hset]
  constructor
  · simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le,
      ofReal_measureReal (measure_ne_top pathLaw _),
      Set.preimage_setOf_eq, Set.mem_singleton_iff] using ENNReal.ofReal_le_ofReal hlo
  · simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le,
      ofReal_measureReal (measure_ne_top pathLaw _),
      Set.preimage_setOf_eq, Set.mem_singleton_iff] using ENNReal.ofReal_le_ofReal hhi

end SRWTightness
