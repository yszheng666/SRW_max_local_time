import SRWTightness.ActualForestExponential
import SRWTightness.CountableRecordEventComparison

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Joint fixed-size forest events preserve the return decay and a uniform total error factor. -/
theorem actual_forest_event_upper {M : Type*} [Countable M]
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hp : ∀ x ∈ A, setHitProbability D K x ≤ ρ)
    (hF : ∀ z ∈ B, ∀ r, pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp (η r) * Q r)
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B) (j : ℕ) (hj : 1 ≤ j)
    (s : Set (List M)) (E : ℝ) (hlen : ∀ rs ∈ s, rs.length = j)
    (herr : ∀ rs ∈ s, (rs.map η).sum ≤ E) :
    pathLaw {ω | killedChildRecords D K C x F ω ∈ s} ≤
      ENNReal.ofReal (ρ ^ (j - 1) * Real.exp E) *
        (∑' rs : s, ENNReal.ofReal ((rs.val.map Q).prod)) := by
  have hpoint : ∀ rs ∈ s,
      pathLaw.real {ω | killedChildRecords D K C x F ω = rs} ≤
        (ρ ^ (j - 1) * Real.exp E) * (rs.map Q).prod := by
    intro vs hvs
    cases vs with
    | nil => have hh := hlen [] hvs; simp only [List.length_nil] at hh; omega
    | cons r rs =>
      have hh := actual_forest_exponential_upper D K C hKC hCD F A B hBK hA hU
        ρ hρ η Q hQ hp hF x hUx r rs
      have hset : {ω | (killedChildIntervals D K C x ω).length = (r :: rs).length ∧
          killedChildRecords D K C x F ω = r :: rs} =
          {ω | killedChildRecords D K C x F ω = r :: rs} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        constructor
        · exact fun h ↦ h.2
        · intro h
          exact ⟨by rw [← killedChildRecords_length D K C x F ω, h], h⟩
      rw [hset] at hh
      have hlength : rs.length = j - 1 := by
        have hh := hlen (r :: rs) hvs
        simp only [List.length_cons] at hh
        omega
      rw [hlength] at hh
      apply hh.trans
      have hprod : 0 ≤ ((r :: rs).map Q).prod := by
        apply List.prod_nonneg
        intro a ha
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
        exact hQ v
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (herr _ hvs)) (pow_nonneg hρ _)) hprod
  have hf : ∀ rs ∈ s, MeasurableSet ((killedChildRecords D K C x F) ⁻¹' {rs}) := by
    intro rs hrs
    exact measurableSet_killedChildRecords_eq D K C x F rs
  have hb := countable_record_event_comparison pathLaw (killedChildRecords D K C x F)
    (fun rs ↦ ENNReal.ofReal ((rs.map Q).prod)) s 0
    (ENNReal.ofReal (ρ ^ (j - 1) * Real.exp E)) hf
  apply hb _ |>.2
  intro rs hrs
  constructor
  · simp only [zero_mul]; exact bot_le
  · have hh := ENNReal.ofReal_le_ofReal (hpoint rs hrs)
    have hset : (killedChildRecords D K C x F) ⁻¹' {rs} =
        {ω | killedChildRecords D K C x F ω = rs} := by ext ω; rfl
    rw [hset]
    simpa only [ofReal_measureReal (measure_ne_top pathLaw _),
      ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hρ _) (Real.exp_nonneg E))] using hh

end SRWTightness
