import SRWTightness.ActualForestUpper

open MeasureTheory

namespace SRWTightness

/-- Independent reference weights collect all single-root errors into one exponential factor. -/
theorem forest_exponential_product {M : Type*} (η Q : M → ℝ) (rs : List M) :
    (rs.map (fun r ↦ Real.exp (η r) * Q r)).prod =
      Real.exp ((rs.map η).sum) * (rs.map Q).prod := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, ih, Real.exp_add]
    ring

/-- Actual fixed-forest upper comparison, retaining the return decay and total root error. -/
theorem actual_forest_exponential_upper {M : Type*}
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → M) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (η Q : M → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hp : ∀ x ∈ A, setHitProbability D K x ≤ ρ)
    (hF : ∀ z ∈ B, ∀ r, pathLaw.real {ω | F z (killedPathWord C z ω) = r} ≤ Real.exp (η r) * Q r)
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B) (r : M) (rs : List M) :
    pathLaw.real {ω | (killedChildIntervals D K C x ω).length = (r :: rs).length ∧
      killedChildRecords D K C x F ω = r :: rs} ≤
        ρ ^ rs.length * Real.exp (((r :: rs).map η).sum) * ((r :: rs).map Q).prod := by
  have hh := actual_forest_probability_upper D K C hKC hCD F A B hBK hA hU ρ hρ
    (fun r ↦ Real.exp (η r) * Q r) (fun r ↦ mul_nonneg (Real.exp_nonneg _) (hQ r))
    hp hF x hUx r rs
  rw [forest_exponential_product] at hh
  simpa only [mul_assoc] using hh

end SRWTightness
