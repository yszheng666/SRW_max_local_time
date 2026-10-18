import SRWTightness.GeometricCompetingComparison
import SRWTightness.InsideChildRecordReal
import SRWTightness.ActualRecordKernel

open MeasureTheory
namespace SRWTightness

/-- An initial inner entrance produces one certain root, then a geometric tail of actual ordered records. -/
theorem actual_geometric_child_records {R : Type*}
    (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (F : Site → PathWord → R) (A B : Set Site) (hBK : B ⊆ (K : Set Site))
    (hCA : domainExitBoundary C ⊆ A)
    (hUs : ∀ y ∈ A, ∀ᵐ z ∂competingEntranceLaw D K y, z ∈ B)
    (p ε : ℝ) (hp : 0 ≤ p) (hpHalf : p ≤ 1 / 2) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 2)
    (hescape : ∀ y ∈ A, |competingExitMass D K y - p| ≤ ε * p)
    (η Q : R → ℝ) (hQ : ∀ u, 0 ≤ Q u)
    (hF : ∀ z ∈ B, ∀ u, Real.exp (-η u) * Q u ≤
        pathLaw.real {ω | F z (killedPathWord C z ω) = u} ∧
      pathLaw.real {ω | F z (killedPathWord C z ω) = u} ≤ Real.exp (η u) * Q u)
    (x : Site) (hx : x ∈ B) (r : R) (rs : List R) :
    let E := 2 * ε * ((rs.length : ℝ) + 1) + ((r :: rs).map η).sum
    let W := p * (1 - p) ^ rs.length * ((r :: rs).map Q).prod
    Real.exp (-E) * W ≤ pathLaw.real {ω | killedChildRecords D K C x F ω = r :: rs} ∧
      pathLaw.real {ω | killedChildRecords D K C x F ω = r :: rs} ≤ Real.exp E * W := by
  dsimp only
  let S : Site → R → Measure Site := fun z u ↦
    recordExitSlice C z (fun ω ↦ F z (killedPathWord C z ω)) u
  have hSf (z : Site) (u : R) : IsFiniteMeasure (S z u) := by dsimp [S]; infer_instance
  have hSs : ∀ z ∈ B, ∀ u, ∀ᵐ y ∂S z u, y ∈ A := by
    intro z hz u
    filter_upwards [recordExitSlice_supported C z (hKC (hBK hz))
      (fun ω ↦ F z (killedPathWord C z ω)) u] with y hy
    exact hCA hy
  have hS : ∀ z ∈ B, ∀ u, Real.exp (-η u) * Q u ≤ (S z u).real Set.univ ∧
      (S z u).real Set.univ ≤ Real.exp (η u) * Q u := by
    intro z hz u
    dsimp only [S]
    rw [recordExitSlice_mass]
    exact hF z hz u
  have ht := actual_geometric_record_weight_comparison D K S A B hSf hUs hSs
    p ε hp hpHalf hε hsmall hescape η Q hQ hS
  let lo := Real.exp (-orderedRecordError (2 * ε) η rs) * geometricOrderedReferenceWeight p Q rs
  let hi := Real.exp (orderedRecordError (2 * ε) η rs) * geometricOrderedReferenceWeight p Q rs
  let P := fun y ↦ pathLaw.real {ω | killedChildRecords D K C y F ω = rs}
  have htail : ∀ y ∈ A, lo ≤ P y ∧ P y ≤ hi := by
    intro y hy
    dsimp only [lo, hi, P]
    rw [actual_ordered_record_kernel D K C hKC hCD F rs y]
    exact ht rs y hy
  have href := geometricOrderedReferenceWeight_nonneg p hp (by linarith) Q hQ rs
  have hlo : 0 ≤ lo := mul_nonneg (Real.exp_nonneg _) href
  have hhi : 0 ≤ hi := mul_nonneg (Real.exp_nonneg _) href
  letI := hSf x r
  have hI := integral_bounds_on_support (S x r) A (hSs x hx r) P lo hi hlo htail
  have hl := (mul_le_mul_of_nonneg_left (hS x hx r).1 hlo).trans hI.1
  have hu := hI.2.trans (mul_le_mul_of_nonneg_left (hS x hx r).2 hhi)
  have hE : η r + orderedRecordError (2 * ε) η rs =
      2 * ε * ((rs.length : ℝ) + 1) + ((r :: rs).map η).sum := by
    rw [orderedRecordError_sum]
    simp only [List.map_cons, List.sum_cons]
    ring
  have hW : Q r * geometricOrderedReferenceWeight p Q rs =
      p * (1 - p) ^ rs.length * ((r :: rs).map Q).prod := by
    rw [geometricOrderedReferenceWeight_product]
    simp only [List.map_cons, List.prod_cons]
    ring
  rw [killedChildRecords_inside_cons_probability_real D K C hKC hCD x (hBK hx) F r rs]
  constructor
  · calc
      _ = lo * (Real.exp (-η r) * Q r) := by
        rw [← hE, ← hW]
        simp only [lo, neg_add, Real.exp_add]
        ring
      _ ≤ _ := hl
  · calc
      _ ≤ hi * (Real.exp (η r) * Q r) := hu
      _ = _ := by
        rw [← hE, ← hW]
        simp only [hi, Real.exp_add]
        ring

end SRWTightness
