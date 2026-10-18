import SRWTightness.ActualForestUpper
import SRWTightness.CapacityMonotone
import Mathlib.Algebra.BigOperators.Ring.List

open MeasureTheory
namespace SRWTightness

/-- A list containing an entrance outside the support of every entrance kernel has zero actual mass. -/
theorem actual_entrance_list_zero (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (A B : Set Site) (hBK : B ⊆ (K : Set Site)) (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (rs : List (Site × PathWord)) (q : Site × PathWord) (hq : q ∈ rs) (hbad : q.1 ∉ B) :
    pathLaw.real {ω | killedChildRecords D K C x (fun y u ↦ (y, u)) ω = rs} = 0 := by
  classical
  let W : Site × PathWord → ℝ := fun p ↦ if p.1 ∈ B then 1 else 0
  have hW : ∀ p, 0 ≤ W p := by intro p; dsimp [W]; split <;> norm_num
  have hlocal : ∀ z ∈ B, ∀ p : Site × PathWord,
      pathLaw.real {ω | (z, killedPathWord C z ω) = p} ≤ W p := by
    intro z hz p
    by_cases hp : p.1 ∈ B
    · simp only [W, if_pos hp]
      exact measureReal_le_one
    · have he : {ω | (z, killedPathWord C z ω) = p} = (∅ : Set Sample) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        exact hp ((congrArg Prod.fst hω) ▸ hz)
      simp only [he, measureReal_empty, W, if_neg hp, le_refl]
  cases rs with
  | nil => simp at hq
  | cons r rs =>
    have hu := actual_forest_probability_upper D K C hKC hCD (fun y u ↦ (y, u)) A B
      hBK hA hU 1 (by norm_num) W hW (fun y _ ↦ setHitProbability_le_one D K y)
      hlocal x hUx r rs
    have he : {ω | (killedChildIntervals D K C x ω).length = (r :: rs).length ∧
        killedChildRecords D K C x (fun y u ↦ (y, u)) ω = r :: rs} =
        {ω | killedChildRecords D K C x (fun y u ↦ (y, u)) ω = r :: rs} := by
      ext ω
      constructor
      · exact And.right
      · intro hω
        refine ⟨?_, hω⟩
        simpa only [killedChildRecords, wordChildRecords, killedChildIntervals, List.length_map] using congrArg List.length hω
    have hz : ((r :: rs).map W).prod = 0 :=
      List.prod_eq_zero (List.mem_map.mpr ⟨q, hq, by exact if_neg hbad⟩)
    rw [he, hz, mul_zero] at hu
    exact le_antisymm hu measureReal_nonneg

/-- Every entrance in a positive actual record-list atom belongs to the entrance support. -/
theorem actual_entrance_list_support (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (A B : Set Site) (hBK : B ⊆ (K : Set Site)) (hA : domainExitBoundary C ⊆ A)
    (hU : ∀ x ∈ A, ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (x : Site) (hUx : ∀ᵐ z ∂competingEntranceLaw D K x, z ∈ B)
    (rs : List (Site × PathWord))
    (hrs : 0 < pathLaw.real {ω | killedChildRecords D K C x (fun y u ↦ (y, u)) ω = rs}) :
    ∀ q ∈ rs, q.1 ∈ B := by
  intro q hq
  by_contra hbad
  exact hrs.ne' (actual_entrance_list_zero D K C hKC hCD A B hBK hA hU x hUx rs q hq hbad)

end SRWTightness
