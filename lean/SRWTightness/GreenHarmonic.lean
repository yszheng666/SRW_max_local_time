import SRWTightness.GreenMatrix

open Matrix

namespace SRWTightness

 theorem killedTransition_mulVec (D : Finset Site) (f : Site → ℝ)
    (hf : ∀ z, z ∉ D → f z = 0) (x : D) :
    (killedTransition D).mulVec (fun z : D ↦ f z) x =
      (1 / 4 : ℝ) * ∑ d : Direction, f ((x : Site) + step d) := by
  simp only [Matrix.mulVec, dotProduct, killedTransition, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hn : (x : Site) + step d ∈ D
  · let z : D := ⟨(x : Site) + step d, hn⟩
    have he (w : D) : (x : Site) + step d = (w : Site) ↔ w = z := by
      constructor
      · exact fun h ↦ Subtype.ext h.symm
      · intro h
        subst w
        rfl
    simp_rw [he]
    simp [z]
  · have he (w : D) : (x : Site) + step d ≠ (w : Site) := by
      intro h
      exact hn (h.symm ▸ w.property)
    simp [he, hf _ hn]

 theorem killedGreen_diag_ge_one (D : Finset Site) (y : Site) (hy : y ∈ D) :
    1 ≤ killedGreen D y y := by
  have h := killedGreen_first_step D y y hy
  have hn : 0 ≤ ∫ d, killedGreen D (y + step d) y ∂directionLaw :=
    MeasureTheory.integral_nonneg (fun d ↦ killedGreen_nonneg D _ y)
  simp at h
  linarith

/-- A function harmonic off one site is a scalar multiple of the corresponding Green column. -/
theorem harmonic_off_site_green_column (D : Finset Site) (f : Site → ℝ)
    (hf : ∀ z, z ∉ D → f z = 0) (y : D)
    (hh : ∀ z : D, z ≠ y → f z = (1 / 4 : ℝ) * ∑ d : Direction, f ((z : Site) + step d))
    (x : D) :
    f x = killedGreen D x y *
      (f y - (1 / 4 : ℝ) * ∑ d : Direction, f ((y : Site) + step d)) := by
  let c := f y - (1 / 4 : ℝ) * ∑ d : Direction, f ((y : Site) + step d)
  have he : (1 - killedTransition D).mulVec (fun z : D ↦ f z) =
      (fun z : D ↦ if z = y then c else 0) := by
    funext z
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    change f z - (killedTransition D).mulVec (fun z : D ↦ f z) z = _
    rw [killedTransition_mulVec D f hf]
    by_cases hz : z = y
    · subst z
      simp [c]
    · rw [if_neg hz, hh z hz, sub_self]
  have hinv : greenMatrix D * (1 - killedTransition D) = 1 :=
    Matrix.mul_eq_one_comm.mp (greenMatrix_right_inverse D)
  calc
    f x = (greenMatrix D).mulVec ((1 - killedTransition D).mulVec (fun z : D ↦ f z)) x := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    _ = _ := by
      rw [he]
      simp [Matrix.mulVec, dotProduct, greenMatrix, c]

end SRWTightness
