import SRWTightness.SetOccupation
import SRWTightness.GreenHarmonic
import SRWTightness.GreenSymmetry

open Matrix

namespace SRWTightness

/-- The boundary charge of the actual hitting probability. -/
noncomputable def equilibriumCharge (D K : Finset Site) (x : Site) : ℝ :=
  if x ∈ K then 1 - (1 / 4 : ℝ) *
    ∑ d : Direction, setHitProbability D K (x + step d) else 0

 theorem equilibriumCharge_eq_laplacian (D K : Finset Site) (hKD : K ⊆ D) (x : D) :
    equilibriumCharge D K x = setHitProbability D K x -
      (1 / 4 : ℝ) * ∑ d : Direction, setHitProbability D K ((x : Site) + step d) := by
  by_cases hx : (x : Site) ∈ K
  · rw [equilibriumCharge, if_pos hx, setHitProbability_one D K x (hKD hx) hx]
  · rw [equilibriumCharge, if_neg hx, setHitProbability_harmonic D K x x.property hx, sub_self]

 theorem green_mul_equilibriumCharge (D K : Finset Site) (hKD : K ⊆ D) (z : Site) :
    ∑ x ∈ K, killedGreen D z x * equilibriumCharge D K x = setHitProbability D K z := by
  by_cases hz : z ∈ D
  · let zz : D := ⟨z, hz⟩
    have he : (1 - killedTransition D).mulVec (fun x : D ↦ setHitProbability D K x) =
        (fun x : D ↦ equilibriumCharge D K x) := by
      funext x
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      change setHitProbability D K x - _ = _
      rw [killedTransition_mulVec D _ (fun y hy ↦ setHitProbability_zero_of_not_mem D K y hy)]
      exact (equilibriumCharge_eq_laplacian D K hKD x).symm
    have hm : (greenMatrix D).mulVec (fun x : D ↦ equilibriumCharge D K x) zz =
        setHitProbability D K z := by
      rw [← he, Matrix.mulVec_mulVec, mul_eq_one_comm.mp (greenMatrix_right_inverse D),
        Matrix.one_mulVec]
    have hsum : (∑ x ∈ D, killedGreen D z x * equilibriumCharge D K x) =
        setHitProbability D K z := by
      rw [← Finset.sum_coe_sort D (fun x ↦ killedGreen D z x * equilibriumCharge D K x)]
      exact hm
    rw [← hsum]
    apply Finset.sum_subset hKD
    intro x hx hxK
    simp [equilibriumCharge, hxK]
  · simp [killedGreen_zero_of_not_mem D z _ hz, setHitProbability_zero_of_not_mem D K z hz]

 theorem green_equilibriumCharge_on_set (D K : Finset Site) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) : ∑ x ∈ K, killedGreen D z x * equilibriumCharge D K x = 1 := by
  rw [green_mul_equilibriumCharge D K hKD z, setHitProbability_one D K z (hKD hz) hz]

 theorem equilibriumCharge_green_on_set (D K : Finset Site) (hKD : K ⊆ D)
    (z : Site) (hz : z ∈ K) : ∑ x ∈ K, equilibriumCharge D K x * killedGreen D x z = 1 := by
  calc
    _ = ∑ x ∈ K, killedGreen D z x * equilibriumCharge D K x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [killedGreen_symm D x z (hKD hx) (hKD hz), mul_comm]
    _ = 1 := green_equilibriumCharge_on_set D K hKD z hz

end SRWTightness
