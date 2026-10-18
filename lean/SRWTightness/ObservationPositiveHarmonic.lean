import SRWTightness.NonnegativeResolventOne
import SRWTightness.ObservationGreenRowNonnegative

open Matrix

namespace SRWTightness

/-- Strict finite row bounds admit a common nonnegative contraction constant. -/
theorem finite_strict_row_uniform (ι : Type) [Fintype ι] (r : ι → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : ∀ i, r i < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ i, r i ≤ q := by
  classical
  by_cases hi : Nonempty ι
  · obtain ⟨i⟩ := hi
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image Finset.univ r
      ⟨i, Finset.mem_univ i⟩
    exact ⟨r k, hr0 k, hr1 k, fun j ↦ hmax j (Finset.mem_univ j)⟩
  · exact ⟨0, le_rfl, zero_lt_one, fun i ↦ (hi ⟨i⟩).elim⟩

/-- The discrete occupation row condition supplies a positive weighted harmonic majorant. -/
theorem observation_positive_harmonic (D A : Finset Site) (hAD : A ⊆ D)
    (v : A → ℝ) (hv : ∀ z, 1 ≤ v z)
    (hrow : ∀ y : A, ∑ z : A,
      |killedGreen D y z - (if y = z then 1 else 0)| * |v z - 1| < 1) :
    ∃ F : Site → ℝ, (∀ x, 1 ≤ F x) ∧
      ∀ x ∈ D, F x = siteWeight A v x *
        ((1 / 4 : ℝ) * ∑ d : Direction, F (x + step d)) := by
  classical
  let M := (observationGreen D A - 1) * Matrix.diagonal (fun z ↦ v z - 1)
  have hM (y z : A) : 0 ≤ M y z := by
    dsimp [M]
    rw [Matrix.mul_diagonal]
    exact mul_nonneg (observationGreen_sub_one_entry_nonneg D A hAD y z)
      (sub_nonneg.mpr (hv z))
  have hmrow (y : A) : ∑ z, |M y z| < 1 := by
    simpa only [M, Matrix.mul_diagonal, observationGreen, Matrix.sub_apply,
      Matrix.one_apply, abs_mul] using hrow y
  obtain ⟨q, hq, hq1, hqrow⟩ := finite_strict_row_uniform A (fun y ↦ ∑ z, |M y z|)
    (fun y ↦ Finset.sum_nonneg (fun z _ ↦ abs_nonneg _)) hmrow
  let u : A → ℝ := (1 - M)⁻¹.mulVec 1
  have hu1 : ∀ z, 1 ≤ u z := nonnegative_resolvent_one_ge_one A M q hq hq1 hM hqrow
  have hunit := matrix_row_contraction_isUnit A M q hq hq1 hqrow
  have he : (1 - M).mulVec u = 1 := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).mp hunit), Matrix.one_mulVec]
  let c : A → ℝ := fun z ↦ (v z - 1) * u z
  let F : Site → ℝ := fun x ↦ 1 + observationLift D A c x
  have hc (z : A) : 0 ≤ c z := mul_nonneg (sub_nonneg.mpr (hv z))
    (zero_le_one.trans (hu1 z))
  have hr (z : A) : F z - c z = u z := by
    have hh := congrFun he z
    have hcvec : (Matrix.diagonal (fun z ↦ v z - 1)).mulVec u = c := by
      funext y
      exact Matrix.mulVec_diagonal _ _ _
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.one_apply] at hh
    dsimp [M] at hh
    rw [← Matrix.mulVec_mulVec, hcvec, Matrix.sub_mulVec, Matrix.one_mulVec] at hh
    change u z - (observationLift D A c z - c z) = 1 at hh
    dsimp [F]
    linarith
  refine ⟨F, ?_, ?_⟩
  · intro x
    exact le_add_of_nonneg_right (Finset.sum_nonneg
      (fun z _ ↦ mul_nonneg (killedGreen_nonneg D x z) (hc z)))
  · intro x hx
    have hp := observationLift_poisson D A hAD c (⟨x, hx⟩ : D)
    have hav : (1 / 4 : ℝ) * ∑ d : Direction, F (x + step d) =
        1 + (1 / 4 : ℝ) * ∑ d : Direction, observationLift D A c (x + step d) := by
      simp only [F, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
      norm_num [Direction]
      ring
    rw [hav]
    by_cases hxA : x ∈ A
    · let xx : A := ⟨x, hxA⟩
      have hrx := hr xx
      have hce : extendZero A c x = c xx := by simp [extendZero, hxA, xx]
      rw [hce] at hp
      have hw : siteWeight A v x = v xx := by simp [siteWeight, hxA, xx]
      rw [hw]
      change 1 + observationLift D A c x - c xx = u xx at hrx
      change 1 + observationLift D A c x = _
      have havu : 1 + (1 / 4 : ℝ) *
          ∑ d : Direction, observationLift D A c (x + step d) = u xx := by
        linarith
      rw [havu]
      change 1 + observationLift D A c x - (v xx - 1) * u xx = u xx at hrx
      nlinarith
    · rw [extendZero_not_mem A c x hxA] at hp
      simp only [siteWeight, dif_neg hxA, one_mul, F]
      linarith

end SRWTightness
