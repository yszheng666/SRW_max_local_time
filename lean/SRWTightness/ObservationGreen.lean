import SRWTightness.GreenLift
import SRWTightness.WeightedResolvent

open Matrix

namespace SRWTightness

noncomputable def observationGreen (D A : Finset Site) : Matrix A A ℝ :=
  fun x y ↦ killedGreen D x y

noncomputable def observationLift (D A : Finset Site) (c : A → ℝ) (x : Site) : ℝ :=
  ∑ y : A, killedGreen D x y * c y

 theorem greenLift_extendZero (D A : Finset Site) (hAD : A ⊆ D) (c : A → ℝ) (x : Site) :
    greenLift D (fun y : D ↦ extendZero A c y) x = observationLift D A c x := by
  unfold greenLift observationLift
  rw [Finset.sum_coe_sort D (fun y ↦ killedGreen D x y * extendZero A c y)]
  have hs : (∑ y ∈ A, killedGreen D x y * extendZero A c y) =
      ∑ y ∈ D, killedGreen D x y * extendZero A c y := by
    apply Finset.sum_subset hAD
    intro y hy hyA
    rw [extendZero_not_mem A c y hyA, mul_zero]
  rw [← hs, ← Finset.sum_coe_sort A (fun y ↦ killedGreen D x y * extendZero A c y)]
  apply Finset.sum_congr rfl
  intro y hy
  rw [extendZero_mem]

 theorem observationLift_poisson (D A : Finset Site) (hAD : A ⊆ D) (c : A → ℝ) (x : D) :
    observationLift D A c x - (1 / 4 : ℝ) *
      ∑ d : Direction, observationLift D A c ((x : Site) + step d) = extendZero A c x := by
  simpa only [greenLift_extendZero D A hAD c] using greenLift_poisson D (fun y : D ↦ extendZero A c y) x

 theorem observationLift_zero_of_not_mem (D A : Finset Site) (c : A → ℝ)
    (x : Site) (hx : x ∉ D) : observationLift D A c x = 0 := by
  simp [observationLift, killedGreen_zero_of_not_mem D x _ hx]

noncomputable def observationResolventMatrix (D A : Finset Site) (v : A → ℝ) : Matrix A A ℝ :=
  1 - (observationGreen D A - 1) * Matrix.diagonal (fun x ↦ v x - 1)

 theorem observationResolventMatrix_isUnit (D A : Finset Site) (hAD : A ⊆ D) (v : A → ℝ)
    (hv0 : ∀ x, 0 ≤ v x) (hv1 : ∀ x, v x ≤ 1) : IsUnit (observationResolventMatrix D A v) := by
  have hker (u : A → ℝ) (hu : (observationResolventMatrix D A v).mulVec u = 0) : u = 0 := by
    let c : A → ℝ := fun x ↦ (v x - 1) * u x
    let F := observationLift D A c
    have hcvec : (Matrix.diagonal (fun x ↦ v x - 1)).mulVec u = c := by
      funext y
      exact Matrix.mulVec_diagonal _ _ _
    have hr (x : A) : F x - c x = u x := by
      have he := congrFun hu x
      simp only [observationResolventMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
        ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Pi.sub_apply, Pi.zero_apply] at he
      rw [hcvec] at he
      change u x - ((observationGreen D A).mulVec c x - c x) = 0 at he
      change (observationGreen D A).mulVec c x - c x = u x
      linarith
    have hF : F = 0 := by
      apply weighted_harmonic_zero D F (observationLift_zero_of_not_mem D A c)
      intro x hx
      have hp := observationLift_poisson D A hAD c (⟨x, hx⟩ : D)
      change F x - (1 / 4 : ℝ) * ∑ d : Direction, F (x + step d) = extendZero A c x at hp
      by_cases hxA : x ∈ A
      · let xx : A := ⟨x, hxA⟩
        have hrx := hr xx
        change F x - c xx = u xx at hrx
        have hce : extendZero A c x = c xx := by simp [extendZero, hxA, xx]
        rw [hce] at hp
        have hav : (1 / 4 : ℝ) * ∑ d : Direction, F (x + step d) = u xx := by linarith
        refine ⟨v xx, hv0 xx, hv1 xx, ?_⟩
        rw [hav]
        dsimp [c] at hrx
        nlinarith
      · rw [extendZero_not_mem A c x hxA] at hp
        exact ⟨1, by norm_num, le_rfl, by linarith⟩
    funext x
    have hp := observationLift_poisson D A hAD c (⟨(x : Site), hAD x.property⟩ : D)
    change F x - (1 / 4 : ℝ) * ∑ d : Direction, F ((x : Site) + step d) = extendZero A c x at hp
    rw [hF] at hp
    simp only [Pi.zero_apply, Finset.sum_const_zero, mul_zero, sub_self, extendZero_mem] at hp
    have hrx := hr x
    rw [hF] at hrx
    simp only [Pi.zero_apply, ← hp, sub_self] at hrx
    exact hrx.symm
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u w huw
  have hz : (observationResolventMatrix D A v).mulVec (u - w) = 0 := by
    rw [Matrix.mulVec_sub, huw, sub_self]
  exact sub_eq_zero.mp (hker (u - w) hz)

end SRWTightness
