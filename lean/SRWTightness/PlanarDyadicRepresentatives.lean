import SRWTightness.FinitePartitionRepresentative
import SRWTightness.PlanarDyadicCells
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace SRWTightness

/-- A deterministic representative of the dyadic cell containing each observation point. -/
noncomputable def planarDyadicRepresentative {ι : Type*}
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (R : ℝ) (n : ℕ) (x : ι) : ι :=
  finitePartitionRepresentative J (fun i ↦ planarDyadicCell R n (p i)) o
    (planarDyadicCell R n (p x))

/-- Representatives retain their cell and belong to the finite observation set. -/
theorem planarDyadicRepresentative_spec {ι : Type*}
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (R : ℝ) (n : ℕ) (x : ι) (hx : x ∈ J) :
    planarDyadicRepresentative J p o R n x ∈ J ∧
      planarDyadicCell R n (p (planarDyadicRepresentative J p o R n x)) =
        planarDyadicCell R n (p x) :=
  finitePartitionRepresentative_spec J _ o _ ⟨x, hx, rfl⟩

/-- There are at most dimension-two many distinct representatives at each scale. -/
theorem planarDyadicRepresentative_card {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (R : ℝ) (hR : 0 < R) (n : ℕ)
    (hp : ∀ x ∈ J, (p x).1 ^ 2 + (p x).2 ^ 2 ≤ R ^ 2) :
    (J.image (planarDyadicRepresentative J p o R n)).card ≤ 9 * 4 ^ n := by
  exact (finitePartitionRepresentative_card_le J _ o (planarDyadicCellLabels n)
    (fun x hx ↦ planarDyadicCell_mem_labels R hR n (p x) (hp x hx))).trans
      (planarDyadicCellLabels_card n)

/-- Fine enough dyadic cells distinguish every distinct planar location in a finite family. -/
theorem planarDyadicCell_eventually_separates {ι : Type*} [Fintype ι]
    (p : ι → ℝ × ℝ) (R : ℝ) (hR : 0 < R) :
    ∀ᶠ n : ℕ in atTop, ∀ i j, planarDyadicCell R n (p i) = planarDyadicCell R n (p j) →
      p i = p j := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hij : p i = p j
  · exact Eventually.of_forall (fun _ _ ↦ hij)
  have hd : 0 < ((p i).1 - (p j).1) ^ 2 + ((p i).2 - (p j).2) ^ 2 := by
    by_contra h
    have hh := le_of_not_gt h
    apply hij
    apply Prod.ext <;> nlinarith [sq_nonneg ((p i).1 - (p j).1),
      sq_nonneg ((p i).2 - (p j).2)]
  have hi : Tendsto (fun n : ℕ ↦ ((2 : ℝ) ^ n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have ht : Tendsto (fun n : ℕ ↦ 2 * (R / 2 ^ n) ^ 2) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_pow (by decide : 2 ≠ 0)] using
      ((hi.const_mul R).pow 2).const_mul 2
  filter_upwards [ht.eventually_lt_const hd] with n hn hcell
  exact (not_lt_of_ge (planarDyadicCell_distance R hR n (p i) (p j) hcell)) hn |>.elim

/-- At a sufficiently fine scale, each representative has exactly the original planar location. -/
theorem planarDyadicRepresentative_eventually_exact {ι : Type*} [Fintype ι]
    (J : Finset ι) (p : ι → ℝ × ℝ) (o : ι) (R : ℝ) (hR : 0 < R) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ J, p (planarDyadicRepresentative J p o R n x) = p x := by
  filter_upwards [planarDyadicCell_eventually_separates p R hR] with n hn
  intro x hx
  exact hn _ _ (planarDyadicRepresentative_spec J p o R n x hx).2

end SRWTightness
