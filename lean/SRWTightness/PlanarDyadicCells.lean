import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace SRWTightness

/-- Equal floor cells force real coordinates to be within one cell width. -/
theorem floor_cell_distance_le (a b w : ℝ) (hw : 0 < w)
    (h : Int.floor (a / w) = Int.floor (b / w)) : |a - b| ≤ w := by
  have ha := Int.floor_le (a / w)
  have ha' := Int.lt_floor_add_one (a / w)
  have hb := Int.floor_le (b / w)
  have hb' := Int.lt_floor_add_one (b / w)
  rw [← h] at hb hb'
  have hh : |a / w - b / w| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [← sub_div, abs_div, abs_of_pos hw] at hh
  simpa only [one_mul] using (div_le_iff₀ hw).mp hh

/-- The square cell at a dyadic mesh width inside a radius-R planar box. -/
noncomputable def planarDyadicCell (R : ℝ) (n : ℕ) (p : ℝ × ℝ) : ℤ × ℤ :=
  (Int.floor (p.1 / (R / 2 ^ n)), Int.floor (p.2 / (R / 2 ^ n)))

/-- Cell labels for the radius-R box form an explicit finite integer square. -/
def planarDyadicCellLabels (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-((2 ^ n : ℕ) : ℤ)) ((2 ^ n : ℕ) : ℤ)).product
    (Finset.Icc (-((2 ^ n : ℕ) : ℤ)) ((2 ^ n : ℕ) : ℤ))

/-- A radius-R disk is covered by these finite dyadic cells. -/
theorem planarDyadicCell_mem_labels (R : ℝ) (hR : 0 < R) (n : ℕ) (p : ℝ × ℝ)
    (hp : p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2) :
    planarDyadicCell R n p ∈ planarDyadicCellLabels n := by
  have hN : 0 < (2 : ℝ) ^ n := by positivity
  have hw : 0 < R / (2 : ℝ) ^ n := div_pos hR hN
  have hcoord (a : ℝ) (ha : |a| ≤ R) :
      -((2 ^ n : ℕ) : ℤ) ≤ Int.floor (a / (R / 2 ^ n)) ∧
        Int.floor (a / (R / 2 ^ n)) ≤ ((2 ^ n : ℕ) : ℤ) := by
    have ha' := abs_le.mp ha
    have hlo : -(2 : ℝ) ^ n ≤ a / (R / 2 ^ n) := by
      apply (le_div_iff₀ hw).mpr
      field_simp
      nlinarith
    have hhi : a / (R / 2 ^ n) ≤ (2 : ℝ) ^ n := by
      apply (div_le_iff₀ hw).mpr
      field_simp
      nlinarith
    constructor
    · apply Int.le_floor.mpr
      exact_mod_cast hlo
    · have hh := (Int.floor_le (a / (R / 2 ^ n))).trans hhi
      exact_mod_cast hh
  have hf : |p.1| ≤ R := (abs_le.mpr ⟨by nlinarith [sq_nonneg p.2],
    by nlinarith [sq_nonneg p.2]⟩)
  have hs : |p.2| ≤ R := (abs_le.mpr ⟨by nlinarith [sq_nonneg p.1],
    by nlinarith [sq_nonneg p.1]⟩)
  simpa only [planarDyadicCell, planarDyadicCellLabels, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc] using And.intro (hcoord p.1 hf) (hcoord p.2 hs)

/-- The dyadic cell list has a dimension-two cardinality bound. -/
theorem planarDyadicCellLabels_card (n : ℕ) :
    (planarDyadicCellLabels n).card ≤ 9 * 4 ^ n := by
  have hN : 1 ≤ (2 : ℕ) ^ n := one_le_pow₀ (by norm_num)
  have he : (((2 ^ n : ℕ) : ℤ) + 1 - (-((2 ^ n : ℕ) : ℤ))).toNat =
      2 * 2 ^ n + 1 := by omega
  have hp : (2 : ℕ) ^ n * 2 ^ n = 4 ^ n := by rw [← mul_pow]; norm_num
  simp only [planarDyadicCellLabels, Finset.product_eq_sprod, Finset.card_product, Int.card_Icc, he]
  nlinarith

/-- Points in one dyadic planar cell have the required squared-distance bound. -/
theorem planarDyadicCell_distance (R : ℝ) (hR : 0 < R) (n : ℕ) (p q : ℝ × ℝ)
    (h : planarDyadicCell R n p = planarDyadicCell R n q) :
    (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 ≤ 2 * (R / 2 ^ n) ^ 2 := by
  have hw : 0 < R / (2 : ℝ) ^ n := by positivity
  have hf := floor_cell_distance_le p.1 q.1 _ hw (congrArg Prod.fst h)
  have hs := floor_cell_distance_le p.2 q.2 _ hw (congrArg Prod.snd h)
  have hfs := (sq_le_sq₀ (abs_nonneg _) hw.le).mpr hf
  have hss := (sq_le_sq₀ (abs_nonneg _) hw.le).mpr hs
  simp only [sq_abs] at hfs hss
  linarith

end SRWTightness
