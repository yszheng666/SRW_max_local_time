import SRWTightness.CenteredLatticeBlock
import Mathlib.Tactic.FinCases

namespace SRWTightness

/-- Every nonzero lattice point has a nearest neighbor strictly closer to the origin. -/
theorem exists_step_normSq_lt (x : Site) (hx : x ≠ 0) :
    ∃ d : Direction, normSq (x + step d) < normSq x := by
  by_cases h₁ : x.1 = 0
  · have h₂ : x.2 ≠ 0 := fun h ↦ hx (Prod.ext h₁ h)
    rcases lt_or_gt_of_ne h₂ with hn | hp
    · refine ⟨2, ?_⟩
      have hh : (x.2 : ℝ) ≤ -1 := by exact_mod_cast (show x.2 ≤ -1 by omega)
      norm_num [step, normSq]
      push_cast
      nlinarith
    · refine ⟨3, ?_⟩
      have hh : (1 : ℝ) ≤ x.2 := by exact_mod_cast (show 1 ≤ x.2 by omega)
      norm_num [step, normSq]
      push_cast
      nlinarith
  · rcases lt_or_gt_of_ne h₁ with hn | hp
    · refine ⟨0, ?_⟩
      have hh : (x.1 : ℝ) ≤ -1 := by exact_mod_cast (show x.1 ≤ -1 by omega)
      norm_num [step, normSq]
      push_cast
      nlinarith
    · refine ⟨1, ?_⟩
      have hh : (1 : ℝ) ≤ x.1 := by exact_mod_cast (show 1 ≤ x.1 by omega)
      norm_num [step, normSq]
      push_cast
      nlinarith

/-- A neighbor of any site of a block of side at least four is within one side of its center. -/
theorem centeredLatticeBlock_neighbor_near (a : ℕ) (ha : 4 ≤ a) (b x : Site)
    (hx : x ∈ centeredLatticeBlock a b) (d : Direction) :
    normSq (x + step d - b) ≤ (a : ℝ) ^ 2 := by
  have hh := hx
  simp only [centeredLatticeBlock, latticeSquare, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub] at hh
  have coord (u v : ℤ)
      (h : v - (a / 2 : ℕ) ≤ u ∧ u ≤ v - (a / 2 : ℕ) + a - 1) :
      -(a : ℝ) ≤ 2 * ((u : ℝ) - v) ∧ 2 * ((u : ℝ) - v) ≤ a := by
    have hi : -(a : ℤ) ≤ 2 * (u - v) ∧ 2 * (u - v) ≤ a := by omega
    constructor
    · exact_mod_cast hi.1
    · exact_mod_cast hi.2
  have h₁ := coord x.1 b.1 hh.1
  have h₂ := coord x.2 b.2 hh.2
  have hs₁ : ((x.1 : ℝ) - b.1) ^ 2 ≤ ((a : ℝ) / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁.2) (sub_nonneg.mpr h₁.1)]
  have hs₂ : ((x.2 : ℝ) - b.2) ^ 2 ≤ ((a : ℝ) / 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h₂.2) (sub_nonneg.mpr h₂.1)]
  have ha' : (4 : ℝ) ≤ a := by exact_mod_cast ha
  fin_cases d <;> norm_num [step, normSq] <;> push_cast <;>
    nlinarith [sq_nonneg ((a : ℝ) - 2)]

end SRWTightness
