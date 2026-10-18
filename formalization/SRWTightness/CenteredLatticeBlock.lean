import SRWTightness.LatticeSquare
import SRWTightness.LatticeNorm

namespace SRWTightness

/-- The half-open integer block of side a centered at its distinguished lattice site. -/
def centeredLatticeBlock (a : ℕ) (b : Site) : Finset Site :=
  latticeSquare (b - (((a / 2 : ℕ) : ℤ), ((a / 2 : ℕ) : ℤ))) a

/-- The unique grid center selected by integer division with the half-block offset. -/
def latticeBlockCenter (a : ℕ) (x : Site) : Site :=
  ((a : ℤ) * ((x.1 + (a / 2 : ℕ)) / (a : ℤ)),
    (a : ℤ) * ((x.2 + (a / 2 : ℕ)) / (a : ℤ)))

theorem latticeBlockCenter_divisible (a : ℕ) (x : Site) :
    (a : ℤ) ∣ (latticeBlockCenter a x).1 ∧ (a : ℤ) ∣ (latticeBlockCenter a x).2 :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- Every lattice site belongs to the half-open block at its selected grid center. -/
theorem mem_centeredLatticeBlock_center (a : ℕ) (ha : 0 < a) (x : Site) :
    x ∈ centeredLatticeBlock a (latticeBlockCenter a x) := by
  have ha' : 0 < (a : ℤ) := by exact_mod_cast ha
  have coord (u : ℤ) :
      (a : ℤ) * ((u + (a / 2 : ℕ)) / (a : ℤ)) - (a / 2 : ℕ) ≤ u ∧
      u ≤ (a : ℤ) * ((u + (a / 2 : ℕ)) / (a : ℤ)) - (a / 2 : ℕ) + a - 1 := by
    have he := Int.emod_add_mul_ediv (u + (a / 2 : ℕ)) (a : ℤ)
    have hlo := Int.emod_nonneg (u + (a / 2 : ℕ)) ha'.ne'
    have hhi := Int.emod_lt_of_pos (u + (a / 2 : ℕ)) ha'
    omega
  simpa only [centeredLatticeBlock, latticeSquare, latticeBlockCenter,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub] using
      And.intro (coord x.1) (coord x.2)

/-- Every site of a centered block is within one side length of its center. -/
theorem centeredLatticeBlock_near (a : ℕ) (b x : Site)
    (hx : x ∈ centeredLatticeBlock a b) : normSq (x - b) ≤ (a : ℝ) ^ 2 := by
  have hh := hx
  simp only [centeredLatticeBlock, latticeSquare, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc,
    Prod.fst_sub, Prod.snd_sub] at hh
  have coord (u v : ℤ) (h : v - (a / 2 : ℕ) ≤ u ∧
      u ≤ v - (a / 2 : ℕ) + a - 1) : ((u : ℝ) - v) ^ 2 ≤ ((a : ℝ) / 2) ^ 2 := by
    have hi : -(a : ℤ) ≤ 2 * (u - v) ∧ 2 * (u - v) ≤ (a : ℤ) := by omega
    have hlo : -(a : ℝ) ≤ 2 * ((u : ℝ) - v) := by exact_mod_cast hi.1
    have hhi : 2 * ((u : ℝ) - v) ≤ (a : ℝ) := by exact_mod_cast hi.2
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (sub_nonneg.mpr hlo)]
  have h₁ := coord x.1 b.1 hh.1
  have h₂ := coord x.2 b.2 hh.2
  simp only [normSq, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  nlinarith [sq_nonneg (a : ℝ)]

end SRWTightness
