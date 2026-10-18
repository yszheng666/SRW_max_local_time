import SRWTightness.TranslatedDiskGeometry
import Mathlib.Algebra.Order.Round

namespace SRWTightness

/-- Coordinatewise rounding gives a lattice-mesh point within one mesh spacing. -/
theorem lattice_mesh_near (a : ℕ) (ha : 0 < a) (x : Site) :
    ∃ z : Site, (a : ℤ) ∣ z.1 ∧ (a : ℤ) ∣ z.2 ∧ normSq (x - z) ≤ (a : ℝ) ^ 2 := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  let z : Site := ((a : ℤ) * round ((x.1 : ℝ) / a),
    (a : ℤ) * round ((x.2 : ℝ) / a))
  refine ⟨z, ⟨_, rfl⟩, ⟨_, rfl⟩, ?_⟩
  have hcoord (b : ℤ) : |(b : ℝ) - a * (round ((b : ℝ) / a) : ℝ)| ≤ a / 2 := by
    calc
      _ = |(a : ℝ) * ((b : ℝ) / a - (round ((b : ℝ) / a) : ℝ))| := by
        rw [mul_sub, mul_div_cancel₀ _ ha'.ne']
      _ = (a : ℝ) * |(b : ℝ) / a - (round ((b : ℝ) / a) : ℝ)| := by
        rw [abs_mul, abs_of_pos ha']
      _ ≤ (a : ℝ) * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sub_round ((b : ℝ) / a)) ha'.le
      _ = _ := by ring
  have h₁ := abs_le.mp (hcoord x.1)
  have h₂ := abs_le.mp (hcoord x.2)
  have hs₁ : ((x.1 : ℝ) - a * (round ((x.1 : ℝ) / a) : ℝ)) ^ 2 ≤ (a / 2 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁.2) (sub_nonneg.mpr h₁.1)]
  have hs₂ : ((x.2 : ℝ) - a * (round ((x.2 : ℝ) / a) : ℝ)) ^ 2 ≤ (a / 2 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr h₂.2) (sub_nonneg.mpr h₂.1)]
  dsimp [normSq, z]
  push_cast
  nlinarith [sq_nonneg (a : ℝ)]

/-- A point in the half-radius disk has a nearby mesh point in the three-quarter disk. -/
theorem lattice_mesh_near_in_disk (R : ℝ) (hR : 0 < R) (a : ℕ) (ha : 0 < a)
    (haR : (a : ℝ) ≤ R / 4) (x : Site) (hx : x ∈ diskFinset (R / 2)) :
    ∃ z ∈ diskFinset (3 * R / 4), (a : ℤ) ∣ z.1 ∧ (a : ℤ) ∣ z.2 ∧
      normSq (x - z) ≤ (a : ℝ) ^ 2 := by
  obtain ⟨z, hz₁, hz₂, hnear⟩ := lattice_mesh_near a ha x
  refine ⟨z, ?_, hz₁, hz₂, hnear⟩
  have hsym : normSq (z - x) ≤ (R / 4) ^ 2 := by
    rw [show z - x = -(x - z) by abel, normSq_neg]
    exact hnear.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) a])
  have hh := normSq_add_lt_of_le_of_lt (z - x) x (by positivity : 0 ≤ R / 4)
    (by positivity : 0 ≤ R / 2) hsym ((mem_diskFinset _ _).mp hx)
  rw [sub_add_cancel, show R / 4 + R / 2 = 3 * R / 4 by ring] at hh
  exact (mem_diskFinset _ _).mpr hh

end SRWTightness
