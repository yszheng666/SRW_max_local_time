import SRWTightness.LatticePairCount

namespace SRWTightness

/-- A planar lattice disk count controls every nonempty block of fixed relative diameter. -/
theorem lattice_diameter_count (hCount : LatticeDiskCountInput) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 1 ≤ r → ∀ (A : Finset Site), A.Nonempty →
      (∀ x ∈ A, ∀ y ∈ A, normSq (x - y) ≤ (c * r) ^ 2) →
      (A.card : ℝ) ≤ C * r ^ 2 := by
  classical
  obtain ⟨K, hK, hcount⟩ := hCount
  let a := max 1 c
  have ha1 : 1 ≤ a := le_max_left _ _
  have hac : c ≤ a := le_max_right _ _
  have ha0 : 0 < a := by linarith
  refine ⟨4 * K * a ^ 2, by positivity, ?_⟩
  intro r hr A hA hdiam
  obtain ⟨z, hz⟩ := hA
  have hr0 : 0 < r := by linarith
  have har : 1 ≤ 2 * a * r := by nlinarith
  have hcr : 0 < c * r := mul_pos hc hr0
  have hcmp : c * r ≤ a * r := mul_le_mul_of_nonneg_right hac hr0.le
  have hcard : A.card ≤ (diskFinset (2 * a * r)).card := by
    apply Finset.card_le_card_of_injOn (fun x : Site ↦ x - z)
    · intro x hx
      change x - z ∈ diskFinset (2 * a * r)
      rw [mem_diskFinset]
      change normSq (x - z) < (2 * a * r) ^ 2
      have hd := hdiam x hx z hz
      have hsquare := mul_self_le_mul_self hcr.le hcmp
      have hpos := sq_pos_of_pos (mul_pos ha0 hr0)
      nlinarith only [hd, hsquare, hpos]
    · intro x hx y hy hxy
      have hh := congrArg (fun w : Site ↦ w + z) hxy
      simpa using hh
  have hcast : (A.card : ℝ) ≤ ((diskFinset (2 * a * r)).card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ K * (2 * a * r) ^ 2 := hcast.trans (hcount _ har)
    _ = _ := by ring

end SRWTightness
