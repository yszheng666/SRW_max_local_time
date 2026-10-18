import SRWTightness.EquilibriumSupportSeparation
import SRWTightness.DiskCapacityLogBound

namespace SRWTightness

noncomputable def geometricDiskFamily (b : Site) (A q : ℝ) (n : ℕ) : Fin n → Finset Site :=
  fun i ↦ translateFinset b (diskFinset (A * q ^ i.val))

theorem geometric_radius_ge (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q) (i : ℕ) :
    A ≤ A * q ^ i := by
  have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hq : 1 ≤ q ^ i) hA
  simpa using hh

theorem geometric_radius_mono (A q : ℝ) (hA : 0 ≤ A) (hq : 1 ≤ q) :
    Monotone (fun i : ℕ ↦ A * q ^ i) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hij) hA

theorem geometric_radius_shell_gap (A q : ℝ) (hA : 1 ≤ A) (hq : 2 ≤ q)
    (i j : ℕ) (hij : i < j) : A * q ^ i ≤ A * q ^ j - 1 := by
  have ha0 : 0 ≤ A := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hi := geometric_radius_ge A q ha0 hq1 i
  have hh := geometric_radius_mono A q ha0 hq1 (Nat.succ_le_of_lt hij)
  change A * q ^ (i + 1) ≤ A * q ^ j at hh
  rw [pow_succ] at hh
  nlinarith

theorem geometricDiskFamily_mono (b : Site) (A q : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hq : 1 ≤ q) : Monotone (geometricDiskFamily b A q n) := by
  intro i j hij
  apply Finset.image_subset_image
  exact diskFinset_mono _ _ (by positivity)
    (geometric_radius_mono A q hA hq (Fin.le_def.mp hij))

theorem geometricDiskFamily_subset (b : Site) (A R q : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hq : 0 ≤ q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R) (i : Fin n) :
    geometricDiskFamily b A q n i ⊆ translateFinset b (diskFinset R) := by
  apply Finset.image_subset_image
  have ha : 0 ≤ A * q ^ i.val := by positivity
  exact diskFinset_mono _ _ ha (by linarith [hsep i])

theorem geometricDiskFamily_center_mem (b : Site) (A q : ℝ) (n : ℕ)
    (hA : 0 < A) (hq : 0 < q) (i : Fin n) : b ∈ geometricDiskFamily b A q n i := by
  have hh := mem_translateFinset_add b (diskFinset (A * q ^ i.val)) 0
  simp only [add_zero] at hh
  exact hh.mpr (zero_mem_diskFinset _ (by positivity))

theorem geometricDiskFamily_center_weight_zero (b : Site) (A R q : ℝ) (n : ℕ)
    (hA : 4 ≤ A) (hq : 2 ≤ q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R) (i : Fin n) :
    equilibriumWeight (translateFinset b (diskFinset R)) (geometricDiskFamily b A q n i) b = 0 := by
  have hi := geometric_radius_ge A q (by linarith) (by linarith) i.val
  exact translated_disk_equilibriumWeight_center_zero _ b _ (by linarith)
    (geometricDiskFamily_subset b A R q n (by linarith) (by linarith) hsep i)

theorem geometricDiskFamily_weights_disjoint (b : Site) (A R q : ℝ) (n : ℕ)
    (hA : 4 ≤ A) (hq : 2 ≤ q)
    (hsep : ∀ i : Fin n, 2 * (A * q ^ i.val) ≤ R) (i j : Fin n) (hij : i ≠ j) (x : Site) :
    equilibriumWeight (translateFinset b (diskFinset R)) (geometricDiskFamily b A q n i) x *
      equilibriumWeight (translateFinset b (diskFinset R)) (geometricDiskFamily b A q n j) x = 0 := by
  have hdir (i j : Fin n) (hij : i < j) :
      equilibriumWeight (translateFinset b (diskFinset R)) (geometricDiskFamily b A q n i) x *
        equilibriumWeight (translateFinset b (diskFinset R)) (geometricDiskFamily b A q n j) x = 0 := by
    have hi := geometric_radius_ge A q (by linarith) (by linarith) i.val
    have hj := geometric_radius_ge A q (by linarith) (by linarith) j.val
    exact translated_disk_equilibriumWeight_disjoint _ b _ _ (by linarith) (by linarith)
      (geometric_radius_shell_gap A q (by linarith) hq i.val j.val (Fin.lt_def.mp hij))
      (geometricDiskFamily_subset b A R q n (by linarith) (by linarith) hsep j) x
  rcases lt_or_gt_of_ne hij with h | h
  · exact hdir i j h
  · rw [mul_comm]
    exact hdir j i h

end SRWTightness
