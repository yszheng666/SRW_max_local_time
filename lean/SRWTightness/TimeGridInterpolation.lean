import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- A continuous ramp, equal to zero before the left endpoint and one after the right. -/
noncomputable def timeGridRamp (a b v : ℝ) : ℝ := max 0 (min 1 ((v - a) / (b - a)))

theorem timeGridRamp_continuous (a b : ℝ) : Continuous (timeGridRamp a b) := by
  unfold timeGridRamp
  fun_prop

theorem timeGridRamp_left (a b v : ℝ) (hab : a < b) (hv : v ≤ a) :
    timeGridRamp a b v = 0 := by
  have hh : (v - a) / (b - a) ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hv) (by linarith)
  unfold timeGridRamp
  rw [min_eq_right (by linarith), max_eq_left hh]

theorem timeGridRamp_right (a b v : ℝ) (hab : a < b) (hv : b ≤ v) :
    timeGridRamp a b v = 1 := by
  have hh : 1 ≤ (v - a) / (b - a) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  simp only [timeGridRamp, min_eq_left hh, max_eq_right zero_le_one]

theorem timeGridRamp_interval (a b v : ℝ) (hab : a < b) (ha : a ≤ v) (hb : v ≤ b) :
    timeGridRamp a b v = (v - a) / (b - a) := by
  have hl : 0 ≤ (v - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hu : (v - a) / (b - a) ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  simp only [timeGridRamp, min_eq_right hu, max_eq_right hl]

/-- Continuous interpolation on a finite time mesh, with constant extension at both ends. -/
noncomputable def timeGridInterpolation (T x : ℕ → ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  x 0 + ∑ j ∈ Finset.range n, timeGridRamp (T j) (T (j + 1)) v * (x (j + 1) - x j)

theorem timeGridInterpolation_continuous (T x : ℕ → ℝ) (n : ℕ) :
    Continuous (timeGridInterpolation T x n) := by
  unfold timeGridInterpolation
  exact continuous_const.add (continuous_finsetSum _ fun j _ ↦
    (timeGridRamp_continuous _ _).mul continuous_const)

theorem timeGridTime_mono (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    T i ≤ T j := by
  have hm : Monotone (fun k : Fin (n + 1) ↦ T k.val) :=
    Fin.monotone_iff_le_succ.mpr (fun k ↦ (hgap k.val k.isLt).le)
  exact hm (show (⟨i, by omega⟩ : Fin (n + 1)) ≤ ⟨j, by omega⟩ from hij)

/-- On each mesh interval the continuous construction is the exact affine interpolation. -/
theorem timeGridInterpolation_interval (T x : ℕ → ℝ) (n k : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (hk : k < n) (v : ℝ)
    (hl : T k ≤ v) (hu : v ≤ T (k + 1)) :
    timeGridInterpolation T x n v =
      (1 - (v - T k) / (T (k + 1) - T k)) * x k +
        ((v - T k) / (T (k + 1) - T k)) * x (k + 1) := by
  let f := fun j ↦ timeGridRamp (T j) (T (j + 1)) v * (x (j + 1) - x j)
  have htail : (∑ j ∈ Finset.range n, f j) = ∑ j ∈ Finset.range (k + 1), f j := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hj hjk
    have hjn := Finset.mem_range.mp hj
    have hkj : k + 1 ≤ j := by simpa only [Finset.mem_range, not_lt] using hjk
    have hvj : v ≤ T j := hu.trans (timeGridTime_mono T n hgap hkj (by omega))
    dsimp [f]
    rw [timeGridRamp_left _ _ _ (hgap j hjn) hvj, zero_mul]
  have hhead : (∑ j ∈ Finset.range k, f j) = x k - x 0 := by
    calc
      _ = ∑ j ∈ Finset.range k, (x (j + 1) - x j) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk := Finset.mem_range.mp hj
        have hvj : T (j + 1) ≤ v :=
          (timeGridTime_mono T n hgap (by omega) (by omega)).trans hl
        dsimp [f]
        rw [timeGridRamp_right _ _ _ (hgap j (by omega)) hvj, one_mul]
      _ = _ := Finset.sum_range_sub x k
  change x 0 + (∑ j ∈ Finset.range n, f j) = _
  rw [htail, Finset.sum_range_succ, hhead]
  dsimp [f]
  rw [timeGridRamp_interval _ _ _ (hgap k hk) hl hu]
  ring

end SRWTightness
