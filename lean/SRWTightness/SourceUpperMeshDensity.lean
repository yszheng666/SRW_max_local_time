import SRWTightness.SourceUpperMeshScale
import SRWTightness.SourceLongEscapeRadii

open Filter

namespace SRWTightness

theorem source_upper_mesh_spacing_le_fine (t : ℝ) (j : ℕ) :
    (sourceUpperMeshSpacing t j : ℝ) ≤ sourceUpperTraversalRadius t (j + 1) := by
  have hr : 0 < sourceUpperTraversalRadius t (j + 1) := by
    unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  have hd : 0 < 1000 * ((j : ℝ) + 1) := by positivity
  have hf : (sourceUpperMeshSpacing t j : ℝ) ≤
      sourceUpperTraversalRadius t (j + 1) / (1000 * ((j : ℝ) + 1)) :=
    Nat.floor_le (div_nonneg hr.le hd.le)
  have hh := (le_div_iff₀ hd).mp hf
  have ha : 0 ≤ (sourceUpperMeshSpacing t j : ℝ) := Nat.cast_nonneg _
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg ha hj]

/-- Exact source spacing gives the quadratic-density scale without a logarithmic loss. -/
theorem source_upper_mesh_density :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ j : ℕ, j ≤ sourceUpperCoarseDepth t →
      Real.exp t / (sourceUpperMeshSpacing t j : ℝ) ≤
        D * ((j : ℝ) + 1) * Real.exp (j : ℝ) := by
  refine ⟨64000 * Real.exp 2, by positivity, ?_⟩
  filter_upwards [source_upper_mesh_scale_conditions] with t ht
  intro j hj
  let a := sourceUpperMeshSpacing t j
  let r := sourceUpperTraversalRadius t (j + 1)
  have ha : 0 < a := (ht.2 j hj).2.1
  have ha' : 0 < (a : ℝ) := by exact_mod_cast ha
  have ha1 : 1 ≤ (a : ℝ) := by exact_mod_cast ha
  have hd : 0 < 1000 * ((j : ℝ) + 1) := by positivity
  have hf : r / (1000 * ((j : ℝ) + 1)) < (a : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hr : r ≤ 2000 * (a : ℝ) * ((j : ℝ) + 1) := by
    have hh := (div_le_iff₀ hd).mp (show r / (1000 * ((j : ℝ) + 1)) ≤ 2 * a by linarith)
    nlinarith
  have hroot := (source_root_depth_bracket (Real.exp t) (sourceUpperRadius t)
    (Real.exp_pos _) ht.1).2.le
  have hid : Real.exp ((j : ℝ) + 1) * r = sourceUpperTraversalRadius t 0 := by
    simpa only [Nat.sub_self, r, sourceUpperTraversalRadius] using
      sourceRecordRadius_long (sourceUpperRadius t)
        (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) j j le_rfl
  change Real.exp t ≤ 32 * Real.exp 1 * sourceUpperTraversalRadius t 0 at hroot
  rw [← hid] at hroot
  apply (div_le_iff₀ ha').mpr
  calc
    _ ≤ (32 * Real.exp 1 * Real.exp ((j : ℝ) + 1)) * r := by nlinarith [hroot]
    _ ≤ (32 * Real.exp 1 * Real.exp ((j : ℝ) + 1)) *
        (2000 * (a : ℝ) * ((j : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by
      have he : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      rw [Real.exp_add, he]
      ring

end SRWTightness
