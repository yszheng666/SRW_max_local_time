import SRWTightness.SourceUpperBlockScales
import SRWTightness.SourceUpperTraversalComparison
import SRWTightness.SourceLongEscapeRadii

open Filter

namespace SRWTightness

/-- The exact distance test selecting the source root level in equation (4.19). -/
def sourceUpperRootAdmissible (t : ℝ) (b : Site) (k : ℕ) : Prop :=
  2 * sourceUpperTraversalRadius t (k + 1) + sourceUpperBuffer t ≤ Real.sqrt (normSq b)

/-- The least admissible root level, with a harmless default outside the source regime. -/
noncomputable def sourceUpperBlockRoot (t : ℝ) (b : Site) : ℕ := by
  classical
  exact if h : ∃ k, sourceUpperRootAdmissible t b k then Nat.find h else 0

/-- The annular center condition supplies an admissible level no larger than ceil(log t). -/
theorem source_upper_root_candidate (t : ℝ) (b : Site) (ht : 0 < t)
    (hR : 32 * sourceUpperRadius t ≤ Real.exp t)
    (hH : t * sourceUpperBuffer t ≤ Real.exp t / 8)
    (hb : Real.exp t / (2 * t) ≤ Real.sqrt (normSq b)) :
    sourceUpperRootAdmissible t b ⌈Real.log t⌉₊ := by
  let k := ⌈Real.log t⌉₊
  have he : t ≤ Real.exp ((k : ℝ) + 1) := by
    rw [← Real.exp_log ht]
    apply Real.exp_le_exp.mpr
    have h := Nat.le_ceil (Real.log t)
    dsimp [k]
    linarith
  have hid : Real.exp ((k : ℝ) + 1) * sourceUpperTraversalRadius t (k + 1) =
      sourceUpperTraversalRadius t 0 := by
    simpa only [Nat.sub_self, sourceUpperTraversalRadius] using
      sourceRecordRadius_long (sourceUpperRadius t)
        (sourceRootDepth (Real.exp t) (sourceUpperRadius t)) k k le_rfl
  have hr : 0 ≤ sourceUpperTraversalRadius t (k + 1) := by
    unfold sourceUpperTraversalRadius sourceRecordRadius sourceUpperRadius
    positivity
  have hm := mul_le_mul_of_nonneg_right he hr
  rw [hid] at hm
  have hroot := source_upper_traversal_radius_bound t hR 0
  have hb' := (div_le_iff₀ (by positivity : 0 < 2 * t)).mp hb
  change 2 * sourceUpperTraversalRadius t (k + 1) + sourceUpperBuffer t ≤ _
  apply (mul_le_mul_iff_right₀ ht).mp
  nlinarith [Real.exp_pos t]

/-- Admissibility and minimality are properties of the actual selected root, not premises. -/
theorem source_upper_block_root_spec (t : ℝ) (b : Site)
    (h : ∃ k, sourceUpperRootAdmissible t b k) :
    sourceUpperRootAdmissible t b (sourceUpperBlockRoot t b) ∧
      ∀ j < sourceUpperBlockRoot t b, ¬ sourceUpperRootAdmissible t b j := by
  classical
  rw [sourceUpperBlockRoot, dif_pos h]
  exact ⟨Nat.find_spec h, fun j hj ↦ Nat.find_min h hj⟩

/-- Every center beyond R/(2t) has a least source root with logarithmic depth. -/
theorem source_upper_block_root_bound :
    ∀ᶠ t : ℝ in atTop, ∀ b : Site,
      Real.exp t / (2 * t) ≤ Real.sqrt (normSq b) →
        sourceUpperRootAdmissible t b (sourceUpperBlockRoot t b) ∧
        sourceUpperBlockRoot t b ≤ ⌈Real.log t⌉₊ ∧
        (sourceUpperBlockRoot t b : ℝ) ≤ Real.log t + 1 := by
  classical
  filter_upwards [source_upper_block_scale_conditions] with t ht
  intro b hb
  have ht0 : 0 < t := by linarith [ht.1]
  have hc := source_upper_root_candidate t b ht0 ht.2.1 ht.2.2.1 hb
  have hex : ∃ k, sourceUpperRootAdmissible t b k := ⟨_, hc⟩
  have hle : sourceUpperBlockRoot t b ≤ ⌈Real.log t⌉₊ := by
    rw [sourceUpperBlockRoot, dif_pos hex]
    exact Nat.find_min' hex hc
  refine ⟨(source_upper_block_root_spec t b hex).1, hle, ?_⟩
  have hc' : (⌈Real.log t⌉₊ : ℝ) < Real.log t + 1 :=
    Nat.ceil_lt_add_one (Real.log_nonneg ht.1)
  have hle' : (sourceUpperBlockRoot t b : ℝ) ≤ (⌈Real.log t⌉₊ : ℝ) := by exact_mod_cast hle
  linarith

end SRWTightness
