import SRWTightness.SourceCommonPairRebase
import SRWTightness.SourceGrowingRecordIdentity
import SRWTightness.SourceForestApplicationGeometry

open Filter
namespace SRWTightness

/-- The common-prefix root entrance radius is the original first source radius. -/
theorem source_common_root_radius (m : ℝ) (ℓ j : ℕ) :
    growingRecordRadius (sourceRecordRadius m ℓ (j + 1)) j = sourceRecordRadius m ℓ 1 := by
  rw [← sourceRecordRadius_reverse _ (j + 1) j (by omega)]
  have h : j + 1 - j = 1 := by omega
  rw [h, sourceRecordRadius_rebase]

/-- The original source annulus discharges both root-entrance and disk-fit conditions. -/
theorem source_common_root_annular_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ (b : Site) (j : ℕ),
      Real.exp t / 4 ≤ Real.sqrt (normSq b) →
      Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      growingRecordRadius (sourceCommonPairInnerRadius t j) j - 14 ≤ Real.sqrt (normSq b) ∧
      Real.sqrt (normSq b) +
        (Real.exp 1 * growingRecordRadius (sourceCommonPairInnerRadius t j) j + 14) + 1 <
          Real.exp t := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T] with t ht
  intro b j hlo hhi
  have hs := hT t ht
  have hm := (sourceScaleThreshold_conditions t 4 (by norm_num) hs.1).2.2.1
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    nlinarith [hs.2, sourceLowerRadius_pos t, Real.exp_one_gt_two]
  have hh := source_annular_center_geometry (Real.exp t) (sourceLowerRadius t) hm hscale
    b hlo hhi 0
  dsimp only [sourceCommonPairInnerRadius]
  rw [source_common_root_radius, sourceRecordRadius_successor _ _ 0]
  exact hh

end SRWTightness
