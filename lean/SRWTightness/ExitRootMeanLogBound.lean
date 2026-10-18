import SRWTightness.KilledWordPairMean
import SRWTightness.SeparatedDiskGreenUpper
import SRWTightness.ShortRootExitSeparation
import SRWTightness.DiskCapacityLogBound

open MeasureTheory
namespace SRWTightness

/-- At an actual short exit, both future-root means have explicit logarithmic bounds. -/
theorem exit_root_pair_mean_log_bound (hLast : FiniteLastVisitCountInput)
    (c b w x : Site) (R r a : ℝ) (hR : 1 ≤ R) (ha : 0 ≤ a) (har : a < r)
    (hsep : 0 < Real.sqrt (normSq (w - b)) - (r + 1) - a)
    (hx : x ∈ domainExitBoundary (translateFinset b (diskFinset r)))
    (hxD : x ∈ translateFinset c (diskFinset R))
    (hC₁D : translateFinset b (diskFinset r) ⊆ translateFinset c (diskFinset R))
    (hC₂D : translateFinset w (diskFinset r) ⊆ translateFinset c (diskFinset R)) :
    (∫ Y, ((wordMarkRootCount (translateFinset b (diskFinset a))
      (translateFinset b (diskFinset r)) Y +
      wordMarkRootCount (translateFinset w (diskFinset a))
      (translateFinset w (diskFinset r)) Y : ℕ) : ℝ)
      ∂killedWordMarkLaw (translateFinset c (diskFinset R)) x) ≤
      ((2 / Real.pi) * Real.log (2 * R / (r - a)) + diskGreenAdditiveConstant) *
        capacity (diskFinset r) (diskFinset a) +
      ((2 / Real.pi) * Real.log
        (2 * R / (Real.sqrt (normSq (w - b)) - (r + 1) - a)) +
        diskGreenAdditiveConstant) * capacity (diskFinset r) (diskFinset a) := by
  have hr : 0 ≤ r := ha.trans har.le
  have hLC (z : Site) : translateFinset z (diskFinset a) ⊆
      translateFinset z (diskFinset r) := by
    intro y hy
    rw [mem_translateFinset_iff] at hy ⊢
    exact diskFinset_mono a r ha har.le hy
  have h₁ (y : Site) (hy : y ∈ translateFinset b (diskFinset a)) :
      killedGreen (translateFinset c (diskFinset R)) x y ≤
        (2 / Real.pi) * Real.log (2 * R / (r - a)) + diskGreenAdditiveConstant :=
    translated_disk_green_separated_upper c x y R (r - a) hR (sub_pos.mpr har)
      hxD (hC₁D (hLC b hy)) (disk_exit_inner_separation b x y r a hr ha hx hy)
  have h₂ (y : Site) (hy : y ∈ translateFinset w (diskFinset a)) :
      killedGreen (translateFinset c (diskFinset R)) x y ≤
        (2 / Real.pi) * Real.log
          (2 * R / (Real.sqrt (normSq (w - b)) - (r + 1) - a)) +
          diskGreenAdditiveConstant :=
    translated_disk_green_separated_upper c x y R _ hR hsep hxD (hC₂D (hLC w hy))
      (disk_exit_other_inner_separation b w x y r a hr ha hx hy)
  have hh := killedWordMark_pair_mean_le hLast _ _ _ _ _ (hLC b) (hLC w)
    hC₁D hC₂D x _ _ (fun y hy _ ↦ h₁ y hy) (fun y hy _ ↦ h₂ y hy)
  simpa only [capacity_translate] using hh

end SRWTightness
