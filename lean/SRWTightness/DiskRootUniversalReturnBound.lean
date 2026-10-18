import SRWTightness.AnnulusUniversalReturnBound
import SRWTightness.HitDomainMonotonicity
import SRWTightness.SourceBufferedHalf
import SRWTightness.TranslatedDiskGeometry

namespace SRWTightness

/-- A containing translated disk turns the annulus gap into an actual outer-disk return bound. -/
theorem disk_root_universal_return_bound (hinput : PotentialKernelAsymptoticInput) :
    ∃ a₀ : ℝ, 2 ≤ a₀ ∧ ∀ a R c : ℝ, a₀ ≤ a → a < 2 * R → a ≤ c →
      ∀ b x : Site, normSq b ≤ R ^ 2 → x ∈ diskFinset R →
      c ≤ Real.sqrt (normSq (x - b)) →
      setHitProbability (diskFinset R) (translateFinset b (diskFinset a)) x ≤
        1 - (Real.log (c / a) - 4 / a) / Real.log (2 * R / a) := by
  obtain ⟨a₀, ha₀, hh⟩ := annulus_universal_return_bound hinput
  refine ⟨a₀, ha₀, ?_⟩
  intro a R c ha hRa hac b x hb hx hxa
  have hR : 0 ≤ R := by linarith
  have hDE := disk_subset_translated_outer R hR b hb
  have hxE := hDE hx
  have hxu : normSq (x - b) ≤ (2 * R) ^ 2 := by
    have ht : normSq (x - b) < (2 * R) ^ 2 := by
      simpa only [mem_translateFinset_iff, mem_diskFinset, disk, Set.mem_setOf_eq] using hxE
    exact ht.le
  have hgap := hh a (2 * R) c ha hRa hac (x - b) hxa hxu
  have hm := setHitProbability_mono_domain (diskFinset R)
    (translateFinset b (diskFinset (2 * R))) (translateFinset b (diskFinset a)) hDE x
  have ht : setHitProbability (translateFinset b (diskFinset (2 * R)))
      (translateFinset b (diskFinset a)) x =
      setHitProbability (diskFinset (2 * R)) (diskFinset a) (x - b) := by
    have he : x = b + (x - b) := by abel
    conv_lhs => rw [he]
    exact setHitProbability_translate b _ _ (x - b)
  rw [ht] at hm
  linarith

end SRWTightness
