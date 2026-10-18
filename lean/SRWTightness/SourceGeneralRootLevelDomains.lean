import SRWTightness.SourceSingleRootGeometry

namespace SRWTightness

/-- Every source root level has the same entrance domain under remaining-depth indexing. -/
theorem source_general_level_entrance (m H : ℝ) (ℓ k : ℕ) (hk : k < ℓ) (b : Site) :
    growingRecordEntrance b m H (ℓ - (k + 1)) =
      translateFinset b (diskFinset (sourceRecordRadius m ℓ (k + 1) - H)) := by
  rw [growingRecordEntrance, ← source_single_root_radius m ℓ k hk]

/-- Every source root level has the same outer domain under remaining-depth indexing. -/
theorem source_general_level_exit (m H : ℝ) (ℓ k : ℕ) (hk : k < ℓ) (b : Site) :
    growingRecordExit b m H (ℓ - (k + 1)) =
      translateFinset b (diskFinset (sourceRecordRadius m ℓ k + H)) := by
  rw [growingRecordExit, ← source_single_root_radius m ℓ k hk,
    ← sourceRecordRadius_successor m ℓ k]

end SRWTightness
