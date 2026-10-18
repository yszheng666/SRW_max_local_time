import SRWTightness.SourceSingleRootGeometry

namespace SRWTightness

/-- At the actual root depth, a general buffer gives the source entrance shell. -/
theorem source_general_root_entrance (m H : ℝ) (ℓ : ℕ) (hℓ : 0 < ℓ) (b : Site) :
    growingRecordEntrance b m H (ℓ - 1) =
      translateFinset b (diskFinset (sourceRecordRadius m ℓ 1 - H)) := by
  rw [growingRecordEntrance, ← source_single_root_radius m ℓ 0 hℓ]

/-- The outer root shell agrees under source and remaining-depth indexing for every buffer. -/
theorem source_general_root_exit (m H : ℝ) (ℓ : ℕ) (hℓ : 0 < ℓ) (b : Site) :
    growingRecordExit b m H (ℓ - 1) =
      translateFinset b (diskFinset (sourceRecordRadius m ℓ 0 + H)) := by
  rw [growingRecordExit, ← source_single_root_radius m ℓ 0 hℓ,
    ← sourceRecordRadius_successor m ℓ 0]

end SRWTightness
