import SRWTightness.SourceForestApplicationGeometry

namespace SRWTightness

/-- All sufficiently separated buffers satisfy the source annular root geometry. -/
theorem source_general_annular_geometry (R m H : ℝ) (hm : 1 ≤ m)
    (hH : 0 ≤ H) (hHm : H ≤ m) (hscale : 32 * m ≤ R)
    (b : Site) (hblo : R / 4 ≤ Real.sqrt (normSq b))
    (hbhi : Real.sqrt (normSq b) ≤ R / 3) (k : ℕ) :
    sourceRecordRadius m (sourceRootDepth R m) (k + 1) - H ≤ Real.sqrt (normSq b) ∧
      Real.sqrt (normSq b) + (sourceRecordRadius m (sourceRootDepth R m) k + H) + 1 < R := by
  have hbr := (source_root_depth_bracket R m (by linarith) hscale).1
  have hchild := sourceRecordRadius_antitone m (by linarith)
    (sourceRootDepth R m) (Nat.zero_le (k + 1))
  have hroot := sourceRecordRadius_antitone m (by linarith)
    (sourceRootDepth R m) (Nat.zero_le k)
  constructor <;> linarith

end SRWTightness
