import SRWTightness.KilledPathWord
import SRWTightness.Filtration

open MeasureTheory

namespace SRWTightness

/-- The fixed finite direction prefix, including its length and every recorded increment. -/
def pathPrefixWord (n : ℕ) (ω : Sample) : PathWord := ⟨n, fun k ↦ ω k⟩

/-- A fixed word prefix depends only on the natural history at its endpoint. -/
theorem history_measurable_path_prefix_word (n : ℕ) :
    Measurable[history n] (pathPrefixWord n) :=
  (measurable_of_countable (fun v : Fin n → Direction ↦ (⟨n, v⟩ : PathWord))).comp
    (history_measurable_prefix n)

/-- The recorded finite prefix is globally measurable as well. -/
theorem measurable_path_prefix_word (n : ℕ) : Measurable (pathPrefixWord n) :=
  (history_measurable_path_prefix_word n).mono (history.le n) le_rfl

/-- Every position through the prefix endpoint is the original walk's actual position. -/
theorem path_prefix_word_position (n : ℕ) (ω : Sample) (i : ℕ) (hi : i ≤ n) :
    position (wordPath (pathPrefixWord n ω)) i = position ω i := by
  apply position_congr
  intro k hk
  simp [wordPath, pathPrefixWord, extendWord, hk.trans_le hi]

end SRWTightness
