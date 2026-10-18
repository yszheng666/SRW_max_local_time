import SRWTightness.WordOccupationMark
import SRWTightness.ChildIntervalExtraction

open MeasureTheory
namespace SRWTightness

/-- An empty mark or a killed path retaining its entrance and every ordered increment. -/
abbrev WordMark := Option (Site × PathWord)

instance wordMark_measurableSpace : MeasurableSpace WordMark := ⊤
instance wordMark_measurableSingletonClass : MeasurableSingletonClass WordMark :=
  ⟨fun _ ↦ trivial⟩

/-- The full killed word started at a specified site, including its entrance. -/
noncomputable def killedWordMark (D : Finset Site) (x : Site) (ω : Sample) : WordMark :=
  some (x, killedPathWord D x ω)

theorem measurable_killedWordMark (D : Finset Site) (x : Site) :
    Measurable (killedWordMark D x) :=
  (measurable_of_countable (fun w : PathWord ↦ (some (x, w) : WordMark))).comp
    (measurable_killedPathWord D x)

noncomputable def killedWordMarkLaw (D : Finset Site) (x : Site) : Measure WordMark :=
  pathLaw.map (killedWordMark D x)

instance killedWordMarkLaw_probability (D : Finset Site) (x : Site) :
    IsProbabilityMeasure (killedWordMarkLaw D x) :=
  Measure.isProbabilityMeasure_map (measurable_killedWordMark D x).aemeasurable

/-- Occupation is a projection of the ordered mark; it is not used to reconstruct crossings. -/
noncomputable def wordMarkOccupation (K : Finset Site) : WordMark → Mark K
  | none => 0
  | some (x, w) => wordOccupationMark K x w

/-- Ordered complete inner-entrance/outer-exit intervals retained by the mark. -/
def wordMarkRootCount (K C : Finset Site) : WordMark → ℕ
  | none => 0
  | some (x, w) => (wordChildIntervals K C x w).length

/-- The occupation projection agrees exactly with the earlier killed occupation mark. -/
theorem wordMarkOccupation_killed (D K : Finset Site) (x : Site) (ω : Sample) :
    wordMarkOccupation K (killedWordMark D x ω) = killedMark D K x ω :=
  wordOccupationMark_killedPathWord D K x ω

end SRWTightness
