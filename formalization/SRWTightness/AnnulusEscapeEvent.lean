import SRWTightness.AnnulusEscapeIdentity
import SRWTightness.LatticeTranslation

open MeasureTheory

namespace SRWTightness

/-- Strict escape is the complementary hitting event; finite exit excludes a tie. -/
theorem exit_before_hit_probability (D K : Finset Site) (hKD : K ⊆ D) (x : Site) :
    pathLaw.real {ω | domainExit D x ω < setHittingTime K x 0 ω} =
      1 - setHitProbability D K x := by
  have hm : MeasurableSet {ω | 1 ≤ setOccupation D K x ω} :=
    (measurable_setOccupation D K x) measurableSet_Ici
  have he : pathLaw.real {ω | domainExit D x ω < setHittingTime K x 0 ω} =
      pathLaw.real {ω | 1 ≤ setOccupation D K x ω}ᶜ := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [domainExit_ne_top_ae D x] with ω hω
    have hh := exit_lt_setHittingTime_iff D K hKD x ω hω
    have hz : setOccupation D K x ω = 0 ↔ ¬ 1 ≤ setOccupation D K x ω := by omega
    exact propext (hh.trans hz)
  rw [he, setHitProbability_eq_probability]
  have hh := measureReal_add_measureReal_compl (μ := pathLaw) hm
  rw [probReal_univ] at hh
  linarith

/-- Translation of both disks preserves the actual strict annulus escape event. -/
theorem translated_annulus_escape_probability (a R : ℝ) (ha : 0 ≤ a) (haR : a ≤ R)
    (b x : Site) :
    pathLaw.real {ω | domainExit (translateFinset b (diskFinset R)) x ω <
      setHittingTime (translateFinset b (diskFinset a)) x 0 ω} =
      annulusOuterExitProbability a R (x - b) := by
  have hx : x = b + (x - b) := by abel
  conv_lhs => rw [hx]
  simp only [domainExit_translate, setHittingTime_translate]
  rw [exit_before_hit_probability, annulusOuterExitProbability_eq_one_sub_hit]
  intro y hy
  have hh : normSq y < a ^ 2 := by
    simpa only [mem_diskFinset, disk, Set.mem_setOf_eq] using hy
  simp only [mem_diskFinset, disk, Set.mem_setOf_eq]
  nlinarith

end SRWTightness
