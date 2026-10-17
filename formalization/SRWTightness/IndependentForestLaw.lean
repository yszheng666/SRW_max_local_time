import SRWTightness.ActualForestEventUpper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.List.OfFn

open MeasureTheory
open scoped BigOperators

namespace SRWTightness

/-- A fixed-size independent reference forest, represented by its ordered root list. -/
noncomputable def independentForestLaw {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] (μ : Measure M) (j : ℕ) : Measure (List M) :=
  (Measure.pi (fun _ : Fin j ↦ μ)).map List.ofFn

instance independentForestLaw_isProbabilityMeasure {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass M] [Countable M]
    (μ : Measure M) [IsProbabilityMeasure μ]
    (j : ℕ) : IsProbabilityMeasure (independentForestLaw μ j) := by
  unfold independentForestLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- The singleton mass is the product of the independent root masses. -/
theorem independentForestLaw_ofFn {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)] [MeasurableSingletonClass M] [Countable M]
    (μ : Measure M) [IsProbabilityMeasure μ] (j : ℕ) (f : Fin j → M) :
    independentForestLaw μ j {List.ofFn f} = ∏ i, μ {f i} := by
  rw [independentForestLaw, Measure.map_apply (measurable_of_countable _)
    (measurableSet_singleton _)]
  have hs : List.ofFn ⁻¹' {List.ofFn f} = {f} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, List.ofFn_inj]
  rw [hs, Measure.pi_singleton]

/-- A prescribed list of the correct length has the product of its real singleton masses. -/
theorem independentForestLaw_singleton {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ]
    (j : ℕ) (rs : List M) (hlen : rs.length = j) :
    independentForestLaw μ j {rs} = ENNReal.ofReal ((rs.map (fun v ↦ μ.real {v})).prod) := by
  subst j
  have hh := independentForestLaw_ofFn μ rs.length rs.get
  rw [List.ofFn_get] at hh
  have hp : (rs.map (fun v ↦ μ.real {v})).prod = ∏ i : Fin rs.length, μ.real {rs.get i} := by
    simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply] using
      congrArg (fun l : List M ↦ (l.map (fun v ↦ μ.real {v})).prod) (List.ofFn_get rs).symm
  rw [hh, hp, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ measureReal_nonneg)]
  simp only [ofReal_measureReal (measure_ne_top μ _)]

/-- Any event of fixed-size reference forests has precisely the sum of branching product weights. -/
theorem independentForestLaw_event {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ]
    (j : ℕ) (s : Set (List M)) (hlen : ∀ rs ∈ s, rs.length = j) :
    independentForestLaw μ j s =
      ∑' rs : s, ENNReal.ofReal ((rs.val.map (fun v ↦ μ.real {v})).prod) := by
  have hh := tsum_measure_preimage_singleton (μ := independentForestLaw μ j)
    (f := id) s.to_countable (fun r _ ↦ measurableSet_singleton r)
  simp only [Set.preimage_id] at hh
  rw [← hh]
  apply tsum_congr
  intro rs
  exact independentForestLaw_singleton μ j rs (hlen rs rs.property)

end SRWTightness
