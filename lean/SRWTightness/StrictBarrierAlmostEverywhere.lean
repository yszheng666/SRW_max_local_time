import SRWTightness.StrictBarrierDistribution

open MeasureTheory Filter
open scoped Topology
namespace SRWTightness

/-- A continuous distribution of measurable closed barriers makes the boundary event null. -/
theorem strict_barrier_ae_closed {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ) (F : ℝ → ℝ)
    (q : ℝ) (hq : 0 < q) (hF : ContinuousAt F q)
    (hm : ∀ p, 0 < p → NullMeasurableSet {ω | ∀ i, X i ω ≤ p} μ)
    (hclosed : ∀ p, 0 < p → μ.real {ω | ∀ i, X i ω ≤ p} = F p) :
    ∀ᵐ ω ∂μ, (∀ i, X i ω < q) ↔ ∀ i, X i ω ≤ q := by
  let C := fun p ↦ {ω | ∀ i, X i ω ≤ p}
  let S := {ω | ∀ i, X i ω < q}
  let D := C q \ S
  have hlim : Tendsto (fun n : ℕ ↦ q - 1 / ((n : ℝ) + 1)) atTop (nhds q) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ q) atTop (nhds q)).sub
        tendsto_one_div_add_atTop_nhds_zero_nat
  have hlimD : Tendsto (fun n : ℕ ↦ F q - F (q - 1 / ((n : ℝ) + 1)))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ F q) atTop (nhds (F q))).sub
        (hF.tendsto.comp hlim)
  have hbound : μ.real D ≤ 0 := by
    apply ge_of_tendsto hlimD
    filter_upwards [hlim.eventually (Ioi_mem_nhds hq)] with n hn
    have hp : q - 1 / ((n : ℝ) + 1) < q := by
      have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hsub : C (q - 1 / ((n : ℝ) + 1)) ⊆ C q :=
      fun ω hω i ↦ (hω i).trans hp.le
    have hds : D ⊆ C q \ C (q - 1 / ((n : ℝ) + 1)) := by
      intro ω hω
      exact ⟨hω.1, fun h ↦ hω.2 (fun i ↦ (h i).trans_lt hp)⟩
    have he : μ.real (C q \ C (q - 1 / ((n : ℝ) + 1))) =
        F q - F (q - 1 / ((n : ℝ) + 1)) := by
      rw [Measure.real, measure_sdiff hsub (hm _ hn) (measure_ne_top _ _),
        ENNReal.toReal_sub_of_le (measure_mono hsub) (measure_ne_top _ _)]
      exact congrArg₂ (· - ·) (hclosed q hq) (hclosed _ hn)
    exact (measureReal_mono hds).trans_eq he
  have hzero : μ D = 0 := (measureReal_eq_zero_iff (measure_ne_top μ D)).mp
    (le_antisymm hbound measureReal_nonneg)
  have hgood : ∀ᵐ ω ∂μ, ω ∉ D := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hzero
  filter_upwards [hgood] with ω hω
  constructor
  · intro h i
    exact (h i).le
  · intro h
    by_contra hn
    exact hω ⟨h, hn⟩

end SRWTightness
