import SRWTightness.Targets
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Order.Basic

open Filter MeasureTheory
open scoped Topology

namespace SRWTightness

/-- Uniform eventual smallness of bounded nonnegative tails gives the iterated limsup limit. -/
theorem tail_limsup_tendsto_zero {ι : Type*} (f : Filter ι) [NeBot f]
    (u : ℝ → ι → ℝ) (hzero : ∀ K i, 0 ≤ u K i) (hone : ∀ K i, u K i ≤ 1)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ k : ℝ, K ≤ k →
      ∀ᶠ i in f, u k i ≤ ε) :
    Tendsto (fun K : ℝ ↦ limsup (u K) f) atTop (𝓝 0) := by
  have hn : ∀ K, 0 ≤ limsup (u K) f := by
    intro K
    apply le_limsup_of_le (isBoundedUnder_of ⟨1, hone K⟩)
    intro b hb
    obtain ⟨i, hi⟩ := hb.exists
    exact (hzero K i).trans hi
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun K ↦ ha.trans_le (hn K))
  · intro b hb
    obtain ⟨K, hK⟩ := hsmall (b / 2) (by positivity)
    filter_upwards [eventually_ge_atTop K] with k hk
    have hh : limsup (u k) f ≤ b / 2 :=
      limsup_le_of_le (isCoboundedUnder_le_of_le f (hzero k)) (hK k hk)
    linarith

/-- Uniform tightness for all n>=3 implies the literal source equation (1.2). -/
theorem time_tightness_double_limit (h : TimeTightnessClaim) :
    Tendsto (fun K : ℝ ↦ limsup
      (fun n : ℕ ↦ pathLaw.real {ω | K < |timeFluctuation n ω|}) atTop)
      atTop (𝓝 0) := by
  apply tail_limsup_tendsto_zero atTop _
    (fun _ _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_le_one)
  intro ε hε
  obtain ⟨K, _, hK⟩ := h ε hε
  refine ⟨K, ?_⟩
  intro k hk
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  have hsub : {ω | k < |timeFluctuation n ω|} ⊆
      {ω | K < |timeFluctuation n ω|} := fun _ hω ↦ hk.trans_lt hω
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hK n hn).le

/-- Uniform real-radius tightness implies the literal source equation (1.4). -/
theorem disk_tightness_double_limit (h : DiskTightnessClaim) :
    Tendsto (fun K : ℝ ↦ limsup
      (fun R : ℝ ↦ pathLaw.real {ω | K < |diskFluctuation R ω|}) atTop)
      atTop (𝓝 0) := by
  apply tail_limsup_tendsto_zero atTop _
    (fun _ _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_le_one)
  intro ε hε
  obtain ⟨K, _, hK⟩ := h 2 (by norm_num) ε hε
  refine ⟨K, ?_⟩
  intro k hk
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with R hR
  have hsub : {ω | k < |diskFluctuation R ω|} ⊆
      {ω | K < |diskFluctuation R ω|} := fun _ hω ↦ hk.trans_lt hω
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hK R hR).le

/-- The convention including the final visit has the same iterated-limit conclusion. -/
theorem inclusive_time_tightness_double_limit (h : InclusiveTimeTightnessClaim) :
    Tendsto (fun K : ℝ ↦ limsup
      (fun n : ℕ ↦ pathLaw.real
        {ω | K < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n|}) atTop)
      atTop (𝓝 0) := by
  apply tail_limsup_tendsto_zero atTop _
    (fun _ _ ↦ measureReal_nonneg) (fun _ _ ↦ measureReal_le_one)
  intro ε hε
  obtain ⟨K, _, hK⟩ := h ε hε
  refine ⟨K, ?_⟩
  intro k hk
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
  have hsub : {ω | k < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n|} ⊆
      {ω | K < |Real.sqrt (inclusiveMaxLocalTime ω n) - timeCenter n|} :=
    fun _ hω ↦ hk.trans_lt hω
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans (hK n hn).le

end SRWTightness
