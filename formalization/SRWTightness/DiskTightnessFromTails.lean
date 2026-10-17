import SRWTightness.CompactDiskTightness
import SRWTightness.SpatialTargets
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

theorem disk_upper_bound_tendsto_zero (C : ℝ) :
    Tendsto (fun s : ℝ ↦ C * (1 + s) * Real.exp (-3 * s / 2)) atTop (𝓝 0) := by
  have ht : Tendsto (fun s : ℝ ↦ 3 * s / 2) atTop atTop :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 3)).atTop_div_const (by norm_num)
  have h₀ := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  have h₁ := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht
  have h := (h₀.add (h₁.const_mul (2 / 3 : ℝ))).const_mul C
  convert h using 1
  · ext s
    dsimp [Function.comp_def]
    rw [show -3 * s / 2 = -(3 * s / 2) by ring]
    ring
  · simp

theorem disk_lower_bound_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun s : ℝ ↦ Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 4))) atTop (𝓝 0) := by
  have ht : Tendsto (fun s : ℝ ↦ Real.sqrt Real.pi * s / 4) atTop atTop :=
    (tendsto_id.const_mul_atTop (Real.sqrt_pos.mpr Real.pi_pos)).atTop_div_const (by norm_num)
  have he := (Real.tendsto_exp_atTop.comp ht).const_mul_atTop hc
  simpa only [Function.comp_def, neg_mul] using Real.tendsto_exp_neg_atTop_nhds_zero.comp he

theorem diskTightness_of_diskTails (h : DiskTailClaim) : DiskTightnessClaim := by
  obtain ⟨C, c, s₀, hC, hc, hs₀, htail⟩ := h
  apply diskTightness_of_eventual_tails
  intro ε hε
  have hu : ∀ᶠ s : ℝ in atTop, C * (1 + s) * Real.exp (-3 * s / 2) < ε / 2 :=
    (disk_upper_bound_tendsto_zero C).eventually (gt_mem_nhds (by positivity))
  have hl : ∀ᶠ s : ℝ in atTop, Real.exp (-c * Real.exp (Real.sqrt Real.pi * s / 4)) < ε / 2 :=
    (disk_lower_bound_tendsto_zero c hc).eventually (gt_mem_nhds (by positivity))
  obtain ⟨s, hs, hus, hls⟩ := ((eventually_ge_atTop s₀).and (hu.and hl)).exists
  obtain ⟨htu, htl⟩ := htail s hs
  have heu : ∀ᶠ R : ℝ in atTop, pathLaw.real {ω | s < diskFluctuation R ω} < ε / 2 :=
    eventually_lt_of_limsup_lt (htu.trans_lt hus)
      (isBoundedUnder_of ⟨1, fun R ↦ measureReal_le_one⟩)
  have hel : ∀ᶠ R : ℝ in atTop, pathLaw.real {ω | diskFluctuation R ω < -s} < ε / 2 :=
    eventually_lt_of_limsup_lt (htl.trans_lt hls)
      (isBoundedUnder_of ⟨1, fun R ↦ measureReal_le_one⟩)
  refine ⟨s, hs₀.le.trans hs, ?_⟩
  filter_upwards [heu, hel] with R hRu hRl
  have hsub : {ω | s < |diskFluctuation R ω|} ⊆
      {ω | s < diskFluctuation R ω} ∪ {ω | diskFluctuation R ω < -s} := by
    intro ω hω
    change s < |diskFluctuation R ω| at hω
    rcases lt_abs.mp hω with hp | hn
    · exact Or.inl hp
    · right
      change diskFluctuation R ω < -s
      linarith
  have hm := measureReal_mono (μ := pathLaw) hsub (measure_ne_top _ _)
  have hadd := measureReal_union_le (μ := pathLaw)
    {ω | s < diskFluctuation R ω} {ω | diskFluctuation R ω < -s}
  linarith

end SRWTightness
