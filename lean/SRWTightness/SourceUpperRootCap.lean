import SRWTightness.SourceUpperBlockRootCount
import SRWTightness.SourceUpperBlockTotalCount

open Filter MeasureTheory

namespace SRWTightness

/-- Some actual source upper block exceeds the prescribed root count cap. -/
def sourceUpperRootCapEvent (t : ℝ) : Set Sample :=
  ⋃ b ∈ sourceUpperBlockCenters t,
    {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)}

/-- The actual root cap event is measurable. -/
theorem measurableSet_sourceUpperRootCapEvent (t : ℝ) :
    MeasurableSet (sourceUpperRootCapEvent t) := by
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.iUnion
  intro hb
  let F : PathWord → ℕ := fun w ↦ (wordChildIntervals
    (sourceUpperBlockInner t (sourceUpperBlockRoot t b) b)
    (sourceUpperBlockOuter t (sourceUpperBlockRoot t b) b) 0 w).length
  exact (measurable_killedPathWord (diskFinset (Real.exp t)) 0)
    (Set.to_countable {w : PathWord | t ^ 2 < (F w : ℝ)}).measurableSet

/-- Uniform cap tail for the actual blocks at their selected root levels. -/
theorem source_upper_block_root_cap_tail (hinput : PotentialKernelAsymptoticInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      pathLaw.real {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)} ≤
        Real.exp (-t ^ 2 / (4 * Real.log t)) := by
  obtain ⟨K, hK, htail⟩ := source_upper_block_root_count_tail hinput
  filter_upwards [htail, source_upper_block_root_conditions, eventually_ge_atTop (2 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (K + 1))] with t ht hk ht2 hlog
  intro b hb
  let n := ⌊t ^ 2⌋₊
  let H := (sourceUpperBlockRoot t b : ℝ) + K
  have hH : 0 < H := by
    dsimp [H]
    linarith [(Nat.cast_nonneg (sourceUpperBlockRoot t b) : (0 : ℝ) ≤ _)]
  have hHlog : H ≤ 2 * Real.log t := by
    have h := (hk b hb).2.1
    dsimp [H]
    linarith
  have hl : 0 < Real.log t := by linarith
  have hn : t ^ 2 / 2 ≤ (n : ℝ) := by
    have h := Nat.lt_floor_add_one (t ^ 2)
    dsimp [n]
    nlinarith [sq_nonneg (t - 2)]
  have hfrac : t ^ 2 / (4 * Real.log t) ≤ (n : ℝ) / H := by
    apply (div_le_div_iff₀ (by positivity) hH).mpr
    have h₁ := mul_le_mul_of_nonneg_left hHlog (sq_nonneg t)
    have h₂ := mul_le_mul_of_nonneg_right hn (by positivity : 0 ≤ 4 * Real.log t)
    nlinarith
  have hsub : {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)} ⊆
      {ω | n + 1 ≤ sourceUpperBlockRootCount t b ω} := by
    intro ω hω
    exact Nat.succ_le_iff.mpr ((Nat.floor_lt (sq_nonneg t)).mpr hω)
  calc
    _ ≤ pathLaw.real {ω | n + 1 ≤ sourceUpperBlockRootCount t b ω} :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ Real.exp (-(n : ℝ) / H) := ht b hb n
    _ ≤ _ := Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hfrac)

/-- Equation (4.23): the actual union of root cap failures has the stated majorant. -/
theorem source_upper_root_cap_probability (hinput : PotentialKernelAsymptoticInput) :
    ∀ᶠ t : ℝ in atTop, pathLaw.real (sourceUpperRootCapEvent t) ≤
      25 * Real.exp (2 * t - t ^ 2 / (4 * Real.log t)) := by
  filter_upwards [source_upper_block_root_cap_tail hinput, source_upper_block_total_count]
    with t ht hc
  calc
    _ ≤ ∑ b ∈ sourceUpperBlockCenters t,
        pathLaw.real {ω | t ^ 2 < (sourceUpperBlockRootCount t b ω : ℝ)} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ b ∈ sourceUpperBlockCenters t, Real.exp (-t ^ 2 / (4 * Real.log t)) :=
      Finset.sum_le_sum (fun b hb ↦ ht b hb)
    _ = ((sourceUpperBlockCenters t).card : ℝ) *
        Real.exp (-t ^ 2 / (4 * Real.log t)) := by simp
    _ ≤ (25 * (Real.exp t) ^ 2) * Real.exp (-t ^ 2 / (4 * Real.log t)) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ = _ := by
      rw [show 2 * t - t ^ 2 / (4 * Real.log t) =
        (t + t) + (-t ^ 2 / (4 * Real.log t)) by ring, Real.exp_add, Real.exp_add]
      ring

end SRWTightness
