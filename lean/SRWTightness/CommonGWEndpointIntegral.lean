import SRWTightness.SourceGWCoarseEvent
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory
open scoped BigOperators ENNReal
namespace SRWTightness

/-- A square-root GW endpoint cutoff bounds its weighted integral by the finite population sum. -/
theorem common_gw_endpoint_integral_upper (j : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (s : Set GeometricGWRecord) (hs : ∀ r ∈ s, geometricGWHeight r j ≤ q)
    (f : ℕ → ℝ≥0∞) :
    (∫⁻ r in s, f (geometricGWPopulation r j) ∂geometricGWRecordLaw 1 j) ≤
      ∑ k ∈ Finset.range (⌊q ^ 2 / 2⌋₊ + 1),
        f k * (geometricGWRecordLaw 1 j) {r | geometricGWPopulation r j = k} := by
  let I := Finset.range (⌊q ^ 2 / 2⌋₊ + 1)
  let S := fun k : ℕ ↦ {r : GeometricGWRecord | geometricGWPopulation r j = k}
  have hm : ∀ k ∈ I, MeasurableSet (S k) := fun _ _ ↦ Set.to_countable _ |>.measurableSet
  have hd : Set.PairwiseDisjoint (↑I) S := by
    intro k hk l hl hkl
    exact Set.disjoint_left.mpr (fun r hrk hrl ↦ hkl (hrk.symm.trans hrl))
  have hcover : s ⊆ ⋃ k ∈ I, S k := by
    intro r hr
    have hh := hs r hr
    unfold geometricGWHeight at hh
    have hsq := Real.sq_sqrt (show 0 ≤ 2 * (geometricGWPopulation r j : ℝ) by positivity)
    have hsqrt := Real.sqrt_nonneg (2 * (geometricGWPopulation r j : ℝ))
    have hf : geometricGWPopulation r j ≤ ⌊q ^ 2 / 2⌋₊ :=
      Nat.le_floor (by nlinarith)
    exact Set.mem_iUnion₂.mpr ⟨geometricGWPopulation r j,
      Finset.mem_range.mpr (by omega), rfl⟩
  calc
    _ ≤ ∫⁻ r in ⋃ k ∈ I, S k, f (geometricGWPopulation r j) ∂geometricGWRecordLaw 1 j :=
      lintegral_mono_set hcover
    _ = ∑ k ∈ I, ∫⁻ r in S k, f (geometricGWPopulation r j) ∂geometricGWRecordLaw 1 j :=
      lintegral_biUnion_finset hd hm _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [setLIntegral_congr_fun (hm k hk) (show Set.EqOn
        (fun r ↦ f (geometricGWPopulation r j)) (fun _ ↦ f k) (S k) from
          fun r hr ↦ congrArg f hr)]
      simp [S]

end SRWTightness
