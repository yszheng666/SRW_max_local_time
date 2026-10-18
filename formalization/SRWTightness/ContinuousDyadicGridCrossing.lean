import SRWTightness.UniformGridApproximation

open Filter
open scoped Topology
namespace SRWTightness

/-- A continuous path crosses a strict level on an interval exactly when a dyadic grid sees it. -/
theorem continuous_strict_crossing_iff_uniform_dyadic (f : ℝ → ℝ) (hf : Continuous f)
    (T q : ℝ) (hT : 0 < T) :
    (∃ t ∈ Set.Icc (0 : ℝ) T, q < f t) ↔
      ∃ n : ℕ, ∃ k ≤ 2 ^ n, q < f (stoppedUniformTimeGrid 0 T (2 ^ n) k) := by
  constructor
  · rintro ⟨t, ht, hq⟩
    have hlim := hf.continuousAt.tendsto.comp
      (stoppedUniformTimeGrid_dyadic_tendsto 0 T t hT ht)
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds hq)).exists
    refine ⟨n, dyadicTimeIndex n ((t - 0) / (T - 0)), ?_, hn⟩
    apply dyadicTimeIndex_le
    exact (div_le_one (by simpa using hT)).mpr (by simpa using ht.2)
  · rintro ⟨n, k, hk, hq⟩
    exact ⟨_, stoppedUniformTimeGrid_mem 0 T (2 ^ n) k hT.le (by positivity), hq⟩

end SRWTightness
