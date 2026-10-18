import SRWTightness.OddHarmonicAsymptotic
import SRWTightness.DiagonalLatticeNorm

open Filter
open scoped BigOperators Topology
namespace SRWTightness

/-- The explicit planar SRW potential constant appearing in the manuscript. -/
noncomputable def sourcePotentialConstant : ℝ :=
  (2 * Real.eulerMascheroniConstant + 3 * Real.log 2) / Real.pi

/-- The exact odd harmonic expression yields the manuscript constant after radial normalization. -/
theorem diagonal_harmonic_constant_limit :
    Tendsto (fun n : ℕ ↦ (4 / Real.pi) *
      (∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1)) -
      (2 / Real.pi) * Real.log (Real.sqrt (normSq ((n : ℤ), (n : ℤ)))))
      atTop (𝓝 sourcePotentialConstant) := by
  have hlim := (odd_harmonic_sum_limit.const_mul (4 / Real.pi)).sub_const
    ((1 / Real.pi) * Real.log 2)
  have he : (4 / Real.pi) * (Real.eulerMascheroniConstant / 2 + Real.log 2) -
      (1 / Real.pi) * Real.log 2 = sourcePotentialConstant := by
    unfold sourcePotentialConstant
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  rw [diagonal_lattice_log_norm n (by omega)]
  ring

end SRWTightness
