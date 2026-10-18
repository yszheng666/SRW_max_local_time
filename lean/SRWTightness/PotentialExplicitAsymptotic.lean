import SRWTightness.PotentialDiagonalIntegral
import SRWTightness.ExplicitPotentialConstant
import SRWTightness.ExternalPotentialAsymptotic

open Filter
open scoped Topology
namespace SRWTightness

/-- The actual diagonal potential has the explicit manuscript constant in its logarithmic limit. -/
theorem potentialKernel_diagonal_constant_limit :
    Tendsto (fun n : ℕ ↦ potentialKernel ((n : ℤ), (n : ℤ)) -
      (2 / Real.pi) * Real.log (Real.sqrt (normSq ((n : ℤ), (n : ℤ)))))
      atTop (𝓝 sourcePotentialConstant) := by
  simpa only [potentialKernel_diagonal_exact] using diagonal_harmonic_constant_limit

/-- Any inverse-square potential asymptotic must use the explicitly computed diagonal constant. -/
theorem potentialKernel_asymptotic_constant_eq (κ C R₀ : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤
        C / normSq z) : κ = sourcePotentialConstant := by
  have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ C / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ ↦ x⁻¹) atTop (𝓝 0)).comp hn).const_mul C
  have hz : Tendsto (fun n : ℕ ↦ potentialKernel ((n : ℤ), (n : ℤ)) -
      ((2 / Real.pi) * Real.log (Real.sqrt (normSq ((n : ℤ), (n : ℤ)))) + κ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_ hsmall
    filter_upwards [hn.eventually (eventually_ge_atTop (max 1 R₀))] with n hlarge
    have hn1 : 1 ≤ (n : ℝ) := (le_max_left _ _).trans hlarge
    have hnR : R₀ ≤ (n : ℝ) := (le_max_right _ _).trans hlarge
    have hroot : (n : ℝ) ≤ Real.sqrt (normSq ((n : ℤ), (n : ℤ))) := by
      rw [diagonal_lattice_norm]
      have htwo : 1 ≤ Real.sqrt (2 : ℝ) :=
        (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      nlinarith
    have hden : (n : ℝ) ≤ normSq ((n : ℤ), (n : ℤ)) := by
      rw [diagonal_lattice_normSq]
      nlinarith
    have hh := (hb ((n : ℤ), (n : ℤ)) (hnR.trans hroot)).trans
      (div_le_div_of_nonneg_left hC (by linarith : 0 < (n : ℝ)) hden)
    simpa only [Real.norm_eq_abs] using hh
  have hk : Tendsto (fun n : ℕ ↦ potentialKernel ((n : ℤ), (n : ℤ)) -
      (2 / Real.pi) * Real.log (Real.sqrt (normSq ((n : ℤ), (n : ℤ)))))
      atTop (𝓝 κ) := by
    have hh := hz.add_const κ
    simp only [zero_add] at hh
    convert hh using 1
    funext n
    ring
  exact tendsto_nhds_unique hk potentialKernel_diagonal_constant_limit

/-- Source (2.5) with its literal Euler--Mascheroni constant, using the original asymptotic
input. -/
theorem potentialKernel_explicit_asymptotic (hinput : PotentialKernelAsymptoticInput) :
    ∃ C R₀ : ℝ, 0 ≤ C ∧ 1 ≤ R₀ ∧ ∀ z : Site,
      R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) +
        sourcePotentialConstant)| ≤ C / normSq z := by
  obtain ⟨κ, C, R₀, hC, hR₀, hb⟩ := hinput
  have hκ := potentialKernel_asymptotic_constant_eq κ C R₀ hC hb
  subst κ
  exact ⟨C, R₀, hC, hR₀, hb⟩

end SRWTightness
