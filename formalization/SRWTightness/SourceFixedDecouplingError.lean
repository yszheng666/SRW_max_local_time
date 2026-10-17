import SRWTightness.SourceEarlyReturnError

open Filter
namespace SRWTightness

/-- At a bounded continuation level, the comparison exponent is uniformly bounded even when
there is no positive lower bound on the distance index. -/
theorem source_fixed_decoupling_exponent_bounded (D C B W : ℝ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) :
    ∀ᶠ t : ℝ in atTop, ∀ ν J : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t → J ≤ ν →
      sourceDecouplingExponent D C B W t ν J ≤ 16 * D * ((ν : ℝ) + 1) ^ 3 + 1 := by
  have he := (tendsto_order.1 (source_decoupling_small_error_tendsto_zero C B W)).2
    (1 : ℝ) (by norm_num)
  filter_upwards [source_early_return_error, he] with t hreturn he
  intro ν J hν hJ
  have hret := hreturn ν hν C hC
  have hexp : Real.exp (-(J : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hlead : D * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) ≤ D * ((ν : ℝ) + 1) := by
    calc
      _ ≤ D * ((J : ℝ) + 1) * 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ D * ((ν : ℝ) + 1) := by
        simpa using mul_le_mul_of_nonneg_left
          (add_le_add (Nat.cast_le.mpr hJ) (le_refl (1 : ℝ))) hD
  have hscaled := mul_le_mul_of_nonneg_left hlead
    (show 0 ≤ 16 * ((ν : ℝ) + 1) ^ 2 by positivity)
  unfold sourceDecouplingExponent
  unfold sourceDecouplingSmallError at he
  nlinarith only [hscaled, hret, he]

end SRWTightness
