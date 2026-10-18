import SRWTightness.LabeledRootCountMixture
import SRWTightness.SourceExteriorEntranceShell
import SRWTightness.SourceEarlyRootCap

open Filter
open scoped BigOperators
namespace SRWTightness

/-- Every positive count composition below the two original caps has the same uniform source error.
This holds for all reference compositions, including those not selected by an observed path. -/
theorem source_count_product_error_cap :
    ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ, ν ≤ 2 * sourceCoarseLowerLevel t →
      ∀ (J : ℕ) (A C : ℝ), 0 ≤ A → 0 ≤ C →
      ∀ {n : ℕ} (label : Fin n → Bool) (r : Fin n → ℕ) (k l : ℕ),
      (∀ i, 0 < r i) → labeledRootTotal label r false = k → labeledRootTotal label r true = l →
      k ≤ sourceEarlyRootCap t ν → l ≤ sourceEarlyRootCap t ν →
      let δ := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
      let ε := C * 15 / (sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)
      (∑ i, (δ + ε * (r i : ℝ))) ≤ 16 * ((ν : ℝ) + 1) ^ 2 * (δ + ε) := by
  filter_upwards [source_early_root_cap_quadratic, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hcap hN htime hm ht
  intro ν hν J A C hA hC n label r k l hr hk hl hkc hlc
  dsimp only
  have hnreal : (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  have hrad := sourceRecordRadius_ge_terminal (sourceLowerRadius t) (sourceLowerRadius_pos t).le
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) hi
  let δ := A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ))
  let ε := C * 15 / (sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hε : 0 ≤ ε := div_nonneg (mul_nonneg hC (by norm_num)) (by linarith)
  have hkr : (k : ℝ) ≤ 8 * ((ν : ℝ) + 1) ^ 2 := (Nat.cast_le.mpr hkc).trans (hcap ν)
  have hlr : (l : ℝ) ≤ 8 * ((ν : ℝ) + 1) ^ 2 := (Nat.cast_le.mpr hlc).trans (hcap ν)
  calc
    _ ≤ (δ + ε) * ((k : ℝ) + l) := positive_root_vector_cost label r k l hr hk hl δ ε hδ
    _ ≤ (δ + ε) * (16 * ((ν : ℝ) + 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (add_nonneg hδ hε)
    _ = _ := mul_comm _ _

end SRWTightness
