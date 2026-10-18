import SRWTightness.SourceEarlyProductLogMoment
import SRWTightness.SourceEarlyBarrierTilt
import SRWTightness.RootPairSquareRootMoment

open MeasureTheory Filter
namespace SRWTightness

/-- Equation 8.22 under the actual early common-reference product law and barrier cap. -/
theorem source_early_square_root_moment (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hinput : PotentialKernelAsymptoticInput)
    (γ : ℝ) (hγ : γ ≤ 1) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ z w : Site, z ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
      let J := sourceEarlyDistanceGap a J₀
      let j := a - J
      let ν := a + J + 5
      let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ γ
      let P := sourceCommonWordLaw t z w j
      ∀ k : ℕ, Real.sqrt (2 * (k : ℝ)) ≤ b →
      let Kz := fun Y : Fin k → WordMark ↦ ∑ i, (sourceCommonWordRootCount t z ν (Y i) : ℝ)
      let Kw := fun Y : Fin k → WordMark ↦ ∑ i, (sourceCommonWordRootCount t w ν (Y i) : ℝ)
      Integrable (fun Y ↦ Real.exp (2 * Real.sqrt (2 * Kz Y) +
        2 * Real.sqrt (2 * Kw Y))) (Measure.pi (fun _ : Fin k ↦ P)) ∧
      (∫ Y, Real.exp (2 * Real.sqrt (2 * Kz Y) + 2 * Real.sqrt (2 * Kw Y))
        ∂Measure.pi (fun _ : Fin k ↦ P)) ≤
        Real.exp (2 * b + 2 * (Real.sqrt (2 * (k : ℝ))) ^ 2 / b +
          C * ((J : ℝ) + 1) + D / t ^ 5) := by
  obtain ⟨C, D, hC, hD, Jm, hm⟩ := source_early_product_log_moment hLast hrec hinput
  obtain ⟨Jp, hp⟩ := source_early_common_root_mean hLast
  refine ⟨12 + 48 * C, 8 * D, by positivity, by positivity, max Jm Jp, ?_⟩
  intro J₀ hJ₀
  obtain ⟨am, ham, hm⟩ := hm J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨ap, hap, hp⟩ := hp J₀ ((le_max_right _ _).trans hJ₀)
  obtain ⟨ab, hab, ht⟩ := source_early_barrier_tilt J₀ C γ hC hγ
  refine ⟨max am (max ap ab), ham.trans (le_max_left _ _), ?_⟩
  filter_upwards [hm, hp, ht] with t hm hp ht
  intro z w hzw ha hrange
  dsimp only
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - z)))
  let J := sourceEarlyDistanceGap a J₀
  let j := a - J
  let ν := a + J + 5
  let b := 4 + sourceBarrierSlope t * j - (j : ℝ) ^ γ
  let P := sourceCommonWordLaw t z w j
  have hm := hm z w hzw ((le_max_left _ _).trans ha) hrange
  have hp := (hp z w hzw
    ((le_max_left _ _).trans ((le_max_right _ _).trans ha)) hrange).1
  have ht := ht a ((le_max_right _ _).trans ((le_max_right _ _).trans ha))
  letI : IsProbabilityMeasure P := hp
  have hb4 : 4 ≤ b := ht.1
  have hb : 0 < b := by linarith
  intro k hk
  let Kz := fun Y : Fin k → WordMark ↦ ∑ i, (sourceCommonWordRootCount t z ν (Y i) : ℝ)
  let Kw := fun Y : Fin k → WordMark ↦ ∑ i, (sourceCommonWordRootCount t w ν (Y i) : ℝ)
  have hksq : 2 * (k : ℝ) ≤ b ^ 2 := by
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg (2 * (k : ℝ))) hk 2
    rwa [Real.sq_sqrt (by positivity)] at hh
  have hcap : (k : ℝ) ≤ 8 * ((j : ℝ) + 1) ^ 2 := by
    have hh := pow_le_pow_left₀ hb.le ht.2.1 2
    nlinarith
  have hmoment := hm 8 (by norm_num) k hcap (2 / b) ht.2.2.1 ht.2.2.2.1 ht.2.2.2.2
  have heq (Y : Fin k → WordMark) :
      (∑ i, ((sourceCommonWordRootCount t z ν (Y i) +
        sourceCommonWordRootCount t w ν (Y i) : ℕ) : ℝ)) = Kz Y + Kw Y := by
    simp only [Nat.cast_add, Finset.sum_add_distrib, Kz, Kw]
  change Integrable (fun Y : Fin k → WordMark ↦ Real.exp ((2 / b) *
      ∑ i, ((sourceCommonWordRootCount t z ν (Y i) +
        sourceCommonWordRootCount t w ν (Y i) : ℕ) : ℝ)))
      (Measure.pi (fun _ : Fin k ↦ P)) ∧
    Real.log (∫ Y : Fin k → WordMark, Real.exp ((2 / b) *
      ∑ i, ((sourceCommonWordRootCount t z ν (Y i) +
        sourceCommonWordRootCount t w ν (Y i) : ℕ) : ℝ))
      ∂Measure.pi (fun _ : Fin k ↦ P)) ≤
      2 * k * (2 / b) + (6 + 24 * C) * k * ((J : ℝ) + 1) * (2 / b) ^ 2 +
        8 * D / t ^ 5 at hmoment
  simp_rw [heq] at hmoment
  have hh := root_pair_square_root_moment (Measure.pi (fun _ : Fin k ↦ P)) Kz Kw
    (measurable_of_countable _) (measurable_of_countable _)
    (fun Y ↦ by dsimp [Kz]; positivity) (fun Y ↦ by dsimp [Kw]; positivity)
    b (2 * k * (2 / b) + (6 + 24 * C) * k * ((J : ℝ) + 1) * (2 / b) ^ 2 +
      8 * D / t ^ 5) hb hmoment.1 hmoment.2
  refine ⟨hh.1, hh.2.trans (Real.exp_le_exp.mpr ?_)⟩
  have hquad : (k : ℝ) * (2 / b) ^ 2 ≤ 2 := by
    calc
      _ = (4 * (k : ℝ)) / b ^ 2 := by ring
      _ ≤ 2 := (div_le_iff₀ (sq_pos_of_pos hb)).2 (by linarith)
  have hq := mul_le_mul_of_nonneg_left hquad
    (show 0 ≤ (6 + 24 * C) * ((J : ℝ) + 1) by positivity)
  change 2 * b + (2 * k * (2 / b) +
      (6 + 24 * C) * k * ((J : ℝ) + 1) * (2 / b) ^ 2 + 8 * D / t ^ 5) ≤
    2 * b + 2 * (Real.sqrt (2 * (k : ℝ))) ^ 2 / b +
      (12 + 48 * C) * ((J : ℝ) + 1) + 8 * D / t ^ 5
  rw [Real.sq_sqrt (by positivity)]
  calc
    _ = (2 * b + 2 * (2 * (k : ℝ)) / b) +
        (6 + 24 * C) * ((J : ℝ) + 1) * ((k : ℝ) * (2 / b) ^ 2) + 8 * D / t ^ 5 := by
      ring
    _ ≤ (2 * b + 2 * (2 * (k : ℝ)) / b) +
        (6 + 24 * C) * ((J : ℝ) + 1) * 2 + 8 * D / t ^ 5 :=
      add_le_add (add_le_add (le_refl _) hq) (le_refl _)
    _ = _ := by ring

end SRWTightness
