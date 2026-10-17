import SRWTightness.PairMarkTiltVariance
import SRWTightness.PairTiltCgf

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Signed cumulant expansion for the actual two-site marks and common equilibrium average. -/
theorem pair_mark_tilt_cgf_taylor (D M : Finset Site) (b : Site) (a : ℝ)
    (ha : 2 ≤ a) (hKM : translateFinset b (diskFinset a) ⊆ M) (hMD : M ⊆ D)
    (z y : M) (hz : Real.sqrt (normSq ((z : Site) - b)) < a - 1)
    (hy : Real.sqrt (normSq ((y : Site) - b)) < a - 1)
    (α g u : ℝ) (hα : 0 < α) (hg : 0 < g) (hu : 0 < u)
    (hcap : α * capacity D M ≤ 1) (k : ℕ) (hk : u ^ 2 / 2 = (k : ℝ))
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ x : M, killedGreen D x x ≤ L)
    (hsmall : 6 ≤ (u * Real.sqrt (α * g)) / (8 * L)) :
    let μ := markProductLaw D M α k
    let F := normalizedMarkSum M k α g u z
    let G := normalizedMarkSum M k α g u y
    let S := normalizedEquilibriumAverage D M (translateFinset b (diskFinset a)) k α g u
    let v := equilibriumEnergyTime D (translateFinset b (diskFinset a)) α g
    let e := (∑ x ∈ translateFinset b (diskFinset a),
      equilibriumWeight D (translateFinset b (diskFinset a)) x ^ 2) / (2 * g)
    |cgf ((2 : ℝ) • (F + G - S)) μ 1 -
      (2 * covariance F F μ + 2 * covariance G G μ + 4 * covariance F G μ - 6 * v - 2 * e)| ≤
        23592976 * L ^ 3 * 6 ^ 3 / (12 * u * (Real.sqrt (α * g)) ^ 3) := by
  have hne : (translateFinset b (diskFinset a)).Nonempty := by
    refine ⟨b, ?_⟩
    rw [mem_translateFinset_iff, sub_self]
    exact zero_mem_diskFinset a (by linarith)
  have hw1 : (∑ x : M, equilibriumWeight D (translateFinset b (diskFinset a)) x) = 1 := by
    simpa only [Finset.sum_coe_sort] using
      equilibriumWeight_sum_over D M _ hKM (hKM.trans hMD) hne
  have ht := pair_tilt_cgf_half_variance D M hMD z y
    (fun x ↦ equilibriumWeight D (translateFinset b (diskFinset a)) x)
    (fun x ↦ equilibriumWeight_nonneg _ _ _) hw1 α g u hα hg hu hcap L hL hαL hG hsmall k hk
  have hv := pair_mark_tilt_half_variance D M b a ha hKM hMD z y hz hy
    α g u hα hg hu hcap k hk
  dsimp only [normalizedEquilibriumAverage] at hv ⊢
  dsimp only at ht
  rw [hv] at ht
  exact ht

end SRWTightness
