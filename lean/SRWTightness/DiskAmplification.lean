import SRWTightness.ChainMaximum

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

 theorem chainSteps_lt_exitTime {a R : ℝ} (ha : 0 ≤ a) (J : ℕ)
    (hgeom : (J : ℝ) * (a + 1) < R) (ω : Sample)
    (hfin : ∀ j, exitChain a j ω ≠ ⊤) :
    (chainSteps a J ω : WithTop ℕ) < exitTime R ω := by
  have hb0 : 0 ≤ (J : ℝ) * (a + 1) := mul_nonneg (Nat.cast_nonneg J) (by linarith)
  by_contra h
  obtain ⟨k, hk, hout⟩ := (exitTime_le_iff R ω (chainSteps a J ω)).mp (le_of_not_gt h)
  have hb := normSq_up_to_chainSteps ha ω hfin J k hk
  nlinarith

/-- Source equation (10.2), proved by strong Markov iteration on the canonical SRW. -/
theorem prob_disk_max_lt_le_pow {a R : ℝ} (ha : 0 ≤ a) (J k : ℕ)
    (hgeom : (J : ℝ) * (a + 1) < R) :
    pathLaw {ω | diskMax R ω < k} ≤ (pathLaw {ω | diskMax a ω < k}) ^ J := by
  have hR : 0 ≤ R := le_of_lt (lt_of_le_of_lt
    (mul_nonneg (Nat.cast_nonneg J) (by linarith : 0 ≤ a + 1)) hgeom)
  have hfin : ∀ᵐ ω ∂pathLaw, ∀ j, exitChain a j ω ≠ ⊤ :=
    ae_all_iff.mpr (exitChain_ne_top_ae ha)
  have hsub : {ω | diskMax R ω < k} ≤ᵐ[pathLaw]
      {ω | stoppedMax (exitChain a J) ω < k} := by
    filter_upwards [hfin, exitTime_ne_top_ae hR] with ω hc he
    intro hk
    change diskMax R ω < k at hk
    change stoppedMax (exitChain a J) ω < k
    have ht := chainSteps_lt_exitTime ha J hgeom ω hc
    rw [← coe_exitSteps R ω he] at ht
    have hn : chainSteps a J ω ≤ exitSteps R ω := (WithTop.coe_lt_coe.mp ht).le
    rw [stoppedMax_eq _ ω (hc J)]
    exact lt_of_le_of_lt (maxLocalTime_mono ω hn) hk
  exact (measure_mono_ae hsub).trans (prob_chain_max_lt_le_pow ha J k)

 theorem prob_disk_max_lt_le_pow_real {a R : ℝ} (ha : 0 ≤ a) (J k : ℕ)
    (hgeom : (J : ℝ) * (a + 1) < R) :
    pathLaw.real {ω | diskMax R ω < k} ≤ (pathLaw.real {ω | diskMax a ω < k}) ^ J := by
  have h := ENNReal.toReal_mono (by finiteness) (prob_disk_max_lt_le_pow ha J k hgeom)
  simpa only [measureReal_def, ENNReal.toReal_pow] using h

end SRWTightness
