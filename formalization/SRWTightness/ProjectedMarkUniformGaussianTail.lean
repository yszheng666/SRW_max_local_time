import SRWTightness.ProjectedMarkGaussianBranches
import SRWTightness.GaussianNegativeUniformTail

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- When the positive branch starts above zero, both branches obey its uniform Gaussian tail. -/
theorem projected_fixed_mark_uniform_gaussian_tail (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (k a : ℕ) (hk : 1 ≤ k) (ha : 1 ≤ a)
    (V : ℝ) (hV : 0 < V) (hdiag : ∀ z : A, killedGreen D z z ≤ V)
    (hpos : 0 ≤ Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * ((k : ℝ) * α))) :
    (markProductLaw D K α k).real
      {Y | ∃ z : A, a ≤ sumMarks K k Y ⟨z, hAK z.property⟩} ≤
      1152 * (A.card : ℝ) * Real.exp
        (-(Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * ((k : ℝ) * α))) ^ 2 / (2 * V)) := by
  let p := Real.sqrt (2 * (a : ℝ)) - Real.sqrt (2 * ((k : ℝ) * α))
  let n := Real.sqrt (2 * (a : ℝ)) + Real.sqrt (2 * ((k : ℝ) * α))
  have hpn : p ≤ n := by dsimp [p, n]; linarith [Real.sqrt_nonneg (2 * ((k : ℝ) * α))]
  have hn : 0 ≤ n := hpos.trans hpn
  have hep : (gaussianGreenLaw D A).real {φ | ∃ z : A, p ≤ φ z} ≤
      (A.card : ℝ) * Real.exp (-p ^ 2 / (2 * V)) :=
    (gaussianGreenLaw_max_tail D A (hAK.trans hKD) p hpos).trans
      (gaussian_negative_tail_sum_uniform D A (hAK.trans hKD) p V hpos hV hdiag)
  have hen := gaussian_negative_tail_sum_uniform D A (hAK.trans hKD) n V hn hV hdiag
  have hexp : Real.exp (-n ^ 2 / (2 * V)) ≤ Real.exp (-p ^ 2 / (2 * V)) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_self_le_mul_self hpos hpn]
  have hen' := hen.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hb := projected_fixed_mark_gaussian_branches D A K hAK hKD α hα hcap k a hk ha
  have hh := mul_le_mul_of_nonneg_left (add_le_add hep hen') (by norm_num : (0 : ℝ) ≤ 576)
  calc
    _ ≤ _ := hb.trans hh
    _ = _ := by dsimp [p]; ring

end SRWTightness
