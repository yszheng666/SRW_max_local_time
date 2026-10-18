import SRWTightness.ExternalFiniteGaussianBridgeKernel

open MeasureTheory

namespace SRWTightness

theorem finiteGaussianMesh_measurable (n j : ℕ) :
    Measurable (fun x : Fin n → ℝ ↦ finiteGaussianMesh n x j) := by
  unfold finiteGaussianMesh
  split_ifs <;> fun_prop

theorem finiteGaussianBridgedPath_measurable (T : ℕ → ℝ) (n M : ℕ) (v : ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (ℕ → GaussianCoefficientSpace) ↦
      finiteGaussianBridgedPath T n M p.1 p.2 v) := by
  unfold finiteGaussianBridgedPath timeGridInterpolation
  apply Measurable.add
  · exact ((finiteGaussianMesh_measurable n 0).comp measurable_fst).add
      (Finset.measurable_sum _ (fun j _ ↦ measurable_const.mul
        (((finiteGaussianMesh_measurable n (j + 1)).comp measurable_fst).sub
          ((finiteGaussianMesh_measurable n j).comp measurable_fst))))
  · exact (timeGridBridge_measurable T M v).comp measurable_snd

theorem finiteGaussianPrefixWindow_measurable (T : ℕ → ℝ) (n M : ℕ)
    (last : Fin n) (q a b : ℝ) :
    MeasurableSet (finiteGaussianPrefixWindow T n M last q a b) := by
  simp only [finiteGaussianPrefixWindow, Set.setOf_and, Set.setOf_forall]
  exact (measurableSet_Icc.preimage (by fun_prop)).inter
    (MeasurableSet.iInter fun r ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun _ ↦ measurableSet_le
        (finiteGaussianBridgedPath_measurable T n M _) measurable_const)

end SRWTightness
