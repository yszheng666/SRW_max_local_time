import SRWTightness.FiniteGaussianBridgedProcess
import SRWTightness.GaussianEndpointResidualInternal

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

theorem finiteGaussianBridgedPath_node (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < n, T j < T (j + 1)) (x : Fin n → ℝ)
    (ω : ℕ → GaussianCoefficientSpace) (j : Fin n) :
    finiteGaussianBridgedPath T n n x ω (T (j.val + 1)) = x j := by
  change bridgedGridPath T (fun k x ↦ finiteGaussianMesh n x k) n (x, ω) _ = _
  rw [bridgedGridPath_node T _ n (j.val + 1) hgap (by omega)]
  exact finiteGaussianMesh_succ n x j

/-- The entire interpolated path is independent of the two residual coordinates. -/
theorem finiteGaussianBridgedPath_independent (T : ℕ → ℝ) (n : ℕ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    IndepFun
      (fun p : ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) × (Fin 2 → ℝ) ↦
        fun v : ℝ ↦ finiteGaussianBridgedPath T n n p.1.1 p.1.2 v)
      Prod.snd
      (((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod
        (independentBridgeLaw ℕ)).prod (gaussianCoordinateLaw R)) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure (brownianTimeMatrix T n)
  letI := gaussianCoordinateLaw_isProbabilityMeasure R
  exact indepFun_prod (measurable_pi_lambda _
    (fun v ↦ finiteGaussianBridgedPath_measurable T n n v)) measurable_id

/-- The full compensated vector is realized by path nodes and independent residuals. -/
theorem finiteGaussianBridgedPath_pair_law (T : ℕ → ℝ) (n : ℕ) (last : Fin n)
    (hlast : last.val + 1 = n) (hT : T 0 = 0)
    (hgap : ∀ j < n, T j < T (j + 1)) (V : Matrix Bool Bool ℝ)
    (hV : V true false = V false true)
    (hR : (pairResidualMatrix (V false false) (V true true) (V false true) (T n)).PosDef) :
    gaussianCoordinateLaw
      (pairObservationCovarianceMatrix (fun j : Fin n ↦ T (j.val + 1)) (fun _ ↦ 0) V) =
      (((gaussianCoordinateLaw (brownianTimeMatrix T n)).prod
        (independentBridgeLaw ℕ)).prod
          (gaussianCoordinateLaw
            (pairResidualMatrix (V false false) (V true true) (V false true) (T n)))).map
        (fun p j ↦ match j with
          | Sum.inl a => finiteGaussianBridgedPath T n n p.1.1 p.1.2 (T (a.val + 1))
          | Sum.inr c => finiteGaussianBridgedPath T n n p.1.1 p.1.2 (T n) +
              p.2 (if c then 1 else 0)) := by
  let B := brownianTimeMatrix T n
  let R := pairResidualMatrix (V false false) (V true true) (V false true) (T n)
  let S := pairObservationCovarianceMatrix (fun j : Fin n ↦ T (j.val + 1)) (fun _ ↦ 0) V
  letI := gaussianCoordinateLaw_isProbabilityMeasure B
  letI := gaussianCoordinateLaw_isProbabilityMeasure R
  letI := gaussianCoordinateLaw_isProbabilityMeasure S
  have hquad (x : Fin n → ℝ) :
      0 ≤ ∑ j, ∑ l, x j * min (T (j.val + 1)) (T (l.val + 1)) * x l := by
    have hh := (brownianTimeMatrix_posSemidef_of_gaps T n hT
      (fun j hj ↦ (hgap j hj).le)).dotProduct_mulVec_nonneg x
    simpa only [brownianTimeMatrix, of_apply, dotProduct, Matrix.mulVec,
      Finset.mul_sum, star_trivial, mul_assoc] using hh
  have hLaw := gaussian_endpoint_residual_input_internal n last
    (fun j ↦ T (j.val + 1)) V
    (fun j ↦ by rw [hlast]; exact timeGridTime_mono T n hgap (by omega) le_rfl)
    hV hquad (by simpa only [hlast] using hR)
  have haux := pair_residual_auxiliary_law last (gaussianCoordinateLaw B)
    (gaussianCoordinateLaw R) (independentBridgeLaw ℕ) (gaussianCoordinateLaw S)
    (by
      rw [hlast] at hLaw
      convert hLaw using 1
      congr 1)
  have hh := congrArg (fun μ ↦ μ.map Prod.fst) haux
  have hm : Measurable
      (fun p : ((Fin n → ℝ) × (ℕ → GaussianCoefficientSpace)) × (Fin 2 → ℝ) ↦
        (pairResidualCoordinates last (p.1.1, p.2), p.1.2)) :=
    (((pairResidualCoordinates_measurable last).comp
      (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd)
  rw [Measure.map_fst_prod, Measure.map_map measurable_fst hm] at hh
  simp only [measure_univ, one_smul] at hh
  calc
    _ = _ := hh
    _ = _ := by
      congr 1
      funext p j
      cases j with
      | inl a =>
        exact (finiteGaussianBridgedPath_node T n hgap p.1.1 p.1.2 a).symm
      | inr c =>
        dsimp [Function.comp_def, pairResidualCoordinates]
        have hnode := finiteGaussianBridgedPath_node T n hgap p.1.1 p.1.2 last
        rw [hlast] at hnode
        rw [hnode]

end SRWTightness
