import SRWTightness.KilledBrownianDoobBesselPositivePathLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The constructed killed-Brownian Doob probability law is the actual Bessel whole-path law. -/
theorem killed_brownian_doob_bessel_path_law (hReflection : BridgeReflectionInput)
    (T x : ℝ) (hT : 0 < T) (hx : 0 < x) :
    (killedBrownianDoobCoefficientLaw T x).map
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ x - Real.sqrt T * gaussianDyadicPath ω (u / T)) =
    (independentBridgeLaw (Fin 3)).map
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ actualBesselThree T x u ω) := by
  classical
  let H := fun p : Set.Ioc (0 : ℝ) T → ℝ ↦ fun u : Set.Icc (0 : ℝ) T ↦
    if hu : 0 < (u : ℝ) then p ⟨u, hu, u.property.2⟩ else x
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro u
    dsimp [H]
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const
  let F := fun ω (u : Set.Ioc (0 : ℝ) T) ↦
    x - Real.sqrt T * gaussianDyadicPath ω (u / T)
  let G := fun ω (u : Set.Ioc (0 : ℝ) T) ↦ actualBesselThree T x u ω
  have hF : Measurable F := measurable_pi_lambda _ (fun _ ↦
    measurable_const.sub (measurable_const.mul (gaussianDyadicPath_measurable _)))
  have hG : Measurable G := measurable_pi_lambda _ (fun _ ↦
    actualBesselThree_measurable T x _)
  have heF : H ∘ F = fun ω (u : Set.Icc (0 : ℝ) T) ↦
      x - Real.sqrt T * gaussianDyadicPath ω (u / T) := by
    funext ω u
    dsimp [H, F, Function.comp_def]
    split_ifs with hu
    · rfl
    · have hu0 : (u : ℝ) = 0 := le_antisymm (le_of_not_gt hu) u.property.1
      simp [hu0, gaussianDyadicPath_zero]
  have heG : H ∘ G = fun ω (u : Set.Icc (0 : ℝ) T) ↦ actualBesselThree T x u ω := by
    funext ω u
    dsimp [H, G, Function.comp_def]
    split_ifs with hu
    · rfl
    · have hu0 : (u : ℝ) = 0 := le_antisymm (le_of_not_gt hu) u.property.1
      simp [hu0, actualBesselThree, gaussianDyadicPath_zero, Fin.sum_univ_succ,
        Real.sqrt_sq hx.le]
  have he := congrArg (fun ρ : Measure (Set.Ioc (0 : ℝ) T → ℝ) ↦ ρ.map H)
    (killed_brownian_doob_bessel_positive_path_law hReflection T x hT hx)
  change ((killedBrownianDoobCoefficientLaw T x).map F).map H =
    ((independentBridgeLaw (Fin 3)).map G).map H at he
  rw [Measure.map_map hH hF, Measure.map_map hH hG, heF, heG] at he
  exact he

end SRWTightness
