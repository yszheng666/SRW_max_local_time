import SRWTightness.SourceCommonLiteralMarkGeometry
import SRWTightness.SourceCommonPairProjectedChernoff
import SRWTightness.SourceTerminalThreshold

open MeasureTheory Filter

namespace SRWTightness

/-- The literal common-mark Chernoff estimate keeps the integer ceiling threshold and every tilt. -/
theorem source_common_literal_chernoff
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      (j : ℤ) = sourceSignedCommonPairLevel t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ W : ℝ, 0 < W → (2 / Real.pi) * sourceCommonPairRowScale t b w j * W < 1 →
      ∀ (u : ℝ) (k : ℕ), u ^ 2 / 2 = (k : ℝ) →
      let K := sourceCommonPairObservation b w
      (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k).real
        {Y | ∀ v : K, ((v : Site) = b ∨ (v : Site) = w) →
          sourceTerminalVisitCutoff t ≤ sumMarks K k Y v} ≤
        Real.exp (-(2 / Real.pi) * sourceTerminalHeight t ^ 2 * Real.log (1 + W) +
          sourceCommonPairIntensity t j * u ^ 2 * W /
            (1 - (2 / Real.pi) * sourceCommonPairRowScale t b w j * W)) := by
  filter_upwards [source_common_literal_mark_geometry] with t ht
  intro b w j hbw hj hd W hW hsmall u k hk
  have hg := ht b w j hbw hj hd
  dsimp only at hg ⊢
  let K := sourceCommonPairObservation b w
  have hp : 0 < Real.sqrt (normSq (w - b)) := by linarith [hg.1]
  have hpair : ({b, w} : Finset Site) ⊆ K := source_common_pair_observation_contains b w hp
  have hc := source_common_pair_projected_chernoff hOcc hRes t b w j hbw
    (2 * Real.sqrt (normSq (w - b))) hg.1 hg.2.1 hg.2.2.1 K hpair
    (Finset.Subset.refl _) hg.2.2.2.1 W hW.le hsmall u (sourceTerminalHeight t) k hk
  letI : IsProbabilityMeasure
      (markProductLaw (sourceCommonPairDomain t b j) K (sourceCommonPairIntensity t j) k) :=
    markProductLaw_isProbabilityMeasure _ _ _ hg.2.2.2.2.1 hg.2.2.2.2.2 k
  apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans hc
  intro Y hY v
  have hv : (v : Site) = b ∨ (v : Site) = w := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using v.property
  have hn := hY ⟨v, hpair v.property⟩ hv
  have hnR : (sourceTerminalVisitCutoff t : ℝ) ≤
      (sumMarks K k Y ⟨v, hpair v.property⟩ : ℝ) := by exact_mod_cast hn
  have hceil : (2 / Real.pi) * sourceTerminalHeight t ^ 2 / 2 ≤
      (sourceTerminalVisitCutoff t : ℝ) := by
    rw [sourceTerminalVisitCutoff_green_form]
    exact Nat.le_ceil _
  exact hceil.trans hnR

end SRWTightness
