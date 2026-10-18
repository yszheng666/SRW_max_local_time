import SRWTightness.SeparatedUnionExit
import SRWTightness.ExternalKilledTraceFactorization

open MeasureTheory
namespace SRWTightness

/-- The actual probability of a stopped direction word conditional on its prescribed exit. -/
noncomputable def killedWordBridgeProbability (C : Finset Site) (x e : Site) (w : PathWord) : ℝ :=
  pathLaw.real {ω | killedPathWord C x ω = w ∧ domainExitLocation C x ω = e} /
    traceExitProbability C x e

/-- Adjoining a one-step separated domain leaves the full stopped-word bridge law unchanged. -/
theorem separated_union_word_bridge (C E : Finset Site) (x e : Site) (hx : x ∈ C)
    (hgap : ∀ y ∈ domainExitBoundary C, y ∉ E) (w : PathWord) :
    killedWordBridgeProbability (C ∪ E) x e w = killedWordBridgeProbability C x e w := by
  have hw := separated_union_killedPathWord_ae C E x hx hgap
  have he : domainExitLocation (C ∪ E) x =ᵐ[pathLaw] domainExitLocation C x := by
    filter_upwards [hw] with ω hω
    rw [← killedPathWord_exitLocation (C ∪ E) x ω,
      ← killedPathWord_exitLocation C x ω, hω]
  have hj : pathLaw.real {ω | killedPathWord (C ∪ E) x ω = w ∧
      domainExitLocation (C ∪ E) x ω = e} =
      pathLaw.real {ω | killedPathWord C x ω = w ∧ domainExitLocation C x ω = e} := by
    apply measureReal_congr
    filter_upwards [hw, he] with ω hω hξ
    change (_ = w ∧ _ = e) = (_ = w ∧ _ = e)
    rw [hω, hξ]
  have hxprob : traceExitProbability (C ∪ E) x e = traceExitProbability C x e := by
    apply measureReal_congr
    filter_upwards [he] with ω hω
    change (_ = e) = (_ = e)
    rw [hω]
  unfold killedWordBridgeProbability
  rw [hj, hxprob]

end SRWTightness
