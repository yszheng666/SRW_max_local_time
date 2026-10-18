import SRWTightness.SourceSingleRootVisits
import SRWTightness.TerminalListVisitSum
import SRWTightness.EquilibriumObservationMatrix

open scoped BigOperators

namespace SRWTightness

/-- Original local-time observations, with the manuscript centering and equilibrium averages. -/
noncomputable def domainLocalObservation {q : ℕ} (Dref K : Finset Site)
    (family : Fin q → Finset Site) (z : K) (D : Finset Site) (x : Site) (ω : Sample)
    (k : ℕ) (α g u : ℝ) : Option (Fin q) → ℝ
  | none => ((domainLocalTime D x z ω : ℝ) - α * k) / (u * Real.sqrt (α * g))
  | some i => ∑ y : K, equilibriumWeight Dref (family i) y *
      (((domainLocalTime D x y ω : ℝ) - α * k) / (u * Real.sqrt (α * g)))

/-- Every source terminal observation agrees with the original walk observation on a single root. -/
theorem source_single_root_normalized_observation (m ρ : ℝ) (n : ℕ) (b : Site)
    (D K : Finset Site) (x : Site) (hρ : 0 ≤ ρ)
    (hm : sourceRecordBuffer ρ + 2 ≤ m)
    (hK : K ⊆ translateFinset b (diskFinset (m - sourceRecordBuffer ρ - 2)))
    (hroot : sourceExitDomain m ρ (n + 1) b 0 ⊆ D)
    (ω : Sample) (hfin : domainExit D x ω ≠ ⊤)
    (r : FiniteExcursionRecord (Mark K) n)
    (hr : killedChildRecords D (sourceEntranceDomain m ρ (n + 1) b 0)
      (sourceExitDomain m ρ (n + 1) b 0) x
      (actualFiniteWordRecord (sourceTreeEntrance m ρ (n + 1) b)
        (sourceTreeExit m ρ (n + 1) b) (wordOccupationMark K) n) ω = [r])
    {q : ℕ} (Dref : Finset Site) (family : Fin q → Finset Site) (z : K)
    (α g u : ℝ) (i : Option (Fin q)) :
    let k := geometricGWPopulation (finiteRecordPopulationList n r) n
    normalizedObservation Dref K family z k α g u i
      (terminalListSamples 0 k (finiteRecordLeaves n r)) =
      domainLocalObservation Dref K family z D x ω k α g u i := by
  dsimp only
  let k := geometricGWPopulation (finiteRecordPopulationList n r) n
  have hv (y : K) :
      (∑ j : Fin k, (terminalListSamples 0 k (finiteRecordLeaves n r) j y : ℝ)) =
        (domainLocalTime D x y ω : ℝ) := by
    rw [terminal_tree_visit_sum K n r y,
      source_single_root_mark_visits m ρ n b D K x hρ hm hK hroot ω hfin r hr y]
  have hn (y : K) : normalizedMarkSum K k α g u y
      (terminalListSamples 0 k (finiteRecordLeaves n r)) =
        ((domainLocalTime D x y ω : ℝ) - α * k) / (u * Real.sqrt (α * g)) := by
    unfold normalizedMarkSum
    rw [hv]
  cases i with
  | none => exact hn z
  | some j =>
    simp only [normalizedObservation, normalizedEquilibriumAverage,
      normalizedWeightedSum, domainLocalObservation]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hn]

end SRWTightness
