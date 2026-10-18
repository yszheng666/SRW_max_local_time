import SRWTightness.FiniteKilledChainWordSum
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Finite site lists carry the discrete measurable structure in the killed-path construction. -/
local instance finiteChainListMeasurableSpace {α : Type*} : MeasurableSpace (List α) := ⊤

/-- Single finite words are measurable in that discrete structure. -/
local instance finiteChainListMeasurableSingleton {α : Type*} :
    MeasurableSingletonClass (List α) := ⟨fun _ ↦ trivial⟩

/-- The finite killed-path law assigns every complete path its actual transition product. -/
noncomputable def finiteChainKilledWordLaw {σ : Type*} [MeasurableSpace σ]
    (P : σ → σ → ℝ≥0∞) (D : Set σ) (x : σ) :
    Measure (List D × {y : σ // y ∉ D}) :=
  Measure.sum (fun q : List D × {y : σ // y ∉ D} ↦
    chainWordWeight P Subtype.val x q.1 q.2.val • Measure.dirac q)

/-- This law gives every individual complete path exactly its transition-product mass. -/
theorem finiteChainKilledWordLaw_singleton {σ : Type*} [MeasurableSpace σ]
    [MeasurableSingletonClass σ] (P : σ → σ → ℝ≥0∞) (D : Set σ) (x : σ)
    (q : List D × {y : σ // y ∉ D}) :
    finiteChainKilledWordLaw P D x {q} = chainWordWeight P Subtype.val x q.1 q.2.val :=
  Measure.sum_smul_dirac_singleton

/-- The law of complete killed paths is a subprobability measure, including possible
nontermination. -/
theorem finiteChainKilledWordLaw_univ_le_one {σ : Type*} [MeasurableSpace σ]
    (P : σ → σ → ℝ≥0∞) (D : Set σ) (hP : ∀ x, ∑' y, P x y ≤ 1) (x : σ) :
    finiteChainKilledWordLaw P D x Set.univ ≤ 1 := by
  rw [finiteChainKilledWordLaw, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  exact finiteChainExitMass_sum_le_one P D hP x

/-- The prescribed exit event has precisely the sum over all internal finite paths. -/
theorem finiteChainKilledWordLaw_exit {σ : Type*} [MeasurableSpace σ]
    [MeasurableSingletonClass σ] [Countable σ]
    (P : σ → σ → ℝ≥0∞) (D : Set σ) (x : σ) (e : {y : σ // y ∉ D}) :
    finiteChainKilledWordLaw P D x {q | q.2 = e} = finiteChainExitMass P D x e.val := by
  classical
  rw [finiteChainKilledWordLaw, Measure.sum_apply _ (Set.to_countable _).measurableSet]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply,
    Set.mem_setOf_eq, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [ENNReal.tsum_prod']
  simp only [tsum_ite_eq, finiteChainExitMass]

end SRWTightness
