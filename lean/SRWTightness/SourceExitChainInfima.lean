import SRWTightness.SourcePointTraversalInfima
import SRWTightness.ChainGeometry

open MeasureTheory

namespace SRWTightness

/-- An eligible endpoint with no earlier eligible time is the exact first hitting time. -/
theorem sourceFirstHit_eq_of_first (P : ℕ → Prop) (a b : ℕ) (hab : a ≤ b) (hb : P b)
    (hbefore : ∀ j, a ≤ j → j < b → ¬ P j) : sourceFirstHit P a = b := by
  apply le_antisymm
  · exact (sourceFirstHit_le_iff P a b).mpr
      ⟨b, WithTop.coe_le_coe.mpr hab, le_rfl, hb⟩
  · rw [sourceFirstHit_eq_sInf]
    apply le_sInf
    rintro t ⟨j, ⟨haj, hpj⟩, rfl⟩
    exact WithTop.coe_le_coe.mpr (not_lt.mp
      (fun hjb ↦ hbefore j (WithTop.coe_le_coe.mp haj) hjb hpj))

/-- The exit of a shifted walk is the original path's first exit from its current-position disk. -/
theorem source_shifted_exit_firstHit (R : ℝ) (hR : 0 < R) (a : ℕ) (ω : Sample)
    (hfin : exitTime R (shift a ω) ≠ ⊤) :
    sourceFirstHit (fun n ↦ R ≤ Real.sqrt (normSq (position ω n - position ω a))) a =
      (↑(a + exitSteps R (shift a ω)) : WithTop ℕ) := by
  have hpos (n : ℕ) (han : a ≤ n) :
      position ω n - position ω a = position (shift a ω) (n - a) := by
    have h := position_add ω a (n - a)
    rw [Nat.add_sub_of_le han] at h
    rw [h, add_sub_cancel_left]
  apply sourceFirstHit_eq_of_first _ a _ (by omega)
  · rw [hpos _ (by omega), Nat.add_sub_cancel_left]
    apply not_lt.mp
    intro hlt
    have hin := (source_disk_region_iff R hR _).mpr hlt
    have hout := normSq_at_exit_ge R (shift a ω) _ (coe_exitSteps R _ hfin).symm
    exact not_lt_of_ge hout hin
  · intro j haj hjb hdist
    rw [hpos j haj] at hdist
    have hj : j - a < exitSteps R (shift a ω) := by omega
    have he : ((j - a : ℕ) : WithTop ℕ) < exitTime R (shift a ω) := by
      rw [← coe_exitSteps R _ hfin]
      exact WithTop.coe_lt_coe.mpr hj
    have hin := (source_disk_region_iff R hR _).mp (before_exit_mem R (shift a ω) _ he)
    exact not_lt_of_ge hdist hin

/-- Source (10.1): on one almost-sure set every recursive translated exit is the literal infimum. -/
theorem source_exit_chain_infima (R : ℝ) (hR : 0 < R) :
    ∀ᵐ ω ∂pathLaw, exitChain R 0 ω = 0 ∧ ∀ i : ℕ,
      exitChain R (i + 1) ω = sInf ((fun n : ℕ ↦ (n : WithTop ℕ)) ''
        {n | exitChain R i ω ≤ n ∧
          R ≤ Real.sqrt (normSq (position ω n - position ω (chainSteps R i ω)))}) := by
  filter_upwards [ae_all_iff.mpr (exitChain_ne_top_ae hR.le)] with ω hfin
  refine ⟨rfl, ?_⟩
  intro i
  have he : exitTime R (shift (chainSteps R i ω) ω) ≠ ⊤ :=
    (WithTop.add_ne_top.mp (hfin (i + 1))).2
  have hh := source_shifted_exit_firstHit R hR (chainSteps R i ω) ω he
  rw [sourceFirstHit_eq_sInf] at hh
  rw [← coe_chainSteps R i ω (hfin i), hh]
  rw [← chainSteps_succ R i ω (hfin (i + 1)), coe_chainSteps R (i + 1) ω (hfin (i + 1))]

end SRWTightness
