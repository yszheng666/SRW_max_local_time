import SRWTightness.ExternalStoppedWordMass
import SRWTightness.ChildFirstExit

namespace SRWTightness

/-- Replaying an admissible exit word exits at exactly its recorded length. -/
theorem admissibleExitWord_domainSteps (C : Finset Site) (x e : Site) (w : PathWord)
    (hw : AdmissibleExitWord C x e w) :
    domainExit C x (wordPath w) ≠ ⊤ ∧ domainSteps C x (wordPath w) = w.length := by
  have hout : x + position (wordPath w) w.length ∉ C := by rw [hw.2.1]; exact hw.2.2
  have he := (domainExit_le_iff C x (wordPath w) w.length).mpr ⟨_, le_rfl, hout⟩
  have hf : domainExit C x (wordPath w) ≠ ⊤ := ne_top_of_le_ne_top (by simp) he
  rw [← coe_domainSteps C x (wordPath w) hf] at he
  have hle := WithTop.coe_le_coe.mp he
  refine ⟨hf, Nat.le_antisymm hle ?_⟩
  by_contra hn
  have ht : domainSteps C x (wordPath w) < w.length := by omega
  exact position_domain_exit_not_mem C x (wordPath w) hf (hw.1 _ ht)

/-- Replaying a genuine exit word and stopping again preserves every recorded increment. -/
theorem admissibleExitWord_killedPathWord (C : Finset Site) (x e : Site) (w : PathWord)
    (hw : AdmissibleExitWord C x e w) : killedPathWord C x (wordPath w) = w := by
  have he := (admissibleExitWord_domainSteps C x e w hw).2
  cases w with
  | mk n f =>
    simp only [killedPathWord]
    congr 1
    apply (Fin.heq_fun_iff he).mpr
    intro k
    have hk : (k : ℕ) < n := lt_of_lt_of_le k.isLt he.le
    simp [wordPath, extendWord, hk]

end SRWTightness
