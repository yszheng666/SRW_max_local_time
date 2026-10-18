import SRWTightness.ExitLocation
import SRWTightness.KilledGreen

open MeasureTheory

namespace SRWTightness

/-- A finite SRW direction word, including its length. -/
structure PathWord where
  length : ℕ
  directions : Fin length → Direction

instance : Countable PathWord := by
  apply Function.Injective.countable (f := fun w : PathWord ↦ (⟨w.length, w.directions⟩ : Σ n : ℕ, Fin n → Direction))
  intro a b h
  cases a
  cases b
  cases h
  rfl
instance : MeasurableSpace PathWord := ⊤
instance : MeasurableSingletonClass PathWord := ⟨fun _ ↦ trivial⟩

/-- The actual increments up to and including the step that exits the domain. -/
noncomputable def killedPathWord (D : Finset Site) (x : Site) (ω : Sample) : PathWord :=
  ⟨domainSteps D x ω, fun k ↦ ω k⟩

/-- Extend a word after its endpoint; only its recorded prefix is used. -/
def wordPath (w : PathWord) : Sample := extendWord w.directions

theorem measurable_killedPathWord (D : Finset Site) (x : Site) :
    Measurable (killedPathWord D x) := by
  have hm : Measurable (fun p : Sample × ℕ ↦ (⟨p.2, fun k ↦ p.1 k⟩ : PathWord)) := by
    apply measurable_from_prod_countable_left
    intro n
    exact (measurable_of_countable (fun v : Fin n → Direction ↦ (⟨n, v⟩ : PathWord))).comp
      (measurable_pi_lambda _ (fun k ↦ measurable_pi_apply (k : ℕ)))
  exact hm.comp (measurable_id.prodMk (measurable_domainSteps D x))

theorem killedPathWord_position (D : Finset Site) (x : Site) (ω : Sample) (i : ℕ)
    (hi : i ≤ domainSteps D x ω) :
    position (wordPath (killedPathWord D x ω)) i = position ω i := by
  apply position_congr
  intro k hk
  simp [wordPath, killedPathWord, extendWord, hk.trans_le hi]

/-- The finite word retains exactly the half-open occupation counts of the killed walk. -/
theorem killedPathWord_localTime (D : Finset Site) (x y : Site) (ω : Sample) :
    localTime (wordPath (killedPathWord D x ω)) (killedPathWord D x ω).length (y - x) =
      domainLocalTime D x y ω := by
  unfold domainLocalTime
  apply localTime_congr
  intro k hk
  simp only [killedPathWord] at hk
  simp [wordPath, killedPathWord, extendWord, hk]

theorem killedPathWord_exitLocation (D : Finset Site) (x : Site) (ω : Sample) :
    x + position (wordPath (killedPathWord D x ω)) (killedPathWord D x ω).length =
      domainExitLocation D x ω := by
  exact congrArg (fun z ↦ x + z) (killedPathWord_position D x ω _ le_rfl)

/-- Every deterministic record extracted from this finite word is measurable. -/
theorem measurable_killed_word_record {M : Type*} [MeasurableSpace M]
    (D : Finset Site) (x : Site) (F : PathWord → M) :
    Measurable (fun ω ↦ F (killedPathWord D x ω)) :=
  (measurable_of_countable F).comp (measurable_killedPathWord D x)

end SRWTightness
