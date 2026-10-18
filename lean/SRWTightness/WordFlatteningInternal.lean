import SRWTightness.ChildWordFiniteRenewal
import SRWTightness.ChildWordTerminalRenewal
import SRWTightness.ChildWordNestedTerminal
import SRWTightness.ChildWordFirstTimes
import SRWTightness.ChildWordEmpty
import SRWTightness.ExternalWordFlattening

namespace SRWTightness

/-- Complete nested finite-word extraction preserves every ordered actual record. -/
theorem word_child_records_flatten_internal {M : Type*}
    (K C K' C' : Finset Site) (hKC : K ⊆ C) (hKC' : K' ⊆ C')
    (hK : K' ⊆ K) (hC : C' ⊆ C) (x : Site) (w : PathWord)
    (hend : x + position (wordPath w) w.length ∉ C) (F : Site → PathWord → M) :
    (wordChildRecords K C x (fun y u ↦ wordChildRecords K' C' y F u) w).flatten =
      wordChildRecords K' C' x F w := by
  classical
  have aux : ∀ N : ℕ, ∀ (x : Site) (w : PathWord), w.length = N →
      x + position (wordPath w) w.length ∉ C →
      (wordChildRecords K C x (fun y u ↦ wordChildRecords K' C' y F u) w).flatten =
        wordChildRecords K' C' x F w := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro x w hw hend
      by_cases hvisit : ∃ i < w.length, x + position (wordPath w) i ∈ K
      · obtain ⟨a, b, hab, hb, hpre, ha, hin, hout⟩ :=
          word_first_child_times K C hKC x w hend hvisit
        by_cases hbN : b < w.length
        · have hp := wordChildRecords_finite_renewal K C hKC x w
            (fun y u ↦ wordChildRecords K' C' y F u) a b hab hbN hpre ha hin hout
          have hc := wordChildRecords_nested_renewal K C K' C' hKC' hK hC x w F
            a b hab hbN hpre hout
          rw [hp, List.flatten_cons, hc]
          congr 1
          apply ih (w.length - (b + 1)) (by omega)
            (x + position (wordPath w) (b + 1))
            (slicePathWord w (b + 1) w.length) rfl
          change (x + position (wordPath w) (b + 1)) +
            position (wordPath (slicePathWord w (b + 1) w.length))
              (w.length - (b + 1)) ∉ C
          rw [slicePathWord_position w (b + 1) w.length _ le_rfl]
          rw [add_assoc, ← position_add, Nat.add_sub_of_le (by omega : b + 1 ≤ w.length)]
          exact hend
        · have he : b = w.length := by omega
          subst b
          rw [wordChildRecords_terminal_child K C x w
            (fun y u ↦ wordChildRecords K' C' y F u) a hab hpre ha hin hout]
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
          exact (wordChildRecords_nested_terminal K C K' C' hKC' hK hC x w F
            a hab hpre hout).symm
      · have hnone : ∀ i ≤ w.length, x + position (wordPath w) i ∉ K := by
          intro i hi hmem
          by_cases he : i = w.length
          · exact hend (he ▸ hKC hmem)
          · exact hvisit ⟨i, by omega, hmem⟩
        rw [wordChildRecords_no_visit K C x _ w hnone,
          wordChildRecords_no_visit K' C' x F w
            (fun i hi hmem ↦ hnone i hi (hK hmem)), List.flatten_nil]
  exact aux w.length x w rfl hend

/-- The deterministic two-level finite-word input is now proved internally. -/
theorem two_level_word_flattening_input_internal : TwoLevelWordFlatteningInput := by
  intro K C K' C' hKC hKC' hK hC x w hend
  exact word_child_records_flatten_internal K C K' C' hKC hKC' hK hC x w hend
    (fun z v ↦ (z, v))

end SRWTightness
