import SRWTightness.ChildVisitCoverage

namespace SRWTightness

/-- Strictly separated half-open intervals cannot cover the same time. -/
theorem separated_intervals_cover_unique (rs : List (ℕ × ℕ))
    (hs : rs.Pairwise (fun a b ↦ a.2 < b.1)) (j : ℕ)
    (a b : ℕ × ℕ) (ha : a ∈ rs) (hb : b ∈ rs)
    (haj : a.1 ≤ j ∧ j < a.2) (hbj : b.1 ≤ j ∧ j < b.2) : a = b := by
  induction rs with
  | nil => simp at ha
  | cons q rs ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hs
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      rcases List.mem_cons.mp hb with he | hb
      · exact he.symm
      · have hh := hhead b hb
        omega
    · rcases List.mem_cons.mp hb with he | hb
      · subst b
        have hh := hhead a ha
        omega
      · exact ih htail ha hb

/-- Every actual inner-set visit belongs to exactly one complete child interval. -/
theorem killedChildIntervals_unique_cover (D K C : Finset Site) (hKC : K ⊆ C) (hCD : C ⊆ D)
    (x : Site) (ω : Sample) (hfin : domainExit D x ω ≠ ⊤) (j : ℕ)
    (hj : j < domainSteps D x ω) (hvisit : x + position ω j ∈ K) :
    ∃! q : ℕ × ℕ, q ∈ killedChildIntervals D K C x ω ∧ q.1 ≤ j ∧ j < q.2 := by
  obtain ⟨q, hq, hc⟩ := killedChildIntervals_cover_visit D K C hKC hCD x ω hfin j hj hvisit
  refine ⟨q, ⟨hq, hc⟩, ?_⟩
  intro p hp
  exact separated_intervals_cover_unique _ (killedChildIntervals_separated D K C x ω)
    j p q hp.1 hq hp.2 hc

end SRWTightness
