import SRWTightness.SourceLongFineRecord
import SRWTightness.SourceLongEscapeRadii
import SRWTightness.ExternalExteriorBridge

namespace SRWTightness

/-- A long segment keeps its site label and its complete ordered fine forest. -/
abbrev SourceExteriorFineValue (t : ℝ) (K₀ K₁ : Finset Site) (ν : ℕ) :=
  Sum (List (FiniteExcursionRecord (Mark K₀)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))
    (List (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))

/-- Fine records extracted from the component chosen by the actual exterior label. -/
noncomputable def sourceExteriorFineRecord (t : ℝ) (b w : Site) (K₀ K₁ : Finset Site)
    (ν : ℕ) (s : ExteriorSlot) (u : PathWord) : SourceExteriorFineValue t K₀ K₁ ν :=
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  if s.2.1 then Sum.inr (wordChildRecords (sourceEntranceDomain m 1 ℓ w ν)
    (sourceExitDomain m 1 ℓ w ν) s.2.2.1 (sourceLongFineRecord t w K₁ ν) u)
  else Sum.inl (wordChildRecords (sourceEntranceDomain m 1 ℓ b ν)
    (sourceExitDomain m 1 ℓ b ν) s.2.2.1 (sourceLongFineRecord t b K₀ ν) u)

/-- The long-segment reference weight, with no empty-root atom. -/
noncomputable def sourceLongFineListWeight (t : ℝ) (b : Site) (K : Finset Site) (ν J : ℕ)
    (rs : List (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))) : ℝ :=
  match rs with
  | [] => 0
  | r :: tail => sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J *
      (1 - sourceLongEscapeParameter (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J) ^ tail.length *
      ((r :: tail).map (sourceLongFineReferenceMass t b K ν)).prod

/-- The full local logarithmic error, including each retained root's fine error. -/
noncomputable def sourceLongFineListError (A C B W t a : ℝ) (K : Finset Site) (ν J : ℕ)
    (rs : List (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))) : ℝ :=
  A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
    C * 15 / (sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) (ν + 1) - 14) * (rs.length : ℝ) +
    (rs.map (sourceLongFineError B W t a K ν)).sum

/-- The reference weight reads the same site tag as the recorded fine forest. -/
noncomputable def sourceExteriorFineWeight (t : ℝ) (b w : Site) (K₀ K₁ : Finset Site)
    (ν J : ℕ) (r : SourceExteriorFineValue t K₀ K₁ ν) : ℝ :=
  r.elim (sourceLongFineListWeight t b K₀ ν J) (sourceLongFineListWeight t w K₁ ν J)

/-- The selected full error is a function of the tagged record itself. -/
noncomputable def sourceExteriorFineError (A C B W t a₀ a₁ : ℝ) (K₀ K₁ : Finset Site)
    (ν J : ℕ) (r : SourceExteriorFineValue t K₀ K₁ ν) : ℝ :=
  r.elim (sourceLongFineListError A C B W t a₀ K₀ ν J)
    (sourceLongFineListError A C B W t a₁ K₁ ν J)

/-- A permitted local record agrees with its exterior label and contains at least one root. -/
def sourceExteriorFineCompatible (t : ℝ) (K₀ K₁ : Finset Site) (ν : ℕ)
    (s : ExteriorSlot) (r : SourceExteriorFineValue t K₀ K₁ ν) : Prop :=
  r.elim (fun rs ↦ s.2.1 = false ∧ rs ≠ []) (fun rs ↦ s.2.1 = true ∧ rs ≠ [])

end SRWTightness
