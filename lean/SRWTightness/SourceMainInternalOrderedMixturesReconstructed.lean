import SRWTightness.SourceMainInternalOrderedMixtures
import SRWTightness.SourceDiskSeedReconstructed

open Filter MeasureTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_main_claims_internal_ordered_mixtures_reconstructed [MeasurableSpace (List
    WordMark)]
    [MeasurableSingletonClass (List WordMark)]
    (hLast : FiniteLastVisitCountInput)
    (hrec : FiniteRootCompletionInput) (hMarginal : GeometricGWOneRootMarginalInput)
    (hExt : ExteriorBridgeFactorizationInput)
    (hErase : ExteriorNestedCountInvarianceInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) (hExit : FiniteKilledWalkMomentInput)
    (hGW : GWBarrierUpperInput)

    (hBE : ∀ (K : Finset Site) (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι],
      RaicConvexCLTInput (MarkSamples K k) ι)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput)
    (hLower : GWBarrierLowerInput)
    (hSum : SeparatedStretchedExponentialSumInput)
    (hBound : QuadraticStretchedExponentialBoundInput)
    (hKernel : FiniteGaussianBridgeKernelInput) (hEndpoint : GaussianEndpointResidualInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)


    (hBDZ : BDZDyadicSquareMaximumInput) (hSup : PlanarGaussianIncrementSupInput)


    (hGreen : BufferedSquareGreenInput)
    (hEmbed : BufferedDyadicInteriorDiskEmbeddingInput)
    (hTranslation : ProjectedMarkTranslationInput) :
    DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
      InclusiveTimeTightnessClaim := by
  have hJoint : MarkedGWJointInput WordMark := marked_gw_joint_input_internal
  have hAllForest : ∀ (K : Finset Site) [MeasurableSpace (List (Mark K))]
      [MeasurableSingletonClass (List (Mark K))], MarkedGWForestJointInput (Mark K) := by
    intro K inst₁ inst₂
    exact marked_gw_forest_joint_input_internal
  have hAllMix : ∀ (α β : Type) [MeasurableSpace α] [MeasurableSpace β]
      [MeasurableSingletonClass α] [MeasurableSingletonClass β] [Countable α] [Countable β]
      [MeasurableSpace (List α)] [MeasurableSpace (List β)]
      [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)],
      OrderedForestMixtureInput α β := by
    intro α β inst₁ inst₂ inst₃ inst₄ inst₅ inst₆ inst₇ inst₈ inst₉ inst₁₀
    exact ordered_forest_mixture_input_internal α β
  have hTree : ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceUpperBlockCenters t,
      MarkedGWTreeInput (Mark (sourceUpperBlock t b)) := by
    apply Eventually.of_forall
    intro t b hb
    letI : MeasurableSpace (List (Mark (sourceUpperBlock t b))) := ⊤
    letI : MeasurableSingletonClass (List (Mark (sourceUpperBlock t b))) :=
      ⟨fun _ ↦ trivial⟩
    exact markedGWJoint_population (hAllForest (sourceUpperBlock t b)).singleRoot
  have hu := source_disk_upper_tail_claim two_level_word_flattening_input_internal hP
    finite_gaussian_regression_input_internal hBDZ hSup
    positive_convolution_input_internal
    sub_gaussian_positive_moment_input_internal gaussian_positive_convolution_input_internal
    gaussian_mills_input_internal
    weighted_gaussian_integral_input_internal hGreen hEmbed
    exponential_floor_scale_input
    lattice_disk_count_input_internal
    hTranslation hGW hTree
    (Eventually.of_forall (fun t b _ ↦ hAllForest (sourceUpperBlock t b)))
  have hs := source_disk_seed_claim_reconstructed lattice_disk_count_input_internal
    lattice_annulus_count_input_internal hLast hrec hMarginal
    hJoint hExt two_level_word_flattening_input_internal hErase hR hP hH hM hT hExit hGW
    hBE hGaussian hReflection
    hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement hLower hSum hBound hKernel
    hEndpoint hOcc hRes hAllForest hAllMix
  exact mainClaims_of_spatial_inputs hu hs

end SRWTightness
