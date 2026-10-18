import SRWTightness.TraceExitCompetingDecomposition
import SRWTightness.TraceStopFirstStepInternal
import SRWTightness.TraceStopExitFirstStepInternal

namespace SRWTightness

/-- All three original actual killed-exit decomposition identities are internally proved. -/
theorem killed_exit_decomposition_input_internal : KilledExitDecompositionInput := by
  refine ⟨trace_exit_competing_decomposition_internal, ?_, ?_⟩
  · exact trace_stop_probability_first_step_internal
  · intro D K hKD x hx e he
    exact trace_stop_exit_probability_first_step_internal D K hKD x e hx he

end SRWTightness
