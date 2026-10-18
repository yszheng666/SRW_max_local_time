# Geometric GW interface audit

Reference checked: Jay Rosen, arXiv:2203.14394v1, Theorem 9.1, PDF page 46
(https://arxiv.org/pdf/2203.14394v1). This is the version named by the manuscript.

The upper input retains fixed delta, curvature, eta and epsilon, positive length,
positive initial population, both state ranges, endpoint margins and the closed
terminal interval. Its multiplier uses sqrt(x/(y*L)). The lower input additionally
retains the margin-product bound, the max(x*y,abs(y-x)) condition, a positive
lattice state in the terminal interval and every interior tube section, and the
minimum of that square-root multiplier with one. The interface restricts the
lower curvature constant to Ctilde>C; the manuscript uses Ctilde=10 and C=1.
The omitted-barrier extension is not imported.

Local construction: geometricGWOffspringLaw uses mathlib geometricMeasure at 1/2.
A generation is the sum of k independent offspring. The finite record law starts
at [k] and recursively binds fresh generations, storing newest first. Height
reads the reversed record. Probability normalization is proved internally.

GWBarrierUpperInput and GWBarrierLowerInput are explicit Prop parameters, not
proved declarations or global proof instances. This checkpoint does not discharge
the source tube, lattice, scale, endpoint or record-comparison obligations, and
must not mark (7.24) or the full one-point theorem certified.


Internal application progress (2026-09-30): terminal closed subwindow lattice existence
and containment in the half-open source window are verified for actual source deficits.
Interior curvature gap >=9 and an ordered-lines lattice lemma are verified. Actual source
scales prove upper tube height >=4 for matching natural generation lengths. Endpoint
margin ordering, tube containment, full parameter verification and probability transfer
are still pending. These are partial application results, not certification of (7.24).


Latest application gate: source_gw_actual_lower_tube_probability uses the actual
natural horizon and retains only GWBarrierLowerInput. All source-specific hypotheses
of that input are internally discharged by source_gw_lower_conditions. The remaining
work is event/probability transfer to the complete coarse event (including the final
layer), scalar prefactor/exponential comparison and the upper estimate. The generic
source tube upper-curve containment is proved. This supersedes earlier parameter gaps.


Complete coarse-event transfer gate: the event contains all layers 1..N_R and the
half-open [u,u+1) window. The lower tube inclusion handles the final layer explicitly.
The upper inclusion enlarges to the closed window and positive-curvature barrier.
Both probability bounds now hold on the actual geometricGWRecordLaw 1 N_R. Remaining
work for (7.24) is scalar prefactor and exponent comparison; original-walk record transfer
remains a separate obligation. This supersedes the previous event-transfer gap.


Final (7.24) correspondence gate: source_gw_coarse_probability chooses positive c,C
before the eventual t threshold and covers every q in [sqrt(d),2sqrt(d)]. The actual
floor-defined generation is converted to a positive natural horizon internally. Its
record event tests all layers 1..N_R, uses the actual total time and slope, and has the
source half-open terminal window. The probability weight is exactly
(1+q)/N_R^2 * exp(-u^2/(2N_R)). Both scalar comparisons are internally proved.
Only the two explicit GW inputs remain. Therefore (7.24) is conditionally certified;
marked reference integration and original-walk record transfer remain uncertified.
