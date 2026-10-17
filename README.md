# Tightness of the maximum local time of planar simple random walk

LaTeX manuscript and a Lean 4 formalization of tightness and quantitative tail bounds for the maximum local time of planar simple random walk. The formalization proves the main claims **conditional on six explicitly stated literature interfaces**.

For the nearest-neighbor walk on $\mathbb Z^2$ started at the origin, let $M_n$ be the maximum number of visits to a site before step $n$. The main time theorem gives tightness of

$$
\sqrt{M_n}-\frac{\log n-\log\log n}{\sqrt\pi},\qquad n\ge3.
$$

The formalization also proves tightness at exit from disks, upper and lower tail bounds for the disk maximum, deterministic-time tail bounds, and the inclusive-time variant.

## Read the manuscript and inspect the formalization

- [Repository manuscript](SRW_max_local_time.tex), retaining the existing publication layout and updated AI/verification declaration.
- [Checksum-bound manuscript source](source/SRW_max_local_time.tex) and its [compiled PDF](output/pdf/SRW_max_local_time.pdf), including the formalization appendix.
- The repository manuscript and checksum-bound source have the same mathematical body; only publication front matter and the verification-status subsection differ. Run `python3 verify_manuscript_correspondence.py` to check this relationship.
- [Main Lean theorem](formalization/SRWTightness/SourceMainInternalReflection.lean): `SRWTightness.source_main_claims_internal_reflection`.
- [Exact target statements](formalization/SRWTightness/Targets.lean).
- [Source-to-Lean registry](obligations.json), linking each registered manuscript label to its status and Lean declarations.
- [Conditional certification](FINAL_CONDITIONAL_CERTIFICATION.md) and [manuscript alignment review](MANUSCRIPT_LEAN_ALIGNMENT_2026-10-17.md).

## Certification scope

The main theorem has the following conclusion:

```lean
DiskTightnessClaim ∧ DiskTailClaim ∧ TimeTightnessClaim ∧ TimeTailClaim ∧
  InclusiveTimeTightnessClaim
```

It retains these six literature input families as theorem hypotheses:

| Lean interface | Mathematical input |
| --- | --- |
| `PotentialKernelAsymptoticInput` | Fine asymptotics of the SRW potential kernel |
| `PositiveHarmonicRelativeInput` | Relative difference estimates for positive harmonic functions |
| `GWBarrierUpperInput` | Upper barrier estimate for the critical geometric Galton–Watson process |
| `∀ K k ι, RaicConvexCLTInput (MarkSamples K k) ι` | Finite-dimensional convex-set normal approximation, with the finite-type conditions retained |
| `GWBarrierLowerInput` | Lower barrier estimate for the critical geometric Galton–Watson process |
| `BDZDyadicSquareMaximumInput` | Maximum bound for the normalized DGFF on dyadic squares |

These are explicit propositions passed as parameters, rather than added Lean axioms. The exact statement, including its measurable-space typeclass parameters, is available in the main theorem file. The central upper-tail and positive-probability lower-bound propositions are derived internally.

All 189 non-section labels of the checksum-bound manuscript are registered:

| Registry status | Labels |
| --- | ---: |
| Internally certified | 98 |
| Conditionally certified | 89 |
| Explicit external inputs | 2 |
| Open | 0 |

The two external registry entries have source labels `eq:2.13` and `eq:3.4`. Source label names need not equal the displayed equation numbers in the revised PDF. These label counts measure registry coverage; they do not count independent assumptions or measure the proportion of mathematics proved internally. In particular, the six input families above are distinct from the two labels classified as external inputs.

The registry connects manuscript labels to Lean declarations. The targeted alignment revision incorporates the added terminal comparisons, quantitative root-return argument, and finite-time Bessel hitting route. Alternative derivations and remaining inputs are disclosed in the manuscript appendix. This correspondence is not a line-by-line Lean verification or an independent re-review of every sentence of the manuscript.

## Reproduce the checks

Pinned dependencies:

- Lean: `leanprover/lean4:v4.32.0`
- mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`
- Transitive dependency revisions: [lake-manifest.json](formalization/lake-manifest.json)

Install an `elan`-managed Lean toolchain, Python 3, and the `shasum` utility. From a fresh checkout, fetch the mathlib cache and run the full check from the repository root:

```sh
cd formalization
lake exe cache get
cd ..
./check.sh
```

Keep the committed toolchain and dependency manifest when reproducing this version. The initial dependency and cache download requires network access.

[`check.sh`](check.sh) first checks that the repository and checksum-bound manuscript bodies agree, then checks the manuscript checksum, builds the Lean root target, generates a fresh declaration-axiom audit, and runs [`verify_certificate.py`](verify_certificate.py). The verifier checks source-label coverage and uniqueness, registered line numbers and declaration bindings, exact audit coverage, and the local import closure of the root and audit modules. It rejects `sorry`, `admit`, custom `axiom`, and `native_decide` in that closure. Allowed logical axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.

The latest [full validation record](logs/manuscript-alignment-2026-10-17-check.log) completed successfully with 4,992 audit entries and 2,714 local modules in the checked import closure. The final status lines are:

```text
PASS: 189 source obligations; 98 internal, 89 conditional, 2 external, 0 open.
PASS: 4992 audit entries, 2714 rooted modules; standard axioms only.
```

This verifies the conditional Lean declarations and their registered source bindings. Assessing whether the explicit literature interfaces follow from the cited literature, and whether each informal passage matches its formal statement, remains a mathematical review task.
