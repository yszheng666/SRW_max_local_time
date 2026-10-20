# Tightness of the maximum local time of planar simple random walk

**Xinyi Li** — Beijing International Center for Mathematical Research, Peking University (xinyili@bicmr.pku.edu.cn).

**Yushu Zheng** — School of Mathematics, Shanghai University of Finance and Economics (zhengyushu@sufe.edu.cn).

LaTeX manuscript on tightness and quantitative tail bounds for the maximum local time of planar simple random walk.

For the maximum visit count $M_n$ before step $n$, the main theorem gives tightness of

$$
\sqrt{M_n}-\frac{\log n-\log\log n}{\sqrt\pi},\qquad n\ge3.
$$

## Manuscript

- [LaTeX manuscript](SRW_max_local_time.tex): the main file for Overleaf or a local LaTeX compiler.
- [PDF of the checksum-bound manuscript](output/pdf/SRW_max_local_time.pdf): the archived verification copy, with a different publication layout.

## Current status

The current manuscript and accompanying conditional Lean 4 formalization are available in this repository. Further polishing of the manuscript and its exposition is planned.

Generative AI tools were used to explore proof strategies, generate the mathematical proof draft, prepare the manuscript, and develop the accompanying Lean formalization. The authors take responsibility for the mathematical content, its verification, and its exposition. The formalization retains six explicit literature input families; it does not constitute an independent human verification of every argument in the manuscript.

## Lean verification

All Lean files and verification materials are grouped in **[lean/](lean/)**.

- [Lean guide, assumptions and reproduction instructions](lean/README.md)
- [Main formal theorem](lean/SRWTightness/SourceMainLiteratureInputs.lean)
- [October 18 literature-interface bridges](lean/LITERATURE_INTERFACE_BRIDGES_2026-10-18.md)
- [Exact target statements](lean/SRWTightness/Targets.lean)
- [Source-to-Lean registry](lean/obligations.json)

The formalization is conditional on six explicit literature input families. Its certificate covers 189 manuscript labels; these coverage counts are not a percentage of mathematics proved without external inputs. See the [detailed scope](lean/README.md#certification-scope).

To reproduce the checks with the pinned Lean toolchain:

```sh
cd lean
lake exe cache get
./check.sh
```

Technical paths in the archived certification reports are relative to `lean/`. The checksum-bound manuscript and its manifest are in [lean/source/](lean/source/).
