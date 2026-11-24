# Extended Parallel Bodies and a Steiner Formula for Planar PL Sets

**Author:** Joseph T. Previdi 

**GitHub repository:** [Extended-Steiner-Formula](https://github.com/jprevidi/Extended-Steiner-Formula)

**Archived publication:** [10.5281/zenodo.24492788](https://doi.org/10.5281/zenodo.24492788)

## Overview

This repository contains the Lean 4 formalization accompanying the research manuscript *Extended Parallel Bodies and a Steiner Formula for Planar PL Sets*.

The principal result establishes that, for every nonempty closed planar PL set \(A\), there exists \(R>0\) such that, for all \(0<r<R\),

\[
\operatorname{Area}(E(A,r))
=
\operatorname{Area}(A)+2\mu_1(A)r+\pi\chi(A)r^2,
\]

where \(E(A,r)\) denotes the extended \(r\)-parallel body, \(\mu_1\) is the first intrinsic volume, and \(\chi\) is the Euler characteristic.

The extended parallel body consists of precisely those points \(x\) such that every closed radius-\(r\) ball containing \(x\) intersects the ordinary parallel body \(A_r\). Equivalently, it is the \(r\)-erosion of the ordinary \(2r\)-parallel body.

The proof proceeds through an explicit geometric characterization of the extended parallel body using arrowhead regions and an inductive simplicial deletion argument.

## Scope of Formalization

The principal formal theorem is:

```lean
FinitePlanarComplex.planarExtendedSteinerFormula
```

It is located in `SteinerProof/MainTheorem.lean`.

The formalization establishes the main extended Steiner formula for nonempty finite planar simplicial complexes, with the Steiner coefficients expressed through their simplicial definitions.

The theorem is established relative to the classical planar Steiner formulas, packaged as the explicit proposition `FinitePlanarComplex.OrdinaryPlanarSteiner`, defined in `SteinerProof/Background.lean`.

This proposition has two fields:

- `convexOffset`: the ordinary planar Steiner formula for nonempty convex realizations of finite planar simplicial complexes, expressed using the simplicial Steiner polynomial.
- `triangleOffset`: the ordinary planar Steiner formula for triangles, expressed in terms of area and perimeter.

These are explicit mathematical hypotheses of the principal theorem, rather than additional axioms introduced into Lean.

The subsequent extension to nonclosed PL sets and the general frontier-extension principle developed in the manuscript are not included in this formalization.

## Formal Verification

The complete Lean project has been successfully built.

The foundational dependencies of the principal theorem were inspected using:

```lean
#print axioms FinitePlanarComplex.planarExtendedSteinerFormula
```

The resulting output was:

```text
'FinitePlanarComplex.planarExtendedSteinerFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are standard foundational axioms of Lean. The principal theorem has no dependency on `sorryAx` or additional custom axioms.

The accompanying `Verification.txt` contains the recorded output of the theorem-statement inspection, the explicit background-hypothesis inspection, and the foundational axiom audit.

This file is provided for convenience and transparency. Independent verification should be performed directly from the Lean source code using the instructions below.

## Project Configuration

- Project name: `SteinerProof`
- Project version: `0.1.0`
- Lean toolchain: `leanprover/lean4:v4.37.0-rc1`
- Mathlib version: `v4.37.0-rc1`
- Default Lake build target: `SteinerProof`

The exact toolchain and dependency configuration are specified in `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

## Reproducing the Formal Verification

### Prerequisites

- Elan, the Lean toolchain manager.
- Git.
- An internet connection for retrieving the specified dependencies.
- Sufficient disk space and memory for Lean and Mathlib.

### Building the Project

Navigate to the root directory of the extracted project, containing `lean-toolchain` and `lakefile.toml`.

Retrieve the precompiled Mathlib dependencies:

```bash
lake exe cache get
```

Build the project:

```bash
lake build
```

Inspect the principal theorem, its mathematical hypotheses, and its foundational dependencies:

```bash
lake env lean SteinerProof/MainTheorem.lean
```

The inspection commands are included at the end of `MainTheorem.lean`.

Successful execution should reproduce the theorem statement, background hypotheses, and foundational axiom dependencies documented in `Verification.txt`.

For machines with limited available memory, compilation may be performed outside an integrated development environment and with reduced parallelism.

On Windows PowerShell:

```powershell
$env:LEAN_NUM_THREADS = "1"
lake build
```

On Linux or macOS:

```bash
LEAN_NUM_THREADS=1 lake build
```

No graphical development environment is required.

## Library Organization

The library consists of 32 Lean modules in the `SteinerProof/` directory, together with the root library file `SteinerProof.lean`.

Selected principal modules include:

| File | Subject |
|---|---|
| `Basic.lean` | Basic definitions |
| `PLComplex.lean` | Finite planar simplicial complexes |
| `Background.lean` | Classical planar Steiner background hypotheses |
| `ExtendedBody.lean` | Extended parallel bodies |
| `AdmissibleRadius.lean` | Admissible radius |
| `Separation.lean` | Geometric separation |
| `ArrowheadGeometry.lean` | Arrowhead geometry |
| `ArrowheadLocalization.lean` | Localization of arrowheads |
| `ArrowheadRecognition.lean` | Recognition of arrowheads |
| `ArrowheadExterior.lean` | Exterior arrowhead geometry |
| `ArrowheadChanges.lean` | Changes in arrowhead regions |
| `HullRefinement.lean` | Convex hull refinement |
| `HullFilling.lean` | Convex hull filling |
| `VertexDeletion.lean` | Vertex deletion |
| `EdgeDeletion.lean` | Edge deletion |
| `TriangleDeletion.lean` | Triangle deletion |
| `SimplexValuation.lean` | Simplicial valuation identities |
| `RealizationBridge.lean` | Realization-level results |
| `MainTheorem.lean` | Principal extended Steiner theorem |

## Repository Contents

- `SteinerProof/` — the 32 Lean source modules.
- `SteinerProof.lean` — root library file.
- `lean-toolchain` — Lean toolchain specification.
- `lakefile.toml` — Lake project configuration.
- `lake-manifest.json` — pinned dependency revisions.
- `Verification.txt` — recorded theorem statement, background hypotheses, and foundational axiom audit.
- `README.md` — project documentation and reproduction instructions.

The research manuscript is available through the associated Zenodo publication.

Downloaded dependencies and generated compilation artifacts are intentionally excluded from the archived source project. They can be reconstructed using the included project configuration.

## Research Status

This work is publicly released as a research preprint with an accompanying machine-checkable formalization of its principal theorem.

The manuscript has not yet undergone peer review.

## Citation

When referencing this work, please cite the corresponding version of the research manuscript and its associated formalization using the Zenodo DOI provided above.
