# Lean 4 formalization: *How Curved Must an SVM Be? Exact Conic Laws, Moment Certificates, and Lean-Verified Minimum-Degree Separation of Planar Data*

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23609222.svg)](https://doi.org/10.5281/zenodo.23609222)

This repository contains the complete Lean 4 / Mathlib formalization accompanying

> S. A. Sheikh,
> *How Curved Must an SVM Be? Exact Conic Laws, Moment Certificates, and Lean-Verified Minimum-Degree Separation of Planar Data* (2026).

The whole development is a single file, [`PlanarSVM.lean`](PlanarSVM.lean) (about 2,600 lines, namespace `PlanarSep`). It contains **no `sorry` and no `axiom` declarations**, and no external results are taken as hypotheses.

## What is formalized

The file studies the **algebraic separation degree** `d_*(A,B)` of two planar point sets: the least total degree of a real bivariate polynomial that is positive on `A` and negative on `B`. This is equivalently the least degree of a polynomial-kernel hard-margin SVM that separates them. It proves:

- **Section 2:** existence of polynomial separators for disjoint compact classes, Lagrange interpolation, class-size bounds, the singleton dichotomy, and smooth minimum-degree separators
- **Section 3:** the Veronese convex-hull criterion, the linear case, moment certificates of non-separability, and their sparse form
- **Section 4:** exact separation-degree laws for labelled points on lines, circles, ellipses, parabolas and hyperbolas (including affine images), alternating labels on circles, and the rational-curve lower bound
- **Section 5:** affine invariance, generic interpolation and shattering, and local stability of the upper bound
- **Section 7 and Appendix A:** the unit-margin reformulation, the kernel identity, and the equivalence of `d_*` with the minimum feasible polynomial-kernel SVM degree
- **Table 1:** the XOR configuration

[`VERIFICATION.md`](VERIFICATION.md) maps each numbered result of the paper to its Lean theorem name.

## Building

Requirements: [Lean 4](https://lean-lang.org/) via `elan`. The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.28.0`), and Mathlib is pinned to `v4.28.0` in `lakefile.toml`.

```bash
git clone https://github.com/sajadcosmos/Planar-Exact_SVM.git
cd Planar-Exact_SVM
lake update          # resolves Mathlib
lake exe cache get   # downloads precompiled Mathlib
lake build
```

A successful `lake build` with no errors confirms that every proof checks.

An automated build (GitHub Actions, see the **Actions** tab) runs on every change. It compiles the file and prints the axioms of the main theorems, failing if any of them depends on `sorry`.

## Files

| File | Purpose |
|---|---|
| `PlanarSVM.lean` | The complete formalization |
| `VERIFICATION.md` | Map from the paper's numbered results to Lean theorem names |
| `lakefile.toml` | Lake build configuration (Mathlib dependency) |
| `lean-toolchain` | Pinned Lean version |
| `CITATION.cff` | Citation metadata (powers GitHub's "Cite this repository" button) |
| `.github/workflows/lean.yml` | Automated build and axiom check |

## How to cite

If you use this formalization, please cite it as:

> S. A. Sheikh, *Lean 4 formalization of "How Curved Must an SVM Be? Exact Conic Laws, Moment Certificates, and Lean-Verified Minimum-Degree Separation of Planar Data,"* version 1.0, Zenodo (2026), doi:[10.5281/zenodo.23609222](https://doi.org/10.5281/zenodo.23609222).

BibTeX:

```bibtex
@software{sheikh_planar_svm_lean_2026,
  author    = {Sheikh, Sajad Ahmad},
  title     = {Lean 4 formalization of ``How Curved Must an SVM Be? Exact Conic Laws, Moment Certificates, and Lean-Verified Minimum-Degree Separation of Planar Data''},
  version   = {1.0},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.23609222},
  url       = {https://doi.org/10.5281/zenodo.23609222}
}
```

## Contact

Sajad Ahmad Sheikh, Department of Mathematics, University of Kashmir, South Campus, Anantnag, 192101, Jammu and Kashmir, India
sajadsheikh@uok.edu.in

## License

See [`LICENSE`](LICENSE).
