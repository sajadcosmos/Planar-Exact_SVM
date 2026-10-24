# Claim-by-claim verification map

Each numbered result of the paper is listed with the Lean declarations in `PlanarSVM.lean` that prove it. All names live in the namespace `PlanarSep`.

## Section 2 — Existence, interpolation and class-size bounds

| Paper | Lean |
|---|---|
| Theorem 2.1 (polynomial separation of disjoint compact classes) | `compact_existence`, `path_meets_zeroSet` |
| Theorem 2.2 (Lagrange interpolation) and its corollary | `lagrangePoly_interpolates`, `polySep_card_sub_one` |
| Proposition 2.3 (class-size upper bound) | `sepDegree_le_classSize` |
| Proposition 2.5 (singleton dichotomy) | `sepDegree_singleton` |
| Theorem 2.6 (smooth minimum-degree separators) | `smooth_min_degree` |

## Section 3 — Veronese criterion and moment certificates

| Paper | Lean |
|---|---|
| Theorem 3.1 (Veronese convex-hull criterion) | `veronese_criterion`, `sepDegree_le_iff_veronese` |
| Corollary 3.2 (linear case) | `sepDegree_eq_one_iff` |
| Theorem 3.3 (moment certificates) | `not_polySep_iff_momentCert`, `lt_sepDegree_iff_momentCert` |
| Corollary 3.4 (sparse certificate) | `sparse_momentCert` |

## Section 4 — Exact laws on curves

| Paper | Lean |
|---|---|
| Theorem 4.1 (line law) | `line_law` |
| Theorem 4.2 (circle, parabola, hyperbola and affine images) | `circle_law`, `parabola_law`, `hyperbola_law`, `affine_parabola_law`, `affine_hyperbola_law` |
| Corollary 4.3 (ellipses; alternating labels) | `ellipse_law`, `circle_alternating` |
| Remark 4.4 (definition of "nondegenerate conic") | `conic_definition_counterexample` |
| Rational-curve lower bound | `trans_le_of_rational` |

## Section 5 — Invariance, genericity and stability

| Paper | Lean |
|---|---|
| Proposition 5.1 (affine invariance) | `sepDegree_affine_invariant` |
| Proposition 5.2 (generic interpolation, shattering of `M_d` points) | `generic_interpolation`, `grid_shattered`, `dgen_spec` |
| Proposition 5.3 (no shattering beyond `M_d`) | `not_shattered` |
| Theorem 5.4 (local stability of the upper bound) | `local_upper_stability` |

## Section 7 and Appendix A — Polynomial-kernel SVMs

| Paper | Lean |
|---|---|
| Appendix A (unit functional margin) | `polySep_iff_unit_margin` |
| Kernel identity | `kernel_identity` |
| Proposition 7.1 (separation ⟺ SVM feasibility) | `polySep_iff_svmFeasible` |
| `d_*` as the minimum feasible SVM degree | `sepDegree_eq_min_svm` |
| SVM norm identity | `svm_norm_identity` |

## Table 1

| Paper | Lean |
|---|---|
| XOR configuration | `xor_sepDegree` |
