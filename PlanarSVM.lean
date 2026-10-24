import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Algebraic separation complexity of planar data — Lean formalisation

This single file formalises the paper *Algebraic Separation Complexity of Planar Data:
Existence, Exact Conic Laws, and Certificates* (`planrsvm.tex`); the corrected paper is
`planrsvm_formalized.tex`.

* The plane is `Plane = Fin 2 → ℝ`, polynomials are `Poly = MvPolynomial (Fin 2) ℝ`.
* `PolySep d A B` : some polynomial of total degree `≤ d` is `> 0` on `A` and `< 0` on `B`.
* `sepDegree A B` : the algebraic separation degree `d_*(A,B)`.
* Ordered samples are given by `γ : ℕ → Plane`, labels `s : ℕ → Bool` and a length `N`;
  `trans s N` / `cycTrans s N` are the linear / cyclic transition numbers.

Main results (paper numbering): `compact_existence` (2.1), `lagrangePoly_interpolates` (2.2),
`sepDegree_le_classSize` (2.3), `sepDegree_singleton` (2.5), `smooth_min_degree` (2.6),
`sepDegree_le_iff_veronese` (3.1), `sepDegree_eq_one_iff` (3.2),
`not_polySep_iff_momentCert` / `lt_sepDegree_iff_momentCert` (3.3), `sparse_momentCert` (3.4),
`line_law` (4.1), `circle_law`, `ellipse_law`, `parabola_law`, `hyperbola_law`,
`affine_parabola_law`, `affine_hyperbola_law` (4.2), `circle_alternating` (4.3),
`trans_le_of_rational` (4.5, rational-curve lower bound), `conic_definition_counterexample`
(Remark 4.4), `sepDegree_affine_invariant` (5.1), `generic_interpolation`, `grid_shattered`,
`dgen_spec` (5.2), `not_shattered` (5.3), `local_upper_stability` (5.4),
`polySep_iff_unit_margin` (Appendix A), `kernel_identity`, `polySep_iff_svmFeasible`,
`sepDegree_eq_min_svm`, `svm_norm_identity` (Section 7), `xor_sepDegree` (Table 1).
-/

noncomputable section

namespace PlanarSep

open MvPolynomial

/-! ## Separation degree, interpolation and class-size bounds (Section 2) -/

/-- The real plane `ℝ²`, with points written as `z = (z 0, z 1)`. -/
abbrev Plane := Fin 2 → ℝ

/-- Real bivariate polynomials `ℝ[x,y]`. -/
abbrev Poly := MvPolynomial (Fin 2) ℝ

/-- `PolySep d A B`: some real polynomial of total degree at most `d` is strictly positive on
`A` and strictly negative on `B`. -/
def PolySep (d : ℕ) (A B : Set Plane) : Prop :=
  ∃ P : Poly, P.totalDegree ≤ d ∧ (∀ a ∈ A, 0 < eval a P) ∧ ∀ b ∈ B, eval b P < 0

/-- The algebraic separation degree `d_*(A,B)`: the least `d` for which `PolySep d A B` holds.
(When no such `d` exists the value is the junk value `0`; all theorems assume separability,
which holds for every pair of finite disjoint sets.) -/
def sepDegree (A B : Set Plane) : ℕ := sInf {d | PolySep d A B}

variable {A B : Set Plane}

theorem PolySep.mono {d e : ℕ} (h : d ≤ e) (hs : PolySep d A B) : PolySep e A B := by
  obtain ⟨P, hP, h1, h2⟩ := hs
  exact ⟨P, hP.trans h, h1, h2⟩

theorem PolySep.subset {d : ℕ} {A' B' : Set Plane} (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hs : PolySep d A B) : PolySep d A' B' := by
  obtain ⟨P, hP, h1, h2⟩ := hs
  exact ⟨P, hP, fun a ha => h1 a (hA ha), fun b hb => h2 b (hB hb)⟩

theorem polySep_sepDegree (h : ∃ d, PolySep d A B) : PolySep (sepDegree A B) A B :=
  Nat.sInf_mem h

theorem sepDegree_le_iff (h : ∃ d, PolySep d A B) {d : ℕ} :
    sepDegree A B ≤ d ↔ PolySep d A B :=
  ⟨fun hd => (polySep_sepDegree h).mono hd, fun hd => Nat.sInf_le hd⟩

theorem not_polySep_zero (hA : A.Nonempty) (hB : B.Nonempty) : ¬ PolySep 0 A B := by
  rintro ⟨P, hP, h1, h2⟩
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  have hc := (totalDegree_eq_zero_iff_eq_C (p := P)).1 (Nat.le_zero.1 hP)
  have e1 := h1 a ha
  have e2 := h2 b hb
  rw [hc] at e1 e2
  simp only [eval_C] at e1 e2
  linarith

theorem one_le_sepDegree (hA : A.Nonempty) (hB : B.Nonempty) (h : ∃ d, PolySep d A B) :
    1 ≤ sepDegree A B := by
  by_contra h0
  push_neg at h0
  have := polySep_sepDegree h
  rw [Nat.lt_one_iff.1 h0] at this
  exact not_polySep_zero hA hB this

/-! ### Explicit finite interpolation (Theorem 2.2) -/

/-- Squared Euclidean distance. -/
def sqDist (u v : Plane) : ℝ := ∑ k, (u k - v k) ^ 2

theorem sqDist_pos {u v : Plane} (h : u ≠ v) : 0 < sqDist u v := by
  unfold sqDist
  have : ∃ k, u k ≠ v k := by
    by_contra hk; push_neg at hk; exact h (funext hk)
  obtain ⟨k, hk⟩ := this
  have hk' : 0 < (u k - v k) ^ 2 := by
    have : u k - v k ≠ 0 := sub_ne_zero.2 hk
    positivity
  calc 0 < (u k - v k) ^ 2 := hk'
    _ ≤ ∑ j, (u j - v j) ^ 2 :=
      Finset.single_le_sum (f := fun j => (u j - v j) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ k)

/-- The affine polynomial `ℓ_{ij}(z) = (z - z_j)·(z_i - z_j) / ‖z_i - z_j‖²`. -/
def ellPoly (zi zj : Plane) : Poly :=
  C (1 / sqDist zi zj) * ∑ k, C (zi k - zj k) * (X k - C (zj k))

theorem totalDegree_ellPoly_le (zi zj : Plane) : (ellPoly zi zj).totalDegree ≤ 1 := by
  unfold ellPoly
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_sum _ _).trans ?_
  refine Finset.sup_le fun k _ => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans ?_
  rw [totalDegree_X, totalDegree_C]
  simp

theorem eval_ellPoly (zi zj z : Plane) :
    eval z (ellPoly zi zj) = (1 / sqDist zi zj) * ∑ k, (zi k - zj k) * (z k - zj k) := by
  simp [ellPoly]

theorem eval_ellPoly_self {zi zj : Plane} (h : zi ≠ zj) : eval zi (ellPoly zi zj) = 1 := by
  rw [eval_ellPoly]
  have hp := sqDist_pos h
  have : ∑ k, (zi k - zj k) * (zi k - zj k) = sqDist zi zj := by
    unfold sqDist; congr 1; ext k; ring
  rw [this]; field_simp

theorem eval_ellPoly_other (zi zj : Plane) : eval zj (ellPoly zi zj) = 0 := by
  rw [eval_ellPoly]; simp

/-- The Lagrange basis polynomial `L_i(z) = ∏_{j ≠ i} ℓ_{ij}(z)`. -/
def lagrangeBasis (S : Finset Plane) (zi : Plane) : Poly := ∏ zj ∈ S.erase zi, ellPoly zi zj

/-- The explicit interpolating polynomial `P(z) = ∑_i v_i L_i(z)` of Theorem 2.2. -/
def lagrangePoly (S : Finset Plane) (v : Plane → ℝ) : Poly :=
  ∑ zi ∈ S, C (v zi) * lagrangeBasis S zi

theorem totalDegree_lagrangeBasis_le (S : Finset Plane) {zi : Plane} (hi : zi ∈ S) :
    (lagrangeBasis S zi).totalDegree ≤ S.card - 1 := by
  unfold lagrangeBasis
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ zj ∈ S.erase zi, (ellPoly zi zj).totalDegree ≤ ∑ _zj ∈ S.erase zi, 1 :=
        Finset.sum_le_sum fun j _ => totalDegree_ellPoly_le zi j
    _ = (S.erase zi).card := by simp
    _ = S.card - 1 := Finset.card_erase_of_mem hi

theorem totalDegree_lagrangePoly_le (S : Finset Plane) (v : Plane → ℝ) :
    (lagrangePoly S v).totalDegree ≤ S.card - 1 := by
  unfold lagrangePoly
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun zi hi => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact totalDegree_lagrangeBasis_le S hi

theorem eval_lagrangeBasis (S : Finset Plane) {zi zk : Plane} (hk : zk ∈ S) :
    eval zk (lagrangeBasis S zi) = if zk = zi then 1 else 0 := by
  unfold lagrangeBasis
  rw [map_prod]
  split_ifs with h
  · subst h
    exact Finset.prod_eq_one fun j hj => eval_ellPoly_self (Finset.ne_of_mem_erase hj).symm
  · exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨h, hk⟩) (eval_ellPoly_other zi zk)

/-- **Theorem 2.2 (explicit finite interpolation).** For distinct points `S` (a finset) and
arbitrary values `v`, the explicit polynomial `lagrangePoly S v` has total degree at most
`|S| - 1` and interpolates `v` on `S`. -/
theorem lagrangePoly_interpolates (S : Finset Plane) (v : Plane → ℝ) :
    (lagrangePoly S v).totalDegree ≤ S.card - 1 ∧ ∀ z ∈ S, eval z (lagrangePoly S v) = v z := by
  refine ⟨totalDegree_lagrangePoly_le S v, fun z hz => ?_⟩
  unfold lagrangePoly
  rw [map_sum]
  simp only [map_mul, eval_C, eval_lagrangeBasis S hz, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq S z]
  simp [hz]

/-- Corollary of Theorem 2.2: finite disjoint classes are separable in degree `|A ∪ B| - 1`. -/
theorem polySep_card_sub_one (A B : Finset Plane) (hAB : Disjoint A B) :
    PolySep ((A ∪ B).card - 1) ↑A ↑B := by
  classical
  refine ⟨lagrangePoly (A ∪ B) (fun z => if z ∈ A then 1 else -1),
    (lagrangePoly_interpolates _ _).1, fun a ha => ?_, fun b hb => ?_⟩
  · rw [(lagrangePoly_interpolates _ _).2 a (Finset.mem_union_left _ ha)]
    simp [show a ∈ A from ha]
  · rw [(lagrangePoly_interpolates _ _).2 b (Finset.mem_union_right _ hb)]
    have : b ∉ A := fun h => Finset.disjoint_left.1 hAB h hb
    simp [this]

/-! ### Class-size bound (Proposition 2.3) -/

/-- The polynomial `‖z - a‖²`. -/
def sqDistPoly (a : Plane) : Poly := ∑ k, (X k - C (a k)) ^ 2

theorem eval_sqDistPoly (a z : Plane) : eval z (sqDistPoly a) = sqDist z a := by
  simp [sqDistPoly, sqDist]

theorem totalDegree_sqDistPoly_le (a : Plane) : (sqDistPoly a).totalDegree ≤ 2 := by
  unfold sqDistPoly
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (totalDegree_pow _ _).trans ?_
  have : (X k - C (a k) : Poly).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_X, totalDegree_C]; simp
  omega

/-- `Q_A(z) = ∏_{a ∈ A} ‖z - a‖²`. -/
def classPoly (A : Finset Plane) : Poly := ∏ a ∈ A, sqDistPoly a

theorem totalDegree_classPoly_le (A : Finset Plane) : (classPoly A).totalDegree ≤ 2 * A.card := by
  unfold classPoly
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ a ∈ A, (sqDistPoly a).totalDegree ≤ ∑ _a ∈ A, 2 :=
        Finset.sum_le_sum fun a _ => totalDegree_sqDistPoly_le a
    _ = 2 * A.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- The class `A` alone can be isolated by a polynomial of degree `2|A|`. -/
theorem polySep_two_mul_card (A B : Finset Plane) (hAB : Disjoint A B) :
    PolySep (2 * A.card) ↑A ↑B := by
  classical
  -- δ = min over B of Q_A, positive
  have hpos : ∀ b ∈ B, 0 < eval b (classPoly A) := by
    intro b hb
    unfold classPoly
    rw [map_prod]
    refine Finset.prod_pos fun a ha => ?_
    rw [eval_sqDistPoly]
    refine sqDist_pos ?_
    rintro rfl
    exact Finset.disjoint_left.1 hAB ha hb
  obtain ⟨ε, hε, hεB⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ b ∈ B, ε < eval b (classPoly A) := by
    by_cases hB : B.Nonempty
    · obtain ⟨b0, hb0, hmin⟩ := B.exists_min_image (fun b => eval b (classPoly A)) hB
      refine ⟨eval b0 (classPoly A) / 2, by linarith [hpos b0 hb0], fun b hb => ?_⟩
      linarith [hmin b hb, hpos b0 hb0]
    · refine ⟨1, one_pos, fun b hb => absurd ⟨b, hb⟩ hB⟩
  refine ⟨C ε - classPoly A, ?_, fun a ha => ?_, fun b hb => ?_⟩
  · refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_C]
    simpa using totalDegree_classPoly_le A
  · have : eval a (classPoly A) = 0 := by
      unfold classPoly
      rw [map_prod]
      exact Finset.prod_eq_zero (show a ∈ A from ha) (by rw [eval_sqDistPoly]; simp [sqDist])
    simp [this, hε]
  · simp only [map_sub, eval_C]
    linarith [hεB b hb]

theorem PolySep.neg_swap {d : ℕ} (h : PolySep d A B) : PolySep d B A := by
  obtain ⟨P, hP, h1, h2⟩ := h
  refine ⟨-P, by rwa [totalDegree_neg], fun b hb => ?_, fun a ha => ?_⟩
  · simp [h2 b hb]
  · simp [h1 a ha]

/-- **Proposition 2.3 (class-size upper bound).** For finite disjoint classes,
`d_*(A,B) ≤ min{N-1, 2m, 2n}` with `m = |A|`, `n = |B|`, `N = m + n`. -/
theorem sepDegree_le_classSize (A B : Finset Plane) (hAB : Disjoint A B) :
    sepDegree ↑A ↑B ≤ min ((A.card + B.card) - 1) (min (2 * A.card) (2 * B.card)) := by
  have h1 := polySep_card_sub_one A B hAB
  rw [Finset.card_union_of_disjoint hAB] at h1
  have h2 := polySep_two_mul_card A B hAB
  have h3 := (polySep_two_mul_card B A hAB.symm).neg_swap
  have hex : ∃ d, PolySep d ↑A ↑B := ⟨_, h1⟩
  refine le_min ((sepDegree_le_iff hex).2 h1) (le_min ((sepDegree_le_iff hex).2 h2)
    ((sepDegree_le_iff hex).2 h3))

/-- Finite disjoint classes are always polynomially separable. -/
theorem exists_polySep (A B : Finset Plane) (hAB : Disjoint A B) : ∃ d, PolySep d ↑A ↑B :=
  ⟨_, polySep_card_sub_one A B hAB⟩

/-! ## Compact classes, Veronese criterion and moment certificates (Sections 2–3) -/

/-! ### Compact classes (Theorem 2.1) -/

/-- **Theorem 2.1 (polynomial separation of disjoint compact classes).** -/
theorem compact_existence (A B : Set Plane) (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) : ∃ P : Poly, (∀ a ∈ A, 0 < eval a P) ∧ ∀ b ∈ B, eval b P < 0 := by
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · exact ⟨C (-1), by simp, fun b _ => by simp⟩
  rcases B.eq_empty_or_nonempty with rfl | hBne
  · exact ⟨C 1, fun a _ => by simp, by simp⟩
  -- the continuous function g = (d_B - d_A)/(d_A + d_B), equal to 1 on A and -1 on B
  set dA : Plane → ℝ := fun z => Metric.infDist z A
  set dB : Plane → ℝ := fun z => Metric.infDist z B
  have hden : ∀ z, 0 < dA z + dB z := by
    intro z
    have h1 : 0 ≤ dA z := Metric.infDist_nonneg
    have h2 : 0 ≤ dB z := Metric.infDist_nonneg
    by_contra hc
    have e1 : dA z = 0 := by linarith
    have e2 : dB z = 0 := by linarith
    have zA : z ∈ A := (hA.isClosed.mem_iff_infDist_zero hAne).2 e1
    have zB : z ∈ B := (hB.isClosed.mem_iff_infDist_zero hBne).2 e2
    exact Set.disjoint_left.1 hAB zA zB
  set g : Plane → ℝ := fun z => (dB z - dA z) / (dA z + dB z)
  have hgc : Continuous g := by
    refine Continuous.div ((Metric.continuous_infDist_pt _).sub (Metric.continuous_infDist_pt _))
      ((Metric.continuous_infDist_pt _).add (Metric.continuous_infDist_pt _)) (fun z => (hden z).ne')
  have hgA : ∀ a ∈ A, g a = 1 := by
    intro a ha
    have : dA a = 0 := Metric.infDist_zero_of_mem ha
    have h := hden a
    simp only [g, this] at h ⊢
    field_simp
    simp
  have hgB : ∀ b ∈ B, g b = -1 := by
    intro b hb
    have : dB b = 0 := Metric.infDist_zero_of_mem hb
    have h := hden b
    simp only [g, this] at h ⊢
    field_simp
    simp
  -- Stone–Weierstrass on K = A ∪ B
  set K : Set Plane := A ∪ B
  have hK : IsCompact K := hA.union hB
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let coord : Fin 2 → C(K, ℝ) := fun i =>
    ⟨fun k => (k : Plane) i, (continuous_apply i).comp continuous_subtype_val⟩
  let S : Subalgebra ℝ C(K, ℝ) := (aeval coord).range
  have hev : ∀ (P : Poly) (k : K), (aeval coord P) k = eval (k : Plane) P := by
    intro P k
    induction P using MvPolynomial.induction_on with
    | C r => simp [_root_.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp, coord]
  have hsep : S.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, (x : Plane) i ≠ (y : Plane) i := by
      by_contra h; push_neg at h; exact hxy (Subtype.ext (funext h))
    obtain ⟨i, hi⟩ := this
    refine ⟨_, ⟨aeval coord (X i), ⟨X i, rfl⟩, rfl⟩, ?_⟩
    simpa [coord] using hi
  obtain ⟨q, hq⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints S hsep
    (fun k : K => g k) (hgc.comp continuous_subtype_val) (1 / 2) (by norm_num)
  obtain ⟨P, hP⟩ := q.2
  have hPq : ∀ k : K, eval (k : Plane) P = (q : C(K, ℝ)) k := by
    intro k; rw [← hev]; exact congrFun (congrArg DFunLike.coe hP) k
  refine ⟨P, fun a ha => ?_, fun b hb => ?_⟩
  · have h := hq ⟨a, Or.inl ha⟩
    rw [← hPq] at h
    simp only [hgA a ha, Real.norm_eq_abs] at h
    have := (abs_lt.1 h).1
    simp only at this
    linarith
  · have h := hq ⟨b, Or.inr hb⟩
    rw [← hPq] at h
    simp only [hgB b hb, Real.norm_eq_abs] at h
    have := (abs_lt.1 h).2
    simp only at this
    linarith

/-- Second half of Theorem 2.1: every continuous path from a point where `P > 0` to a point
where `P < 0` meets the zero set of `P`. -/
theorem path_meets_zeroSet (P : Poly) (γ : ℝ → Plane) (hγ : ContinuousOn γ (Set.Icc 0 1))
    (h0 : 0 < eval (γ 0) P) (h1 : eval (γ 1) P < 0) :
    ∃ t ∈ Set.Ioo (0 : ℝ) 1, eval (γ t) P = 0 := by
  have hc : ContinuousOn (fun t => eval (γ t) P) (Set.Icc 0 1) :=
    (MvPolynomial.continuous_eval P).comp_continuousOn hγ
  have := intermediate_value_Icc' (zero_le_one) hc
  obtain ⟨t, ht, htz⟩ := this ⟨h1.le, h0.le⟩
  refine ⟨t, ⟨?_, ?_⟩, htz⟩
  · rcases ht.1.eq_or_lt with h | h
    · subst h; simp at htz; linarith
    · exact h
  · rcases ht.2.eq_or_lt with h | h
    · subst h; simp at htz; linarith
    · exact h

/-! ### Separation of finite sets by affine functionals -/

/-- Finite sets in `ℝ^ι` are strictly separated by an affine functional iff their convex hulls
are disjoint. -/
theorem exists_affine_sep_iff {ι : Type*} [Fintype ι] (S T : Set (ι → ℝ)) (hS : S.Finite)
    (hT : T.Finite) :
    (∃ c : ι → ℝ, ∃ u : ℝ, (∀ x ∈ S, 0 < u + ∑ i, c i * x i) ∧ ∀ y ∈ T, u + ∑ i, c i * y i < 0) ↔
      Disjoint (convexHull ℝ S) (convexHull ℝ T) := by
  classical
  constructor
  · rintro ⟨c, u, hSc, hTc⟩
    let f : (ι → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun x => ∑ i, c i * x i
        map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r x => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring }
    have hS' : S ⊆ {x | -u < f x} := by
      intro x hx
      have := hSc x hx
      simp only [Set.mem_setOf_eq, f, LinearMap.coe_mk, AddHom.coe_mk]
      linarith
    have hT' : T ⊆ {x | f x < -u} := by
      intro x hx
      have := hTc x hx
      simp only [Set.mem_setOf_eq, f, LinearMap.coe_mk, AddHom.coe_mk]
      linarith
    have h1 : convexHull ℝ S ⊆ {x | -u < f x} :=
      convexHull_min hS' (convex_halfSpace_gt f.isLinear _)
    have h2 : convexHull ℝ T ⊆ {x | f x < -u} :=
      convexHull_min hT' (convex_halfSpace_lt f.isLinear _)
    rw [Set.disjoint_left]
    intro x hx hx'
    have := h1 hx; have := h2 hx'
    simp only [Set.mem_setOf_eq] at *
    linarith
  · intro hdisj
    obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed (convex_convexHull ℝ S)
      hS.isCompact_convexHull (convex_convexHull ℝ T) hT.isCompact_convexHull.isClosed hdisj
    have hf : ∀ x : ι → ℝ, f x = ∑ i, (f fun j => if i = j then 1 else 0) * x i := by
      intro x
      rw [show f x = f.toLinearMap x from rfl, LinearMap.pi_apply_eq_sum_univ]
      simp [mul_comm]
    refine ⟨fun i => -(f fun j => if i = j then 1 else 0), u, fun x hx => ?_, fun y hy => ?_⟩
    · have := hfu x (subset_convexHull ℝ S hx)
      rw [hf] at this
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
    · have := hfv y (subset_convexHull ℝ T hy)
      rw [hf] at this
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith

/-! ### The Veronese representation -/

/-- Exponent pairs `(r,s)` with `r + s ≤ d`. -/
def monoSet (d : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (d + 1)) ×ˢ (Finset.range (d + 1))).filter (fun p => p.1 + p.2 ≤ d)

theorem mem_monoSet {d : ℕ} {p : ℕ × ℕ} : p ∈ monoSet d ↔ p.1 + p.2 ≤ d := by
  simp only [monoSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The index type of the monomials of total degree at most `d`. -/
abbrev Mono (d : ℕ) := ↥(monoSet d)

/-- The Veronese (total-degree monomial) map `Φ_d(x,y) = (x^r y^s)_{r+s ≤ d}`. -/
def veronese (d : ℕ) (z : Plane) : Mono d → ℝ := fun p => z 0 ^ p.1.1 * z 1 ^ p.1.2

/-- The polynomial `∑_{r+s ≤ d} c_{rs} x^r y^s`. -/
def polyOfCoeff (d : ℕ) (c : ℕ × ℕ → ℝ) : Poly :=
  ∑ p ∈ monoSet d, C (c p) * (X 0 ^ p.1 * X 1 ^ p.2)

theorem totalDegree_polyOfCoeff_le (d : ℕ) (c : ℕ × ℕ → ℝ) :
    (polyOfCoeff d c).totalDegree ≤ d := by
  unfold polyOfCoeff
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun p hp => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_mul _ _).trans ?_
  refine (add_le_add (totalDegree_pow _ _) (totalDegree_pow _ _)).trans ?_
  rw [totalDegree_X, totalDegree_X, mul_one, mul_one]
  exact mem_monoSet.1 hp

theorem eval_polyOfCoeff (d : ℕ) (c : ℕ × ℕ → ℝ) (z : Plane) :
    eval z (polyOfCoeff d c) = ∑ p ∈ monoSet d, c p * (z 0 ^ p.1 * z 1 ^ p.2) := by
  simp [polyOfCoeff]

/-- Every polynomial of total degree `≤ d` is a linear combination of the monomials
`x^r y^s`, `r + s ≤ d`. -/
theorem exists_coeff_of_totalDegree_le {d : ℕ} {P : Poly} (hP : P.totalDegree ≤ d) :
    ∃ c : ℕ × ℕ → ℝ, ∀ z : Plane, eval z P = ∑ p ∈ monoSet d, c p * (z 0 ^ p.1 * z 1 ^ p.2) := by
  classical
  let key : (Fin 2 →₀ ℕ) → ℕ × ℕ := fun m => (m 0, m 1)
  refine ⟨fun p => ∑ m ∈ P.support.filter (fun m => key m = p), coeff m P, fun z => ?_⟩
  have hmaps : ∀ m ∈ P.support, key m ∈ monoSet d := by
    intro m hm
    have := le_totalDegree hm
    rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
    exact mem_monoSet.2 (this.trans hP)
  rw [eval_eq']
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun m hm => ?_
  rw [Finset.mem_filter] at hm
  rw [Fin.prod_univ_two, ← hm.2]

/-- Linear functional form: `P(z) = c^T Φ_d(z)` on the Veronese coordinates. -/
theorem sum_mono_eq (d : ℕ) (c : ℕ × ℕ → ℝ) (z : Plane) :
    ∑ p ∈ monoSet d, c p * (z 0 ^ p.1 * z 1 ^ p.2) =
      ∑ p : Mono d, c p.1 * veronese d z p := by
  rw [← Finset.sum_coe_sort (monoSet d)]
  rfl

/-- Polynomial separability in degree `d` is affine separability of the Veronese images. -/
theorem polySep_iff_affine_veronese (d : ℕ) (A B : Set Plane) :
    PolySep d A B ↔ ∃ c : Mono d → ℝ, ∃ u : ℝ,
      (∀ x ∈ veronese d '' A, 0 < u + ∑ i, c i * x i) ∧
        ∀ y ∈ veronese d '' B, u + ∑ i, c i * y i < 0 := by
  classical
  simp only [Set.forall_mem_image]
  constructor
  · rintro ⟨P, hP, h1, h2⟩
    obtain ⟨c, hc⟩ := exists_coeff_of_totalDegree_le hP
    refine ⟨fun p => c p.1, 0, fun a ha => ?_, fun b hb => ?_⟩
    · have := h1 a ha; rw [hc, sum_mono_eq] at this; simpa using this
    · have := h2 b hb; rw [hc, sum_mono_eq] at this; simpa using this
  · rintro ⟨c, u, h1, h2⟩
    let c' : ℕ × ℕ → ℝ := fun p => if h : p ∈ monoSet d then c ⟨p, h⟩ else 0
    have hc' : ∀ z, eval z (C u + polyOfCoeff d c') = u + ∑ i, c i * veronese d z i := by
      intro z
      rw [map_add, eval_C, eval_polyOfCoeff, sum_mono_eq]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [c', p.2]
    refine ⟨C u + polyOfCoeff d c', ?_, fun a ha => ?_, fun b hb => ?_⟩
    · refine (totalDegree_add _ _).trans (max_le ?_ (totalDegree_polyOfCoeff_le d c'))
      simp
    · rw [hc']; exact h1 ha
    · rw [hc']; exact h2 hb

/-- **Theorem 3.1 (Veronese convex-hull criterion).** For finite `A, B`, degree-`d`
separability holds iff the convex hulls of the Veronese images are disjoint. -/
theorem veronese_criterion (d : ℕ) (A B : Set Plane) (hA : A.Finite) (hB : B.Finite) :
    PolySep d A B ↔ Disjoint (convexHull ℝ (veronese d '' A)) (convexHull ℝ (veronese d '' B)) := by
  rw [polySep_iff_affine_veronese]
  exact exists_affine_sep_iff _ _ (hA.image _) (hB.image _)

/-- **Theorem 3.1, `d_*` form.** For finite disjoint classes,
`d_*(A,B) ≤ d ⟺ conv Φ_d(A) ∩ conv Φ_d(B) = ∅`. -/
theorem sepDegree_le_iff_veronese (d : ℕ) (A B : Finset Plane) (hAB : Disjoint A B) :
    sepDegree ↑A ↑B ≤ d ↔
      Disjoint (convexHull ℝ (veronese d '' ↑A)) (convexHull ℝ (veronese d '' ↑B)) := by
  rw [sepDegree_le_iff (exists_polySep A B hAB)]
  exact veronese_criterion d _ _ A.finite_toSet B.finite_toSet

/-- Polynomials of degree at most one are affine functions. -/
theorem polySep_one_iff_affine (A B : Set Plane) :
    PolySep 1 A B ↔ ∃ c : Fin 2 → ℝ, ∃ u : ℝ,
      (∀ x ∈ A, 0 < u + ∑ i, c i * x i) ∧ ∀ y ∈ B, u + ∑ i, c i * y i < 0 := by
  constructor
  · rintro ⟨P, hP, h1, h2⟩
    obtain ⟨c, hc⟩ := exists_coeff_of_totalDegree_le hP
    have hms : monoSet 1 = {(0, 0), (0, 1), (1, 0)} := by decide
    have he : ∀ z : Plane, eval z P = c (0, 0) + ∑ i, ![c (1, 0), c (0, 1)] i * z i := by
      intro z; rw [hc, hms]; simp [Fin.sum_univ_two]; ring
    refine ⟨![c (1, 0), c (0, 1)], c (0, 0), fun a ha => ?_, fun b hb => ?_⟩
    · rw [← he]; exact h1 a ha
    · rw [← he]; exact h2 b hb
  · rintro ⟨c, u, h1, h2⟩
    refine ⟨C u + ∑ i, C (c i) * X i, ?_, fun a ha => ?_, fun b hb => ?_⟩
    · refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
      refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
      refine (totalDegree_mul _ _).trans ?_
      simp
    · simpa using h1 a ha
    · simpa using h2 b hb

/-- Degree-one separability of finite sets is disjointness of their convex hulls. -/
theorem polySep_one_iff_disjoint_convexHull (A B : Set Plane) (hA : A.Finite) (hB : B.Finite) :
    PolySep 1 A B ↔ Disjoint (convexHull ℝ A) (convexHull ℝ B) := by
  rw [polySep_one_iff_affine]
  exact exists_affine_sep_iff A B hA hB

/-- **Corollary 3.2 (linear case).** For finite, disjoint, *nonempty* classes,
`d_*(A,B) = 1 ⟺ conv A ∩ conv B = ∅`. (Nonemptiness of both classes is needed: if one class
is empty then `d_* = 0`.) -/
theorem sepDegree_eq_one_iff (A B : Finset Plane) (hAB : Disjoint A B) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    sepDegree ↑A ↑B = 1 ↔ Disjoint (convexHull ℝ (↑A : Set Plane)) (convexHull ℝ ↑B) := by
  have hex := exists_polySep A B hAB
  have h1 := one_le_sepDegree (Finset.coe_nonempty.2 hA) (Finset.coe_nonempty.2 hB) hex
  rw [← polySep_one_iff_disjoint_convexHull _ _ A.finite_toSet B.finite_toSet,
    ← sepDegree_le_iff hex]
  omega

/-- **Proposition 2.5 (singleton dichotomy).** If `A = {a}` and `B` is a nonempty finite set
not containing `a`, then `d_* = 1` when `a ∉ conv B` and `d_* = 2` when `a ∈ conv B`. -/
theorem sepDegree_singleton (a : Plane) (B : Finset Plane) (hB : B.Nonempty) (haB : a ∉ B) :
    (a ∉ convexHull ℝ (↑B : Set Plane) → sepDegree ↑({a} : Finset Plane) ↑B = 1) ∧
      (a ∈ convexHull ℝ (↑B : Set Plane) → sepDegree ↑({a} : Finset Plane) ↑B = 2) := by
  have hAB : Disjoint ({a} : Finset Plane) B := Finset.disjoint_singleton_left.2 haB
  have hiff := sepDegree_eq_one_iff {a} B hAB (Finset.singleton_nonempty a) hB
  have hdisj : Disjoint (convexHull ℝ (↑({a} : Finset Plane) : Set Plane)) (convexHull ℝ ↑B) ↔
      a ∉ convexHull ℝ (↑B : Set Plane) := by
    simp [Set.disjoint_singleton_left]
  rw [hdisj] at hiff
  refine ⟨hiff.2, fun ha => ?_⟩
  have hle := sepDegree_le_classSize {a} B hAB
  have hge := one_le_sepDegree (Finset.coe_nonempty.2 (Finset.singleton_nonempty a))
    (Finset.coe_nonempty.2 hB) (exists_polySep _ _ hAB)
  have hne : sepDegree ↑({a} : Finset Plane) ↑B ≠ 1 := fun h => (hiff.1 h) ha
  simp only [Finset.card_singleton] at hle
  omega

/-! ### Truncated-moment certificates (Theorem 3.3) -/

/-- Weights on a finite set representing a point of the convex hull of an image. -/
theorem exists_weights_of_mem_convexHull_image {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Finset Plane) (f : Plane → E) {x : E} (hx : x ∈ convexHull ℝ (f '' ↑A)) :
    ∃ α : Plane → ℝ, (∀ a ∈ A, 0 ≤ α a) ∧ ∑ a ∈ A, α a = 1 ∧ ∑ a ∈ A, α a • f a = x := by
  classical
  obtain ⟨ι, _, w, z, hw0, hw1, hz, hx⟩ := mem_convexHull_iff_exists_fintype.1 hx
  choose g hgA hgz using fun i => (hz i : z i ∈ f '' ↑A)
  refine ⟨fun a => ∑ i ∈ Finset.univ.filter (fun i => g i = a), w i, fun a _ =>
    Finset.sum_nonneg fun i _ => hw0 i, ?_, ?_⟩
  · rw [Finset.sum_fiberwise_of_maps_to (fun i _ => hgA i), hw1]
  · simp_rw [Finset.sum_smul]
    rw [← hx, ← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := A) (g := g)
      (fun i _ => hgA i)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_filter] at hi
    rw [← hi.2, hgz]

/-- The moment-matching condition of Theorem 3.3: `α ∈ Δ(A)`, `β ∈ Δ(B)` and the two discrete
measures have identical moments `∫ x^r y^s` for `r + s ≤ d`. -/
def MomentCert (d : ℕ) (A B : Finset Plane) (α β : Plane → ℝ) : Prop :=
  (∀ a ∈ A, 0 ≤ α a) ∧ ∑ a ∈ A, α a = 1 ∧ (∀ b ∈ B, 0 ≤ β b) ∧ ∑ b ∈ B, β b = 1 ∧
    ∀ r s : ℕ, r + s ≤ d →
      ∑ a ∈ A, α a * (a 0 ^ r * a 1 ^ s) = ∑ b ∈ B, β b * (b 0 ^ r * b 1 ^ s)

/-- **Theorem 3.3 (truncated-moment certificate).** For finite `A, B`, degree-`d` separation
fails iff there are probability weights on `A` and `B` with equal moments through degree `d`. -/
theorem not_polySep_iff_momentCert (d : ℕ) (A B : Finset Plane) :
    ¬ PolySep d ↑A ↑B ↔ ∃ α β, MomentCert d A B α β := by
  classical
  constructor
  · intro h
    rw [veronese_criterion d _ _ A.finite_toSet B.finite_toSet, Set.not_disjoint_iff] at h
    obtain ⟨w, hwA, hwB⟩ := h
    obtain ⟨α, hα0, hα1, hαw⟩ := exists_weights_of_mem_convexHull_image A (veronese d) hwA
    obtain ⟨β, hβ0, hβ1, hβw⟩ := exists_weights_of_mem_convexHull_image B (veronese d) hwB
    refine ⟨α, β, hα0, hα1, hβ0, hβ1, fun r s hrs => ?_⟩
    have hp : (r, s) ∈ monoSet d := mem_monoSet.2 hrs
    have := congrFun (hαw.trans hβw.symm) ⟨(r, s), hp⟩
    simpa [Finset.sum_apply, veronese] using this
  · rintro ⟨α, β, hα0, hα1, hβ0, hβ1, hm⟩ ⟨P, hP, h1, h2⟩
    obtain ⟨c, hc⟩ := exists_coeff_of_totalDegree_le hP
    have key : ∑ a ∈ A, α a * eval a P = ∑ b ∈ B, β b * eval b P := by
      simp_rw [hc, Finset.mul_sum]
      rw [Finset.sum_comm, Finset.sum_comm (s := B)]
      refine Finset.sum_congr rfl fun p hp => ?_
      have := hm p.1 p.2 (mem_monoSet.1 hp)
      calc ∑ a ∈ A, α a * (c p * (a 0 ^ p.1 * a 1 ^ p.2))
          = c p * ∑ a ∈ A, α a * (a 0 ^ p.1 * a 1 ^ p.2) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
        _ = c p * ∑ b ∈ B, β b * (b 0 ^ p.1 * b 1 ^ p.2) := by rw [this]
        _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring
    have hpos : 0 < ∑ a ∈ A, α a * eval a P := by
      obtain ⟨a, ha, hαa⟩ : ∃ a ∈ A, 0 < α a := by
        by_contra hc; push_neg at hc
        have : ∑ a ∈ A, α a ≤ 0 := Finset.sum_nonpos hc
        linarith
      exact Finset.sum_pos' (fun a ha => mul_nonneg (hα0 a ha) (h1 a ha).le)
        ⟨a, ha, mul_pos hαa (h1 a ha)⟩
    have hneg : ∑ b ∈ B, β b * eval b P < 0 := by
      obtain ⟨b, hb, hβb⟩ : ∃ b ∈ B, 0 < β b := by
        by_contra hc; push_neg at hc
        have : ∑ b ∈ B, β b ≤ 0 := Finset.sum_nonpos hc
        linarith
      have := Finset.sum_pos' (s := B) (f := fun b => β b * -eval b P)
        (fun b hb => mul_nonneg (hβ0 b hb) (by linarith [h2 b hb]))
        ⟨b, hb, mul_pos hβb (by linarith [h2 b hb])⟩
      simp only [mul_neg, Finset.sum_neg_distrib] at this
      linarith
    linarith

/-- **Theorem 3.3, `d_*` form.** `d_*(A,B) > d` iff a moment certificate exists. -/
theorem lt_sepDegree_iff_momentCert (d : ℕ) (A B : Finset Plane) (hAB : Disjoint A B) :
    d < sepDegree ↑A ↑B ↔ ∃ α β, MomentCert d A B α β := by
  rw [← not_polySep_iff_momentCert, ← sepDegree_le_iff (exists_polySep A B hAB), not_le]

/-! ## Transition numbers and the one-dimensional core (Section 4) -/

/-! ### Ordered labelled samples and transition numbers -/

/-- Indices `i < N - 1` with a label change `s i ≠ s (i+1)`. -/
def transSet (s : ℕ → Bool) (N : ℕ) : Finset ℕ :=
  (Finset.range (N - 1)).filter (fun i => s i ≠ s (i + 1))

/-- The (linear) transition number `R = #{i < N-1 : s_i ≠ s_{i+1}}`. -/
def trans (s : ℕ → Bool) (N : ℕ) : ℕ := (transSet s N).card

/-- The cyclic transition number `R_cyc = #{i < N : s_i ≠ s_{i+1 mod N}}`, written as the
linear transitions plus the wrap-around transition between `s_{N-1}` and `s_0`. -/
def cycTrans (s : ℕ → Bool) (N : ℕ) : ℕ :=
  trans s N + if 0 < N ∧ s (N - 1) ≠ s 0 then 1 else 0

/-- Positively labelled points of an indexed sample `(γ i, s i)`, `i < N`. -/
def posPts (γ : ℕ → Plane) (s : ℕ → Bool) (N : ℕ) : Set Plane :=
  {z | ∃ i < N, s i = true ∧ γ i = z}

/-- Negatively labelled points of an indexed sample. -/
def negPts (γ : ℕ → Plane) (s : ℕ → Bool) (N : ℕ) : Set Plane :=
  {z | ∃ i < N, s i = false ∧ γ i = z}

/-- `P` realises the labels of the sample. -/
def Realizes (P : Poly) (γ : ℕ → Plane) (s : ℕ → Bool) (N : ℕ) : Prop :=
  ∀ i < N, (s i = true → 0 < eval (γ i) P) ∧ (s i = false → eval (γ i) P < 0)

theorem polySep_iff_realizes (d : ℕ) (γ : ℕ → Plane) (s : ℕ → Bool) (N : ℕ) :
    PolySep d (posPts γ s N) (negPts γ s N) ↔
      ∃ P : Poly, P.totalDegree ≤ d ∧ Realizes P γ s N := by
  constructor
  · rintro ⟨P, hP, h1, h2⟩
    exact ⟨P, hP, fun i hi => ⟨fun hs => h1 _ ⟨i, hi, hs, rfl⟩, fun hs => h2 _ ⟨i, hi, hs, rfl⟩⟩⟩
  · rintro ⟨P, hP, h⟩
    refine ⟨P, hP, ?_, ?_⟩
    · rintro _ ⟨i, hi, hs, rfl⟩; exact (h i hi).1 hs
    · rintro _ ⟨i, hi, hs, rfl⟩; exact (h i hi).2 hs

theorem mem_transSet {s : ℕ → Bool} {N j : ℕ} :
    j ∈ transSet s N ↔ j + 1 < N ∧ s j ≠ s (j + 1) := by
  simp only [transSet, Finset.mem_filter, Finset.mem_range]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩

theorem mono_of_succ {t : ℕ → ℝ} {N : ℕ} (ht : ∀ i, i + 1 < N → t i < t (i + 1)) :
    ∀ i j, i < j → j < N → t i < t j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact (ih h (by omega)).trans (ht j hj)
    · subst h; exact ht i hj

/-- Labels are determined by the parity of the number of earlier transitions. -/
theorem label_parity (s : ℕ → Bool) (N : ℕ) :
    ∀ i < N, (s i = s 0 ↔ Even ((transSet s N).filter (· < i)).card) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    have hsplit : (transSet s N).filter (· < i + 1) =
        if i ∈ transSet s N then insert i ((transSet s N).filter (· < i))
        else (transSet s N).filter (· < i) := by
      ext j
      split_ifs with h
      · simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hj, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
          · exact Or.inr ⟨hj, h'⟩
          · exact Or.inl h'
        · rintro (rfl | ⟨hj, hlt⟩)
          · exact ⟨h, Nat.lt_succ_self _⟩
          · exact ⟨hj, by omega⟩
      · simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hj, hlt⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
          · exact ⟨hj, h'⟩
          · subst h'; exact absurd hj h
        · rintro ⟨hj, hlt⟩; exact ⟨hj, by omega⟩
    rw [hsplit]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), Nat.even_add_one, ← ih']
      have hne := (mem_transSet.1 h).2
      cases h0 : s 0 <;> cases hi' : s i <;> cases hi1 : s (i + 1) <;> simp_all
    · rw [← ih']
      have : s i = s (i + 1) := by
        by_contra hc; exact h (mem_transSet.2 ⟨by omega, hc⟩)
      rw [this]

/-- The cyclic transition number is even. -/
theorem even_cycTrans (s : ℕ → Bool) (N : ℕ) : Even (cycTrans s N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cycTrans, trans, transSet]
  have hp := label_parity s N (N - 1) (by omega)
  have hfil : (transSet s N).filter (· < N - 1) = transSet s N := by
    apply Finset.filter_true_of_mem
    intro j hj; have := (mem_transSet.1 hj).1; omega
  rw [hfil] at hp
  unfold cycTrans trans
  by_cases h : s (N - 1) = s 0
  · simp only [hN, ne_eq, h, not_true_eq_false, and_false, if_false, add_zero]
    exact hp.1 h
  · simp only [hN, ne_eq, h, not_false_eq_true, and_self, if_true]
    have : ¬ Even (transSet s N).card := fun he => h (hp.2 he)
    rw [Nat.not_even_iff_odd] at this
    exact this.add_one

/-! ### Lower bounds: counting forced roots -/

/-- **Core lower bound.** A univariate polynomial of degree `≤ k` whose signs at the increasing
nodes `t_0 < … < t_{N-1}` realise the labels has at least `R` roots, so `R ≤ k`. -/
theorem trans_le_natDegree (q : Polynomial ℝ) (t : ℕ → ℝ) (s : ℕ → Bool) (N k : ℕ)
    (ht : ∀ i, i + 1 < N → t i < t (i + 1)) (hq : q.natDegree ≤ k)
    (hsign : ∀ i < N, (s i = true → 0 < q.eval (t i)) ∧ (s i = false → q.eval (t i) < 0)) :
    trans s N ≤ k := by
  classical
  have hroot : ∀ j ∈ transSet s N, ∃ r ∈ Set.Ioo (t j) (t (j + 1)), q.eval r = 0 := by
    intro j hj
    obtain ⟨hjN, hne⟩ := mem_transSet.1 hj
    have hc : ContinuousOn (fun x => q.eval x) (Set.Icc (t j) (t (j + 1))) :=
      q.continuous.continuousOn
    have hle := (ht j hjN).le
    cases hsj : s j
    · have h1 : s (j + 1) = true := by cases h' : s (j + 1) <;> simp_all
      have a1 := (hsign j (by omega)).2 hsj
      have a2 := (hsign (j + 1) hjN).1 h1
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo hle hc ⟨a1, a2⟩
      exact ⟨r, hr, hr0⟩
    · have h1 : s (j + 1) = false := by cases h' : s (j + 1) <;> simp_all
      have a1 := (hsign j (by omega)).1 hsj
      have a2 := (hsign (j + 1) hjN).2 h1
      obtain ⟨r, hr, hr0⟩ := intermediate_value_Ioo' hle hc ⟨a2, a1⟩
      exact ⟨r, hr, hr0⟩
  choose! r hr hr0 using hroot
  have hmono := mono_of_succ ht
  have hinj : Set.InjOn r (transSet s N) := by
    intro i hi j hj hij
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := (hr i hi).2
      have := (hr j hj).1
      have hj1 := (mem_transSet.1 hj).1
      have : t (i + 1) ≤ t j := by
        rcases Nat.lt_or_ge (i + 1) j with h' | h'
        · exact (hmono _ _ h' (by omega)).le
        · have : i + 1 = j := by omega
          rw [this]
      linarith
    · have := (hr j hj).2
      have := (hr i hi).1
      have hi1 := (mem_transSet.1 hi).1
      have : t (j + 1) ≤ t i := by
        rcases Nat.lt_or_ge (j + 1) i with h' | h'
        · exact (hmono _ _ h' (by omega)).le
        · have : j + 1 = i := by omega
          rw [this]
      linarith
  by_cases hT : (transSet s N).Nonempty
  · obtain ⟨j0, hj0⟩ := hT
    have hq0 : q ≠ 0 := by
      intro h0
      have hj0N := (mem_transSet.1 hj0).1
      have := hsign j0 (by omega)
      cases hs : s j0
      · have := this.2 hs; rw [h0] at this; simp at this
      · have := this.1 hs; rw [h0] at this; simp at this
    have hsub : ((transSet s N).image r).val ⊆ q.roots := by
      intro x hx
      rw [Finset.mem_val, Finset.mem_image] at hx
      obtain ⟨j, hj, rfl⟩ := hx
      exact (Polynomial.mem_roots hq0).2 (hr0 j hj)
    have := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_image_of_injOn hinj] at this
    exact this.trans hq
  · rw [Finset.not_nonempty_iff_eq_empty] at hT
    simp [trans, hT]

/-- Substituting a rational parametrisation `(n₀/h, n₁/h)` into `P` and clearing the
denominator `h^d`. -/
def substPoly (n : Fin 2 → Polynomial ℝ) (h : Polynomial ℝ) (d : ℕ) (P : Poly) :
    Polynomial ℝ :=
  ∑ m ∈ P.support, Polynomial.C (coeff m P) * ((n 0) ^ (m 0) * (n 1) ^ (m 1) * h ^ (d - (m 0 + m 1)))

theorem support_deg_le {P : Poly} {d : ℕ} (hP : P.totalDegree ≤ d) {m : Fin 2 →₀ ℕ}
    (hm : m ∈ P.support) : m 0 + m 1 ≤ d := by
  have := le_totalDegree hm
  rw [Finsupp.sum_fintype _ _ (by simp), Fin.sum_univ_two] at this
  exact this.trans hP

theorem natDegree_substPoly_le {n : Fin 2 → Polynomial ℝ} {h : Polynomial ℝ} {k d : ℕ}
    (hn : ∀ i, (n i).natDegree ≤ k) (hh : h.natDegree ≤ k) {P : Poly} (hP : P.totalDegree ≤ d) :
    (substPoly n h d P).natDegree ≤ k * d := by
  unfold substPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  have hmd := support_deg_le hP hm
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_mul_le).trans ?_
  refine (add_le_add (Polynomial.natDegree_mul_le) (Polynomial.natDegree_pow_le)).trans ?_
  refine (add_le_add (add_le_add Polynomial.natDegree_pow_le Polynomial.natDegree_pow_le)
    le_rfl).trans ?_
  have e1 := Nat.mul_le_mul_left (m 0) (hn 0)
  have e2 := Nat.mul_le_mul_left (m 1) (hn 1)
  have e3 := Nat.mul_le_mul_left (d - (m 0 + m 1)) hh
  calc m 0 * (n 0).natDegree + m 1 * (n 1).natDegree + (d - (m 0 + m 1)) * h.natDegree
      ≤ m 0 * k + m 1 * k + (d - (m 0 + m 1)) * k := by omega
    _ = (m 0 + m 1 + (d - (m 0 + m 1))) * k := by ring
    _ = k * d := by rw [Nat.add_sub_cancel' hmd, mul_comm]

theorem eval_substPoly (n : Fin 2 → Polynomial ℝ) (h : Polynomial ℝ) {d : ℕ} {P : Poly}
    (hP : P.totalDegree ≤ d) (u : ℝ) (hu : h.eval u ≠ 0) :
    (substPoly n h d P).eval u = h.eval u ^ d * eval (fun i => (n i).eval u / h.eval u) P := by
  unfold substPoly
  rw [eval_eq', Polynomial.eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd := support_deg_le hP hm
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Fin.prod_univ_two,
    div_pow]
  have : h.eval u ^ d = h.eval u ^ (m 0) * h.eval u ^ (m 1) * h.eval u ^ (d - (m 0 + m 1)) := by
    rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hmd]
  rw [this]
  field_simp

/-- **Rational-curve transition lower bound** (formal substitute for Theorem 4.4 on curves with
a rational parametrisation of degree `k`): if the observations are `γ i = (n₀(t_i)/h(t_i),
n₁(t_i)/h(t_i))` with `h(t_i) > 0` and increasing parameters, any degree-`d` separator forces
`R ≤ k d`. -/
theorem trans_le_of_rational (n : Fin 2 → Polynomial ℝ) (h : Polynomial ℝ) (k : ℕ)
    (hn : ∀ i, (n i).natDegree ≤ k) (hh : h.natDegree ≤ k) (t : ℕ → ℝ) (s : ℕ → Bool) (N d : ℕ)
    (ht : ∀ i, i + 1 < N → t i < t (i + 1)) (hpos : ∀ i < N, 0 < h.eval (t i))
    (γ : ℕ → Plane) (hγ : ∀ i < N, γ i = fun j => (n j).eval (t i) / h.eval (t i))
    (hsep : PolySep d (posPts γ s N) (negPts γ s N)) : trans s N ≤ k * d := by
  obtain ⟨P, hP, hreal⟩ := (polySep_iff_realizes d γ s N).1 hsep
  refine trans_le_natDegree (substPoly n h d P) t s N (k * d) ht
    (natDegree_substPoly_le hn hh hP) fun i hi => ?_
  rw [eval_substPoly n h hP _ (hpos i hi).ne', ← hγ i hi]
  have hp := pow_pos (hpos i hi) d
  exact ⟨fun hs => mul_pos hp ((hreal i hi).1 hs),
    fun hs => mul_neg_of_pos_of_neg hp ((hreal i hi).2 hs)⟩

/-! ### Upper bounds: sign patterns and paired products -/

/-- Midpoint cut values in the transition intervals. -/
def cutPt (t : ℕ → ℝ) (j : ℕ) : ℝ := (t j + t (j + 1)) / 2

theorem prod_neg_sign (l : List ℝ) (x : ℝ) (hl : ∀ e ∈ l, x < e) :
    0 < (-1) ^ l.length * (l.map (fun e => x - e)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ih' := ih fun e he => hl e (by simp [he])
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    have : (-1 : ℝ) ^ l.length * -1 * ((x - a) * (l.map (fun e => x - e)).prod) =
        ((-1) ^ l.length * (l.map (fun e => x - e)).prod) * (a - x) := by ring
    rw [this]
    exact mul_pos ih' (by linarith)

/-- **Sign construction.** With cuts at the midpoints of the transition intervals, followed by
extra cuts `E` beyond all nodes, a suitable constant `σ` times `∏ (t - cut)` realises the
labels. -/
theorem sign_construction (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ)
    (ht : ∀ i, i + 1 < N → t i < t (i + 1)) (E : List ℝ) (hE : ∀ e ∈ E, ∀ i < N, t i < e) :
    ∃ σ : ℝ, ∀ i < N,
      (s i = true → 0 < σ * ((((transSet s N).toList.map (cutPt t)) ++ E).map
        (fun x => t i - x)).prod) ∧
      (s i = false → σ * ((((transSet s N).toList.map (cutPt t)) ++ E).map
        (fun x => t i - x)).prod < 0) := by
  classical
  set J := transSet s N
  have hmono := mono_of_succ ht
  refine ⟨(if s 0 then 1 else -1) * (-1) ^ (J.card + E.length), fun i hi => ?_⟩
  have hprod : ((J.toList.map (cutPt t) ++ E).map (fun x => t i - x)).prod =
      (∏ j ∈ J.filter (· < i), (t i - cutPt t j)) *
        ((-1) ^ (J.filter (fun j => ¬ j < i)).card *
          ∏ j ∈ J.filter (fun j => ¬ j < i), (cutPt t j - t i)) *
        (E.map (fun x => t i - x)).prod := by
    rw [List.map_append, List.prod_append, List.map_map, Finset.prod_map_toList,
      ← Finset.prod_filter_mul_prod_filter_not J (· < i), ← Finset.prod_neg]
    simp
  have hA : 0 < ∏ j ∈ J.filter (· < i), (t i - cutPt t j) := by
    refine Finset.prod_pos fun j hj => ?_
    rw [Finset.mem_filter] at hj
    have hj1 := (mem_transSet.1 hj.1).1
    have h1 := ht j hj1
    have h2 : t (j + 1) ≤ t i := by
      rcases Nat.lt_or_ge (j + 1) i with h' | h'
      · exact (hmono _ _ h' hi).le
      · have : j + 1 = i := by omega
        rw [this]
    unfold cutPt; linarith
  have hB : 0 < ∏ j ∈ J.filter (fun j => ¬ j < i), (cutPt t j - t i) := by
    refine Finset.prod_pos fun j hj => ?_
    rw [Finset.mem_filter] at hj
    have hj1 := (mem_transSet.1 hj.1).1
    have h1 := ht j hj1
    have h2 : t i ≤ t j := by
      rcases Nat.lt_or_ge i j with h' | h'
      · exact (hmono _ _ h' (by omega)).le
      · have : i = j := by omega
        rw [this]
    unfold cutPt; linarith
  have hC := prod_neg_sign E (t i) (fun e he => hE e he i hi)
  have hcard : (J.filter (· < i)).card + (J.filter (fun j => ¬ j < i)).card = J.card :=
    Finset.card_filter_add_card_filter_not _
  have hpar := label_parity s N i hi
  set a := (J.filter (· < i)).card
  set b := (J.filter (fun j => ¬ j < i)).card
  set M := (∏ j ∈ J.filter (· < i), (t i - cutPt t j)) *
    (∏ j ∈ J.filter (fun j => ¬ j < i), (cutPt t j - t i)) *
    ((-1) ^ E.length * (E.map (fun x => t i - x)).prod)
  have hM : 0 < M := mul_pos (mul_pos hA hB) hC
  have key : (if s 0 then (1 : ℝ) else -1) * (-1) ^ (J.card + E.length) *
      ((J.toList.map (cutPt t) ++ E).map (fun x => t i - x)).prod =
      (if s 0 then (1 : ℝ) else -1) * (-1) ^ a * M := by
    rw [hprod, ← hcard]
    simp only [M]
    have e2 : ((-1 : ℝ) ^ b) * (-1) ^ b = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; simp
    calc (if s 0 then (1 : ℝ) else -1) * (-1) ^ (a + b + E.length) *
          ((∏ j ∈ J.filter (· < i), (t i - cutPt t j)) *
            ((-1) ^ b * ∏ j ∈ J.filter (fun j => ¬ j < i), (cutPt t j - t i)) *
            (E.map (fun x => t i - x)).prod)
        = (if s 0 then (1 : ℝ) else -1) * (-1) ^ a * (((-1 : ℝ) ^ b) * (-1) ^ b) *
          ((∏ j ∈ J.filter (· < i), (t i - cutPt t j)) *
            (∏ j ∈ J.filter (fun j => ¬ j < i), (cutPt t j - t i)) *
            ((-1) ^ E.length * (E.map (fun x => t i - x)).prod)) := by
          rw [pow_add, pow_add]; ring
      _ = _ := by rw [e2]; ring
  rw [key]
  rcases Nat.even_or_odd a with hae | hao
  · rw [hae.neg_one_pow]
    have hs := hpar.2 hae
    constructor
    · intro hsi; rw [hsi] at hs; rw [← hs]; simp [hM]
    · intro hsi; rw [hsi] at hs; rw [← hs]; simp [hM]
  · rw [hao.neg_one_pow]
    have hs : s i ≠ s 0 := fun h => (Nat.not_even_iff_odd.2 hao) (hpar.1 h)
    constructor
    · intro hsi; rw [hsi] at hs
      have : s 0 = false := by cases h : s 0 <;> simp_all
      simp [this, hM]
    · intro hsi; rw [hsi] at hs
      have : s 0 = true := by cases h : s 0 <;> simp_all
      simp [this, hM]

theorem cutPt_mem (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ) (ht : ∀ i, i + 1 < N → t i < t (i + 1))
    {j : ℕ} (hj : j ∈ transSet s N) : t j < cutPt t j ∧ cutPt t j < t (j + 1) := by
  have := ht j (mem_transSet.1 hj).1
  unfold cutPt; constructor <;> linarith

theorem cutPt_ne (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ) (ht : ∀ i, i + 1 < N → t i < t (i + 1))
    {j i : ℕ} (hj : j ∈ transSet s N) (hi : i < N) : t i ≠ cutPt t j := by
  have hmono := mono_of_succ ht
  obtain ⟨h1, h2⟩ := cutPt_mem t s N ht hj
  have hj1 := (mem_transSet.1 hj).1
  intro heq
  rcases Nat.lt_or_ge j i with h | h
  · have : t (j + 1) ≤ t i := by
      rcases Nat.lt_or_ge (j + 1) i with h' | h'
      · exact (hmono _ _ h' hi).le
      · have : j + 1 = i := by omega
        rw [this]
    linarith
  · have : t i ≤ t j := by
      rcases Nat.lt_or_ge i j with h' | h'
      · exact (hmono _ _ h' (by omega)).le
      · have : i = j := by omega
        rw [this]
    linarith

/-- Products of paired factors: `Q a b` for consecutive pairs and `R a` for a leftover. -/
def pairProd (Q : ℝ → ℝ → Poly) (R : ℝ → Poly) : List ℝ → Poly
  | [] => 1
  | [a] => R a
  | a :: b :: l => Q a b * pairProd Q R l

theorem totalDegree_pairProd (Q : ℝ → ℝ → Poly) (R : ℝ → Poly) (q1 q2 : ℕ)
    (hQ : ∀ a b, (Q a b).totalDegree ≤ q2) (hR : ∀ a, (R a).totalDegree ≤ q1) :
    ∀ L : List ℝ, (pairProd Q R L).totalDegree ≤ q2 * (L.length / 2) + q1 * (L.length % 2)
  | [] => by simp [pairProd]
  | [a] => by simpa [pairProd] using hR a
  | a :: b :: l => by
    have ih := totalDegree_pairProd Q R q1 q2 hQ hR l
    simp only [pairProd, List.length_cons]
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (l.length + 1 + 1) / 2 = l.length / 2 + 1 := by omega
    have h2 : (l.length + 1 + 1) % 2 = l.length % 2 := by omega
    rw [h1, h2]
    have := hQ a b
    nlinarith

theorem pairProd_sign (Q : ℝ → ℝ → Poly) (R : ℝ → Poly) (z : Plane) (x : ℝ) :
    ∀ L : List ℝ, (∀ a ∈ L, ∀ b ∈ L, 0 < eval z (Q a b) * ((x - a) * (x - b))) →
      (Odd L.length → ∀ a ∈ L, 0 < eval z (R a) * (x - a)) →
      0 < eval z (pairProd Q R L) * (L.map (fun e => x - e)).prod
  | [], _, _ => by simp [pairProd]
  | [a], _, hR => by simpa [pairProd] using hR (by simp) a (by simp)
  | a :: b :: l, hQ, hR => by
    have ih := pairProd_sign Q R z x l (fun a' ha b' hb => hQ a' (by simp [ha]) b' (by simp [hb]))
      (fun ho a' ha => hR (by simp only [List.length_cons]; exact ho.add_one.add_one) a'
        (by simp [ha]))
    have hab := hQ a (by simp) b (by simp)
    simp only [pairProd, map_mul, List.map_cons, List.prod_cons]
    have : eval z (Q a b) * eval z (pairProd Q R l) *
        ((x - a) * ((x - b) * (l.map (fun e => x - e)).prod)) =
        (eval z (Q a b) * ((x - a) * (x - b))) *
          (eval z (pairProd Q R l) * (l.map (fun e => x - e)).prod) := by ring
    rw [this]
    exact mul_pos hab ih

/-- Transfer of signs: if `P·Π > 0` and `σ·Π` has the sign of the label, so does `σ·P`. -/
theorem sign_transfer {x y σ : ℝ} (hxy : 0 < x * y) :
    (0 < σ * y → 0 < σ * x) ∧ (σ * y < 0 → σ * x < 0) := by
  have hy : y ≠ 0 := by rintro rfl; simp at hxy
  have hy2 : 0 < y ^ 2 := by positivity
  constructor
  · intro h
    have : 0 < (σ * y) * (x * y) := mul_pos h hxy
    have : 0 < (σ * x) * y ^ 2 := by nlinarith
    exact pos_of_mul_pos_left this hy2.le |> fun h' => by
      rcases lt_or_ge 0 (σ * x) with h1 | h1
      · exact h1
      · nlinarith
  · intro h
    have : (σ * y) * (x * y) < 0 := mul_neg_of_neg_of_pos h hxy
    have : (σ * x) * y ^ 2 < 0 := by nlinarith
    rcases lt_or_ge (σ * x) 0 with h1 | h1
    · exact h1
    · nlinarith

/-- **Generic upper bound.** If along the parameters `t_i` the paired factors have the sign of
the corresponding products of `(t - cut)`, then the labels are realised by a polynomial of degree
`q₂·⌊L/2⌋ + q₁·(L mod 2)` where `L` is the number of cuts. -/
theorem realizes_of_pairs (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ)
    (ht : ∀ i, i + 1 < N → t i < t (i + 1)) (E : List ℝ) (hE : ∀ e ∈ E, ∀ i < N, t i < e)
    (γ : ℕ → Plane) (Q : ℝ → ℝ → Poly) (R : ℝ → Poly) (q1 q2 : ℕ)
    (hQd : ∀ a b, (Q a b).totalDegree ≤ q2) (hRd : ∀ a, (R a).totalDegree ≤ q1)
    (hQ : ∀ i < N, ∀ a ∈ (transSet s N).toList.map (cutPt t) ++ E,
      ∀ b ∈ (transSet s N).toList.map (cutPt t) ++ E,
        0 < eval (γ i) (Q a b) * ((t i - a) * (t i - b)))
    (hR : Odd ((transSet s N).card + E.length) → ∀ i < N,
      ∀ a ∈ (transSet s N).toList.map (cutPt t) ++ E, 0 < eval (γ i) (R a) * (t i - a)) :
    ∃ P : Poly, P.totalDegree ≤ q2 * (((transSet s N).card + E.length) / 2) +
        q1 * (((transSet s N).card + E.length) % 2) ∧ Realizes P γ s N := by
  obtain ⟨σ, hσ⟩ := sign_construction t s N ht E hE
  set L := (transSet s N).toList.map (cutPt t) ++ E
  have hlen : L.length = (transSet s N).card + E.length := by simp [L]
  refine ⟨C σ * pairProd Q R L, ?_, fun i hi => ?_⟩
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add, ← hlen]
    exact totalDegree_pairProd Q R q1 q2 hQd hRd L
  · have hpos := pairProd_sign Q R (γ i) (t i) L (hQ i hi)
      (fun ho => hR (hlen ▸ ho) i hi)
    have tr := sign_transfer (σ := σ) hpos
    simp only [map_mul, eval_C]
    exact ⟨fun hs => tr.1 ((hσ i hi).1 hs), fun hs => tr.2 ((hσ i hi).2 hs)⟩

/-! ## Affine invariance; line, parabola and hyperbola laws (Sections 4–5) -/

/-! ### Affine invariance (Proposition 5.1) -/

/-- Substitution `P(g₀, g₁)` of two polynomials into `P`. -/
def affSubst (g : Fin 2 → Poly) (P : Poly) : Poly :=
  ∑ m ∈ P.support, C (coeff m P) * ∏ i, g i ^ m i

theorem eval_affSubst (g : Fin 2 → Poly) (P : Poly) (z : Plane) :
    eval z (affSubst g P) = eval (fun i => eval z (g i)) P := by
  rw [eval_eq' (fun i => eval z (g i)) P]
  simp [affSubst, map_sum]

theorem totalDegree_affSubst_le (g : Fin 2 → Poly) (hg : ∀ i, (g i).totalDegree ≤ 1) (P : Poly) :
    (affSubst g P).totalDegree ≤ P.totalDegree := by
  unfold affSubst
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  have := le_totalDegree hm
  rw [Finsupp.sum_fintype _ _ (by simp)] at this
  refine le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hg i))) ?_
  simpa using this

/-- Composition of a polynomial with an affine map does not increase the total degree. -/
theorem exists_comp_affine (F : Plane →ᵃ[ℝ] Plane) (P : Poly) :
    ∃ Q : Poly, Q.totalDegree ≤ P.totalDegree ∧ ∀ z, eval z Q = eval (F z) P := by
  classical
  let g : Fin 2 → Poly := fun i =>
    C (F 0 i) + ∑ k, C (F.linear (fun j => if k = j then 1 else 0) i) * X k
  have hg : ∀ i, (g i).totalDegree ≤ 1 := by
    intro i
    refine (totalDegree_add _ _).trans (max_le (by simp) ?_)
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp
  have hF : ∀ z, F z = fun i => eval z (g i) := by
    intro z
    have h1 : F z = F.linear z + F 0 := by
      have := F.linearMap_vsub z 0
      simp only [vsub_eq_sub, sub_zero] at this
      rw [this]; abel
    rw [h1, LinearMap.pi_apply_eq_sum_univ F.linear z]
    funext i
    simp [g, add_comm, mul_comm]
  refine ⟨affSubst g P, totalDegree_affSubst_le g hg P, fun z => ?_⟩
  rw [eval_affSubst, hF]

/-- Degree-`d` separability is invariant under invertible affine maps. -/
theorem polySep_image_iff (T : Plane ≃ᵃ[ℝ] Plane) (d : ℕ) (A B : Set Plane) :
    PolySep d (T '' A) (T '' B) ↔ PolySep d A B := by
  constructor
  · rintro ⟨P, hP, h1, h2⟩
    obtain ⟨Q, hQ, hQe⟩ := exists_comp_affine T.toAffineMap P
    refine ⟨Q, hQ.trans hP, fun a ha => ?_, fun b hb => ?_⟩
    · rw [hQe]; exact h1 _ ⟨a, ha, rfl⟩
    · rw [hQe]; exact h2 _ ⟨b, hb, rfl⟩
  · rintro ⟨P, hP, h1, h2⟩
    obtain ⟨Q, hQ, hQe⟩ := exists_comp_affine T.symm.toAffineMap P
    refine ⟨Q, hQ.trans hP, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩; rw [hQe]; simpa using h1 a ha
    · rintro _ ⟨b, hb, rfl⟩; rw [hQe]; simpa using h2 b hb

/-- **Proposition 5.1 (affine invariance).** `d_*(T(A), T(B)) = d_*(A, B)`. -/
theorem sepDegree_affine_invariant (T : Plane ≃ᵃ[ℝ] Plane) (A B : Set Plane) :
    sepDegree (T '' A) (T '' B) = sepDegree A B := by
  unfold sepDegree
  congr 1
  ext d
  exact polySep_image_iff T d A B

theorem image_posPts (T : Plane → Plane) (γ : ℕ → Plane) (s : ℕ → Bool) (N : ℕ) :
    T '' posPts γ s N = posPts (fun i => T (γ i)) s N := by
  ext z; simp only [posPts, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨i, hi, hs, rfl⟩, rfl⟩; exact ⟨i, hi, hs, rfl⟩
  · rintro ⟨i, hi, hs, rfl⟩; exact ⟨_, ⟨i, hi, hs, rfl⟩, rfl⟩

theorem image_negPts (T : Plane → Plane) (γ : ℕ → Plane) (s : ℕ → Bool) (N : ℕ) :
    T '' negPts γ s N = negPts (fun i => T (γ i)) s N := by
  ext z; simp only [negPts, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨_, ⟨i, hi, hs, rfl⟩, rfl⟩; exact ⟨i, hi, hs, rfl⟩
  · rintro ⟨i, hi, hs, rfl⟩; exact ⟨_, ⟨i, hi, hs, rfl⟩, rfl⟩

/-- Affine invariance for indexed samples. -/
theorem sepDegree_affine_sample (T : Plane ≃ᵃ[ℝ] Plane) (γ : ℕ → Plane) (s : ℕ → Bool)
    (N : ℕ) :
    sepDegree (posPts (fun i => T (γ i)) s N) (negPts (fun i => T (γ i)) s N) =
      sepDegree (posPts γ s N) (negPts γ s N) := by
  rw [← image_posPts, ← image_negPts, sepDegree_affine_invariant]

/-! ### Assembling exact laws from lower and upper bounds -/

theorem sepDegree_eq_of_bounds (γ : ℕ → Plane) (s : ℕ → Bool) (N D : ℕ)
    (hup : PolySep D (posPts γ s N) (negPts γ s N))
    (hlow : ∀ d, PolySep d (posPts γ s N) (negPts γ s N) → D ≤ d) :
    sepDegree (posPts γ s N) (negPts γ s N) = D :=
  le_antisymm ((sepDegree_le_iff ⟨D, hup⟩).2 hup) (hlow _ (polySep_sepDegree ⟨D, hup⟩))

/-! ### Collinear data (Theorem 4.1) -/

/-- The affine parameter `ℓ(z) = (z - p₀)·v / ‖v‖²` along the line `p₀ + t v`. -/
def lineParam (p0 v : Plane) : Poly :=
  C (1 / ∑ k, v k ^ 2) * ∑ k, C (v k) * (X k - C (p0 k))

theorem totalDegree_lineParam_le (p0 v : Plane) : (lineParam p0 v).totalDegree ≤ 1 := by
  unfold lineParam
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_sub _ _).trans ?_
  simp

theorem eval_lineParam (p0 v : Plane) (hv : v ≠ 0) (t : ℝ) :
    eval (p0 + t • v) (lineParam p0 v) = t := by
  have hpos : 0 < ∑ k, v k ^ 2 := by
    have := sqDist_pos hv
    simpa [sqDist] using this
  simp only [lineParam, map_mul, eval_C, map_sum, map_sub, eval_X, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, add_sub_cancel_left]
  have : ∑ k, v k * (t * v k) = t * ∑ k, v k ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  field_simp

/-- **Theorem 4.1 (exact line transition law).** For labelled points `p₀ + t_i v` (with `v ≠ 0`)
ordered along a line, `t_0 < t_1 < ⋯ < t_{N-1}`, the algebraic separation degree equals the
number `R` of adjacent label changes. -/
theorem line_law (p0 v : Plane) (hv : v ≠ 0) (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ)
    (ht : ∀ i, i + 1 < N → t i < t (i + 1)) :
    sepDegree (posPts (fun i => p0 + t i • v) s N) (negPts (fun i => p0 + t i • v) s N) =
      trans s N := by
  set γ : ℕ → Plane := fun i => p0 + t i • v
  apply sepDegree_eq_of_bounds
  · -- upper bound: product of `R` affine factors
    rw [polySep_iff_realizes]
    let ℓ := lineParam p0 v
    obtain ⟨P, hP, hreal⟩ := realizes_of_pairs t s N ht [] (by simp) γ
      (fun a b => (ℓ - C a) * (ℓ - C b)) (fun a => ℓ - C a) 1 2
      (fun a b => by
        refine (totalDegree_mul _ _).trans ?_
        have h1 : (ℓ - C a).totalDegree ≤ 1 :=
          (totalDegree_sub _ _).trans (max_le (totalDegree_lineParam_le p0 v) (by simp))
        have h2 : (ℓ - C b).totalDegree ≤ 1 :=
          (totalDegree_sub _ _).trans (max_le (totalDegree_lineParam_le p0 v) (by simp))
        omega)
      (fun a => (totalDegree_sub _ _).trans (max_le (totalDegree_lineParam_le p0 v) (by simp)))
      (fun i hi a ha b hb => by
        simp only [List.append_nil, List.mem_map, Finset.mem_toList] at ha hb
        obtain ⟨j, hj, rfl⟩ := ha
        obtain ⟨j', hj', rfl⟩ := hb
        simp only [map_mul, map_sub, eval_C, γ, ℓ, eval_lineParam p0 v hv]
        have h1 := sub_ne_zero.2 (cutPt_ne t s N ht hj hi)
        have h2 := sub_ne_zero.2 (cutPt_ne t s N ht hj' hi)
        have : 0 < ((t i - cutPt t j) * (t i - cutPt t j')) ^ 2 := by positivity
        nlinarith)
      (fun _ i hi a ha => by
        simp only [List.append_nil, List.mem_map, Finset.mem_toList] at ha
        obtain ⟨j, hj, rfl⟩ := ha
        simp only [map_sub, eval_C, γ, ℓ, eval_lineParam p0 v hv]
        have h1 := sub_ne_zero.2 (cutPt_ne t s N ht hj hi)
        have : 0 < (t i - cutPt t j) ^ 2 := by positivity
        nlinarith)
    refine ⟨P, hP.trans ?_, hreal⟩
    simp only [List.length_nil, add_zero]
    unfold trans; omega
  · -- lower bound: restriction to the line has at least `R` roots
    intro d hd
    have := trans_le_of_rational (fun j => Polynomial.C (p0 j) + Polynomial.C (v j) * Polynomial.X)
      1 1 (fun j => by
        refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
        exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp))
      (by simp) t s N d ht (by simp) γ (fun i _ => by
        funext j; simp [γ]; ring) hd
    simpa using this

/-! ### Parabola `y = x²` -/

/-- **Theorem 4.2, parabola case.** For labelled points `(t_i, t_i²)` with increasing `t_i`,
`d_* = ⌈R/2⌉`, written `(R + 1) / 2` in natural-number arithmetic. -/
theorem parabola_law (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ) (ht : ∀ i, i + 1 < N → t i < t (i + 1)) :
    sepDegree (posPts (fun i => ![t i, t i ^ 2]) s N) (negPts (fun i => ![t i, t i ^ 2]) s N) =
      (trans s N + 1) / 2 := by
  set γ : ℕ → Plane := fun i => ![t i, t i ^ 2]
  apply sepDegree_eq_of_bounds
  · rw [polySep_iff_realizes]
    have hRd : ∀ a : ℝ, (X 0 - C a : Poly).totalDegree ≤ 1 := fun a =>
      (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
    obtain ⟨P, hP, hreal⟩ := realizes_of_pairs t s N ht [] (by simp) γ
      (fun a b => X 1 - C (a + b) * X 0 + C (a * b)) (fun a => X 0 - C a) 1 1
      (fun a b => by
        refine (totalDegree_add _ _).trans (max_le ?_ (by rw [totalDegree_C]; omega))
        refine (totalDegree_sub _ _).trans (max_le (by simp) ?_)
        refine (totalDegree_mul _ _).trans ?_
        rw [totalDegree_C, totalDegree_X])
      hRd
      (fun i hi a ha b hb => by
        simp only [List.append_nil, List.mem_map, Finset.mem_toList] at ha hb
        obtain ⟨j, hj, rfl⟩ := ha
        obtain ⟨j', hj', rfl⟩ := hb
        simp only [map_add, map_sub, map_mul, eval_C, eval_X, γ, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        have h1 := sub_ne_zero.2 (cutPt_ne t s N ht hj hi)
        have h2 := sub_ne_zero.2 (cutPt_ne t s N ht hj' hi)
        have : 0 < ((t i - cutPt t j) * (t i - cutPt t j')) ^ 2 := by positivity
        nlinarith)
      (fun _ i hi a ha => by
        simp only [List.append_nil, List.mem_map, Finset.mem_toList] at ha
        obtain ⟨j, hj, rfl⟩ := ha
        simp only [map_sub, eval_C, eval_X, γ, Matrix.cons_val_zero]
        have h1 := sub_ne_zero.2 (cutPt_ne t s N ht hj hi)
        have : 0 < (t i - cutPt t j) ^ 2 := by positivity
        nlinarith)
    refine ⟨P, hP.trans ?_, hreal⟩
    simp only [List.length_nil, add_zero]
    unfold trans; omega
  · intro d hd
    have := trans_le_of_rational ![Polynomial.X, Polynomial.X ^ 2] 1 2
      (fun j => by
        fin_cases j
        · simp
        · simp)
      (by simp) t s N d ht (by simp) γ (fun i _ => by
        funext j; fin_cases j <;> simp [γ]) hd
    omega

/-! ### Hyperbola branch `xy = 1`, `x > 0` -/

/-- **Theorem 4.2, hyperbola case.** For labelled points `(t_i, 1/t_i)` with
`0 < t_0 < ⋯ < t_{N-1}` on one branch of `xy = 1`, `d_* = ⌈R/2⌉ = (R + 1) / 2`. -/
theorem hyperbola_law (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ) (ht : ∀ i, i + 1 < N → t i < t (i + 1))
    (htpos : ∀ i < N, 0 < t i) :
    sepDegree (posPts (fun i => ![t i, 1 / t i]) s N) (negPts (fun i => ![t i, 1 / t i]) s N) =
      (trans s N + 1) / 2 := by
  set γ : ℕ → Plane := fun i => ![t i, 1 / t i]
  apply sepDegree_eq_of_bounds
  · rw [polySep_iff_realizes]
    have hRd : ∀ a : ℝ, (X 0 - C a : Poly).totalDegree ≤ 1 := fun a =>
      (totalDegree_sub _ _).trans (max_le (by simp) (by simp))
    obtain ⟨P, hP, hreal⟩ := realizes_of_pairs t s N ht [] (by simp) γ
      (fun a b => X 0 - C (a + b) + C (a * b) * X 1) (fun a => X 0 - C a) 1 1
      (fun a b => by
        refine (totalDegree_add _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_sub _ _).trans (max_le (by simp) (by rw [totalDegree_C]; omega))
        · refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_C, totalDegree_X])
      hRd
      (fun i hi a ha b hb => by
        simp only [List.append_nil, List.mem_map, Finset.mem_toList] at ha hb
        obtain ⟨j, hj, rfl⟩ := ha
        obtain ⟨j', hj', rfl⟩ := hb
        simp only [map_add, map_sub, map_mul, eval_C, eval_X, γ, Matrix.cons_val_zero,
          Matrix.cons_val_one]
        have h1 := sub_ne_zero.2 (cutPt_ne t s N ht hj hi)
        have h2 := sub_ne_zero.2 (cutPt_ne t s N ht hj' hi)
        have htp := htpos i hi
        have e : t i - (cutPt t j + cutPt t j') + cutPt t j * cutPt t j' * (1 / t i) =
            (t i - cutPt t j) * (t i - cutPt t j') / t i := by
          field_simp; ring
        rw [e]
        have : 0 < ((t i - cutPt t j) * (t i - cutPt t j')) ^ 2 / t i := by positivity
        calc (0 : ℝ) < ((t i - cutPt t j) * (t i - cutPt t j')) ^ 2 / t i := this
          _ = _ := by ring)
      (fun _ i hi a ha => by
        simp only [List.append_nil, List.mem_map, Finset.mem_toList] at ha
        obtain ⟨j, hj, rfl⟩ := ha
        simp only [map_sub, eval_C, eval_X, γ, Matrix.cons_val_zero]
        have h1 := sub_ne_zero.2 (cutPt_ne t s N ht hj hi)
        have : 0 < (t i - cutPt t j) ^ 2 := by positivity
        nlinarith)
    refine ⟨P, hP.trans ?_, hreal⟩
    simp only [List.length_nil, add_zero]
    unfold trans; omega
  · intro d hd
    have := trans_le_of_rational ![Polynomial.X ^ 2, 1] Polynomial.X 2
      (fun j => by
        fin_cases j
        · simp
        · simp)
      (by simp) t s N d ht (by simpa using htpos) γ (fun i hi => by
        have htp := htpos i hi
        funext j; fin_cases j
        · simp [γ]; field_simp
        · simp [γ]) hd
    omega

/-! ## Circle and ellipse laws (Section 4) -/

/-! ### Circle and ellipse (Theorem 4.2, compact case; Corollary 4.3) -/

theorem sin_half_mul_pos {y : ℝ} (h1 : -(2 * π) < y) (h2 : y < 2 * π) (h0 : y ≠ 0) :
    0 < Real.sin (y / 2) * y := by
  rcases lt_or_gt_of_ne h0 with h | h
  · have : Real.sin (y / 2) < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
    exact mul_pos_of_neg_of_neg this h
  · have : 0 < Real.sin (y / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    exact mul_pos this h

/-- The chord line through the points of angles `a` and `b` on the unit circle. -/
def chordPoly (a b : ℝ) : Poly :=
  C (Real.cos ((a - b) / 2)) - C (Real.cos ((a + b) / 2)) * X 0 - C (Real.sin ((a + b) / 2)) * X 1

theorem totalDegree_chordPoly_le (a b : ℝ) : (chordPoly a b).totalDegree ≤ 1 := by
  unfold chordPoly
  refine (totalDegree_sub _ _).trans (max_le ((totalDegree_sub _ _).trans (max_le (by simp) ?_)) ?_)
  · exact (totalDegree_mul _ _).trans (by simp)
  · exact (totalDegree_mul _ _).trans (by simp)

theorem eval_chordPoly (a b θ : ℝ) :
    eval ![Real.cos θ, Real.sin θ] (chordPoly a b) =
      2 * Real.sin ((θ - a) / 2) * Real.sin ((θ - b) / 2) := by
  simp only [chordPoly, map_sub, map_mul, eval_C, eval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have e : Real.cos ((a - b) / 2) - Real.cos ((a + b) / 2) * Real.cos θ -
      Real.sin ((a + b) / 2) * Real.sin θ =
      Real.cos ((a - b) / 2) - Real.cos (θ - (a + b) / 2) := by
    rw [Real.cos_sub]; ring
  rw [e, Real.cos_sub_cos]
  have h1 : ((a - b) / 2 + (θ - (a + b) / 2)) / 2 = (θ - b) / 2 := by ring
  have h2 : ((a - b) / 2 - (θ - (a + b) / 2)) / 2 = -((θ - a) / 2) := by ring
  rw [h1, h2, Real.sin_neg]
  ring

theorem cos_two_mul_tan {w : ℝ} (hw : Real.cos w ≠ 0) :
    Real.cos (2 * w) = (1 - Real.tan w ^ 2) / (1 + Real.tan w ^ 2) ∧
      Real.sin (2 * w) = 2 * Real.tan w / (1 + Real.tan w ^ 2) := by
  have hs := Real.sin_sq_add_cos_sq w
  have h1 : 1 + Real.tan w ^ 2 = 1 / Real.cos w ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]; field_simp; linarith
  rw [h1, Real.tan_eq_sin_div_cos, Real.cos_two_mul, Real.sin_two_mul]
  constructor
  · field_simp; linarith
  · field_simp

/-- **Theorem 4.2, compact case (circle).** Let `θ_0 < θ_1 < ⋯ < θ_{N-1} < θ_0 + 2π` be the
angles of `N ≥ 1` labelled points on the unit circle, in cyclic order. Then
`d_* = R_cyc / 2`, where `R_cyc` is the (even) number of cyclic label transitions. -/
theorem circle_law (θ : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ) (hN : 0 < N)
    (ht : ∀ i, i + 1 < N → θ i < θ (i + 1)) (hwin : θ (N - 1) < θ 0 + 2 * π) :
    sepDegree (posPts (fun i => ![Real.cos (θ i), Real.sin (θ i)]) s N)
      (negPts (fun i => ![Real.cos (θ i), Real.sin (θ i)]) s N) = cycTrans s N / 2 := by
  set γ : ℕ → Plane := fun i => ![Real.cos (θ i), Real.sin (θ i)]
  have hmono := mono_of_succ ht
  have hle0 : ∀ i < N, θ 0 ≤ θ i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | h
    · rfl
    · exact (hmono 0 i h hi).le
  have hleN : ∀ i < N, θ i ≤ θ (N - 1) := by
    intro i hi
    rcases Nat.lt_or_ge i (N - 1) with h | h
    · exact (hmono i (N - 1) h (by omega)).le
    · have : i = N - 1 := by omega
      rw [this]
  have hpi := Real.pi_pos
  -- the gap angle
  set ψ : ℝ := (θ (N - 1) + θ 0 + 2 * π) / 2
  have hψ1 : θ (N - 1) < ψ := by simp only [ψ]; linarith
  have hψ2 : ψ < θ 0 + 2 * π := by simp only [ψ]; linarith
  have hθ0N : θ 0 ≤ θ (N - 1) := hle0 (N - 1) (by omega)
  apply sepDegree_eq_of_bounds
  · -- upper bound via chords
    rw [polySep_iff_realizes]
    set E : List ℝ := if s (N - 1) ≠ s 0 then [ψ] else []
    have hE : ∀ e ∈ E, ∀ i < N, θ i < e := by
      intro e he i hi
      simp only [E] at he
      split_ifs at he
      · simp only [List.mem_singleton] at he; subst he; linarith [hleN i hi]
      · simp at he
    have hEw : ∀ e ∈ E, θ 0 < e ∧ e < θ 0 + 2 * π := by
      intro e he
      simp only [E] at he
      split_ifs at he
      · simp only [List.mem_singleton] at he; subst he; constructor <;> linarith
      · simp at he
    have hlen : (transSet s N).card + E.length = cycTrans s N := by
      simp only [E, cycTrans, trans, hN, true_and]
      split_ifs <;> simp
    have hwinL : ∀ i < N, ∀ a ∈ (transSet s N).toList.map (cutPt θ) ++ E,
        -(2 * π) < θ i - a ∧ θ i - a < 2 * π ∧ θ i - a ≠ 0 := by
      intro i hi a ha
      rw [List.mem_append] at ha
      rcases ha with ha | ha
      · simp only [List.mem_map, Finset.mem_toList] at ha
        obtain ⟨j, hj, rfl⟩ := ha
        obtain ⟨c1, c2⟩ := cutPt_mem θ s N ht hj
        have hj1 := (mem_transSet.1 hj).1
        have := hle0 j (by omega)
        have := hleN (j + 1) hj1
        have := hle0 i hi
        have := hleN i hi
        refine ⟨by linarith, by linarith, sub_ne_zero.2 (cutPt_ne θ s N ht hj hi)⟩
      · obtain ⟨e1, e2⟩ := hEw a ha
        have := hE a ha i hi
        have := hle0 i hi
        refine ⟨by linarith, by linarith, by linarith⟩
    obtain ⟨P, hP, hreal⟩ := realizes_of_pairs θ s N ht E hE γ chordPoly (fun a => chordPoly a a)
      1 1 totalDegree_chordPoly_le (fun a => totalDegree_chordPoly_le a a)
      (fun i hi a ha b hb => by
        simp only [γ, eval_chordPoly]
        obtain ⟨a1, a2, a3⟩ := hwinL i hi a ha
        obtain ⟨b1, b2, b3⟩ := hwinL i hi b hb
        have pa := sin_half_mul_pos a1 a2 a3
        have pb := sin_half_mul_pos b1 b2 b3
        have : 2 * Real.sin ((θ i - a) / 2) * Real.sin ((θ i - b) / 2) * ((θ i - a) * (θ i - b)) =
            2 * (Real.sin ((θ i - a) / 2) * (θ i - a)) * (Real.sin ((θ i - b) / 2) * (θ i - b)) := by
          ring
        rw [this]; positivity)
      (fun ho => by
        rw [hlen] at ho
        exact absurd (even_cycTrans s N) (Nat.not_even_iff_odd.2 ho))
    refine ⟨P, hP.trans ?_, hreal⟩
    rw [hlen]
    have := even_cycTrans s N
    obtain ⟨k, hk⟩ := this
    omega
  · -- lower bound via stereographic projection from the gap point
    intro d hd
    set w : ℕ → ℝ := fun i => (θ i - ψ + π) / 2
    have hw : ∀ i < N, w i ∈ Set.Ioo (-(π / 2)) (π / 2) := by
      intro i hi
      have := hle0 i hi
      have := hleN i hi
      simp only [w, Set.mem_Ioo]
      constructor <;> linarith
    set u : ℕ → ℝ := fun i => Real.tan (w i)
    have hu : ∀ i, i + 1 < N → u i < u (i + 1) := by
      intro i hi
      refine Real.strictMonoOn_tan (hw i (by omega)) (hw (i + 1) hi) ?_
      simp only [w]; linarith [ht i hi]
    let n : Fin 2 → Polynomial ℝ :=
      ![Polynomial.C (-Real.cos ψ) * (1 - Polynomial.X ^ 2) +
          Polynomial.C (2 * Real.sin ψ) * Polynomial.X,
        Polynomial.C (-Real.sin ψ) * (1 - Polynomial.X ^ 2) -
          Polynomial.C (2 * Real.cos ψ) * Polynomial.X]
    have hd1 : ∀ a b : ℝ, (Polynomial.C a * (1 - Polynomial.X ^ 2) +
        Polynomial.C b * Polynomial.X : Polynomial ℝ).natDegree ≤ 2 := by
      intro a b; compute_degree!
    have hd2 : ∀ a b : ℝ, (Polynomial.C a * (1 - Polynomial.X ^ 2) -
        Polynomial.C b * Polynomial.X : Polynomial ℝ).natDegree ≤ 2 := by
      intro a b; compute_degree!
    have hn : ∀ j, (n j).natDegree ≤ 2 := by
      intro j; fin_cases j
      · exact hd1 _ _
      · exact hd2 _ _
    have hh : (1 + Polynomial.X ^ 2 : Polynomial ℝ).natDegree ≤ 2 := by compute_degree
    have := trans_le_of_rational n (1 + Polynomial.X ^ 2) 2 hn hh u s N d hu
      (fun i _ => by simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_pow,
        Polynomial.eval_X]; positivity) γ
      (fun i hi => by
        have hcw : Real.cos (w i) ≠ 0 := (Real.cos_pos_of_mem_Ioo (hw i hi)).ne'
        obtain ⟨c2, s2⟩ := cos_two_mul_tan hcw
        have hθ : θ i = 2 * w i + ψ - π := by simp only [w]; ring
        have hden : (0 : ℝ) < 1 + u i ^ 2 := by positivity
        funext j; fin_cases j
        · simp only [γ, n, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one,
            Polynomial.eval_pow, Polynomial.eval_X]
          rw [hθ, Real.cos_sub_pi, Real.cos_add, c2, s2]
          simp only [u]
          field_simp
          ring
        · simp only [γ, n, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_one,
            Polynomial.eval_pow, Polynomial.eval_X, Matrix.cons_val_zero]
          rw [hθ, Real.sin_sub_pi, Real.sin_add, c2, s2]
          simp only [u]
          field_simp
          ring) hd
    have hcyc : cycTrans s N ≤ trans s N + 1 := by
      unfold cycTrans; split_ifs <;> omega
    have := even_cycTrans s N
    obtain ⟨k, hk⟩ := this
    omega

/-- **Corollary 4.3 / Theorem 4.2 for ellipses.** For labelled points on an ellipse — the image
`T(cos θ_i, sin θ_i)` of the unit circle under an invertible affine map `T` — in cyclic order,
`d_* = R_cyc / 2`. -/
theorem ellipse_law (T : Plane ≃ᵃ[ℝ] Plane) (θ : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ) (hN : 0 < N)
    (ht : ∀ i, i + 1 < N → θ i < θ (i + 1)) (hwin : θ (N - 1) < θ 0 + 2 * π) :
    sepDegree (posPts (fun i => T ![Real.cos (θ i), Real.sin (θ i)]) s N)
      (negPts (fun i => T ![Real.cos (θ i), Real.sin (θ i)]) s N) = cycTrans s N / 2 := by
  rw [sepDegree_affine_sample T (fun i => ![Real.cos (θ i), Real.sin (θ i)])]
  exact circle_law θ s N hN ht hwin

/-- Theorem 4.2 for affine images of the parabola `y = x²`. -/
theorem affine_parabola_law (T : Plane ≃ᵃ[ℝ] Plane) (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ)
    (ht : ∀ i, i + 1 < N → t i < t (i + 1)) :
    sepDegree (posPts (fun i => T ![t i, t i ^ 2]) s N) (negPts (fun i => T ![t i, t i ^ 2]) s N) =
      (trans s N + 1) / 2 := by
  rw [sepDegree_affine_sample T (fun i => ![t i, t i ^ 2])]
  exact parabola_law t s N ht

/-- Theorem 4.2 for affine images of a branch of the hyperbola `xy = 1`. -/
theorem affine_hyperbola_law (T : Plane ≃ᵃ[ℝ] Plane) (t : ℕ → ℝ) (s : ℕ → Bool) (N : ℕ)
    (ht : ∀ i, i + 1 < N → t i < t (i + 1)) (htpos : ∀ i < N, 0 < t i) :
    sepDegree (posPts (fun i => T ![t i, 1 / t i]) s N)
      (negPts (fun i => T ![t i, 1 / t i]) s N) = (trans s N + 1) / 2 := by
  rw [sepDegree_affine_sample T (fun i => ![t i, 1 / t i])]
  exact hyperbola_law t s N ht htpos

/-- **Corollary 4.3 (alternating labels).** `2r ≥ 2` cyclically ordered points on a circle with
alternating labels have `d_* = r`. -/
theorem circle_alternating (θ : ℕ → ℝ) (r : ℕ) (hr : 0 < r)
    (ht : ∀ i, i + 1 < 2 * r → θ i < θ (i + 1)) (hwin : θ (2 * r - 1) < θ 0 + 2 * π) :
    sepDegree (posPts (fun i => ![Real.cos (θ i), Real.sin (θ i)]) (fun i => decide (Even i)) (2 * r))
      (negPts (fun i => ![Real.cos (θ i), Real.sin (θ i)]) (fun i => decide (Even i)) (2 * r)) =
      r := by
  rw [circle_law θ _ (2 * r) (by omega) ht hwin]
  have htr : trans (fun i => decide (Even i)) (2 * r) = 2 * r - 1 := by
    unfold trans transSet
    rw [Finset.filter_true_of_mem]
    · simp
    · intro i _
      simp only [Nat.even_add_one, ne_eq, decide_eq_decide]
      tauto
  have hw : decide (Even (2 * r - 1)) ≠ decide (Even 0) := by
    have : ¬ Even (2 * r - 1) := by
      rw [Nat.not_even_iff_odd]; exact ⟨r - 1, by omega⟩
    simp [this]
  unfold cycTrans
  rw [htr, if_pos ⟨by omega, hw⟩]
  omega

/-! ## Capacity, stability, LP normalisation, SVMs, XOR (Sections 5–7, Appendix A) -/

/-! ### Dimension count `M_d = binom(d+2, 2)` -/

theorem monoSet_succ (d : ℕ) :
    monoSet (d + 1) = monoSet d ∪ Finset.antidiagonal (d + 1) := by
  ext p
  simp only [Finset.mem_union, mem_monoSet, Finset.mem_antidiagonal]
  omega

/-- `M_d = |{(r,s) : r + s ≤ d}| = binom(d+2, 2)`. -/
theorem card_monoSet (d : ℕ) : (monoSet d).card = (d + 2).choose 2 := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [monoSet_succ, Finset.card_union_of_disjoint, ih, Finset.Nat.card_antidiagonal]
    · have h : (d + 1 + 2).choose 2 = (d + 2) + (d + 2).choose 2 := by
        have h := Nat.choose_succ_succ (d + 2) 1
        rw [Nat.choose_one_right] at h
        exact h
      rw [h]; ring
    · rw [Finset.disjoint_left]
      intro p hp hp'
      rw [mem_monoSet] at hp
      rw [Finset.mem_antidiagonal] at hp'
      omega

/-! ### No configuration of `M_d + 1` points is shattered (Proposition 5.3) -/

/-- **Proposition 5.3.** If there are more than `M_d` points `z_i` (repetitions allowed), some
two-class labelling `(I, Iᶜ)` of them is not realisable by polynomials of degree `≤ d`. -/
theorem not_shattered (d : ℕ) {ι : Type*} [Fintype ι] (hcard : (monoSet d).card < Fintype.card ι)
    (z : ι → Plane) : ∃ I : Set ι, ¬ PolySep d (z '' I) (z '' Iᶜ) := by
  classical
  set v : ι → (Mono d → ℝ) := fun i => veronese d (z i)
  have hnli : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at this
    simp only [Fintype.card_coe] at this
    omega
  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hnli
  have h00 : ((0, 0) : ℕ × ℕ) ∈ monoSet d := mem_monoSet.2 (by simp)
  have hsum : ∑ i, g i = 0 := by
    have := congrFun hg ⟨(0, 0), h00⟩
    simpa [v, veronese, Finset.sum_apply] using this
  have hpos : ∃ i, 0 < g i := by
    by_contra hc
    push_neg at hc
    have hall : ∀ i ∈ Finset.univ, g i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hc i)).1 hsum
    exact hi0 (hall i0 (Finset.mem_univ _))
  obtain ⟨i1, hi1⟩ := hpos
  refine ⟨{i | 0 < g i}, ?_⟩
  rintro ⟨P, hP, h1, h2⟩
  obtain ⟨c, hc⟩ := exists_coeff_of_totalDegree_le hP
  have hzero : ∑ i, g i * eval (z i) P = 0 := by
    simp_rw [hc, sum_mono_eq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun p _ => ?_
    have := congrFun hg p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, v] at this
    calc ∑ i, g i * (c p.1 * veronese d (z i) p) = c p.1 * ∑ i, g i * veronese d (z i) p := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ = 0 := by rw [this, mul_zero]
  have hterm : ∀ i, 0 ≤ g i * eval (z i) P := by
    intro i
    by_cases hgi : 0 < g i
    · exact (mul_pos hgi (h1 _ ⟨i, hgi, rfl⟩)).le
    · push_neg at hgi
      exact mul_nonneg_of_nonpos_of_nonpos hgi (h2 _ ⟨i, hgi.not_gt, rfl⟩).le
  have : 0 < ∑ i, g i * eval (z i) P :=
    Finset.sum_pos' (fun i _ => hterm i) ⟨i1, Finset.mem_univ _, mul_pos hi1 (h1 _ ⟨i1, hi1, rfl⟩)⟩
  linarith

/-! ### Generic capacity: a unisolvent configuration (Proposition 5.2, existence part) -/

/-- The triangular grid point `(r, s)`. -/
def gridPt (p : ℕ × ℕ) : Plane := ![(p.1 : ℝ), (p.2 : ℝ)]

/-- Newton-type basis polynomial on the triangular grid. -/
def gridBasis (d : ℕ) (p : ℕ × ℕ) : Poly :=
  (∏ i ∈ Finset.range p.1, (X 0 - C (i : ℝ))) * (∏ j ∈ Finset.range p.2, (X 1 - C (j : ℝ))) *
    ∏ k ∈ Finset.Ioc (p.1 + p.2) d, (X 0 + X 1 - C (k : ℝ))

theorem totalDegree_gridBasis_le (d : ℕ) {p : ℕ × ℕ} (hp : p ∈ monoSet d) :
    (gridBasis d p).totalDegree ≤ d := by
  have hp' := mem_monoSet.1 hp
  unfold gridBasis
  have hfac : ∀ (q : Poly) (S : Finset ℕ) (f : ℕ → Poly), (∀ k, (f k).totalDegree ≤ 1) →
      (∏ k ∈ S, f k).totalDegree ≤ S.card := by
    intro _ S f hf
    refine (totalDegree_finset_prod _ _).trans ?_
    calc ∑ k ∈ S, (f k).totalDegree ≤ ∑ _k ∈ S, 1 := Finset.sum_le_sum fun k _ => hf k
      _ = S.card := by simp
  have hl : ∀ (j : Fin 2) (c : ℝ), (X j - C c : Poly).totalDegree ≤ 1 := fun j c =>
    (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X]) (by rw [totalDegree_C]; omega))
  have hl2 : ∀ c : ℝ, (X 0 + X 1 - C c : Poly).totalDegree ≤ 1 := fun c =>
    (totalDegree_sub _ _).trans (max_le ((totalDegree_add _ _).trans
      (max_le (by rw [totalDegree_X]) (by rw [totalDegree_X]))) (by rw [totalDegree_C]; omega))
  have h1 := hfac 0 (Finset.range p.1) (fun i => X 0 - C (i : ℝ)) (fun i => hl 0 _)
  have h2 := hfac 0 (Finset.range p.2) (fun j => X 1 - C (j : ℝ)) (fun j => hl 1 _)
  have h3 := hfac 0 (Finset.Ioc (p.1 + p.2) d) (fun k => X 0 + X 1 - C (k : ℝ))
    (fun k => hl2 _)
  simp only [Finset.card_range, Nat.card_Ioc] at h1 h2 h3
  refine (totalDegree_mul _ _).trans ?_
  refine (add_le_add (totalDegree_mul _ _) h3).trans ?_
  have := add_le_add h1 h2
  omega

theorem eval_gridBasis (d : ℕ) {p q : ℕ × ℕ} (hp : p ∈ monoSet d) (hq : q ∈ monoSet d) :
    eval (gridPt q) (gridBasis d p) = 0 ↔ q ≠ p := by
  have hp' := mem_monoSet.1 hp
  have hq' := mem_monoSet.1 hq
  simp only [gridBasis, gridPt, map_mul, map_prod, map_sub, map_add, eval_X, eval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, mul_eq_zero, Finset.prod_eq_zero_iff,
    Finset.mem_range, Finset.mem_Ioc, sub_eq_zero]
  constructor
  · rintro ((⟨i, hi, he⟩ | ⟨j, hj, he⟩) | ⟨k, hk, he⟩) rfl
    · exact absurd (Nat.cast_injective he) (by omega)
    · exact absurd (Nat.cast_injective he) (by omega)
    · have : (q.1 + q.2 : ℕ) = k := by exact_mod_cast he
      omega
  · intro hne
    by_cases h1 : q.1 < p.1
    · exact Or.inl (Or.inl ⟨q.1, h1, rfl⟩)
    by_cases h2 : q.2 < p.2
    · exact Or.inl (Or.inr ⟨q.2, h2, rfl⟩)
    refine Or.inr ⟨q.1 + q.2, ⟨?_, hq'⟩, by push_cast; ring⟩
    have : q.1 ≠ p.1 ∨ q.2 ≠ p.2 := by
      by_contra hc; push_neg at hc; exact hne (Prod.ext hc.1 hc.2)
    omega

/-- **Unisolvence of the triangular grid.** Every vector of values on the `M_d` grid points
`{(r,s) : r + s ≤ d}` is interpolated by a polynomial of degree `≤ d`; in particular the
evaluation map `E_d` is onto for this configuration. -/
theorem grid_interpolation (d : ℕ) (v : ℕ × ℕ → ℝ) :
    ∃ P : Poly, P.totalDegree ≤ d ∧ ∀ q ∈ monoSet d, eval (gridPt q) P = v q := by
  classical
  refine ⟨∑ p ∈ monoSet d, C (v p / eval (gridPt p) (gridBasis d p)) * gridBasis d p, ?_, ?_⟩
  · refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun p hp => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact totalDegree_gridBasis_le d hp
  · intro q hq
    rw [map_sum, Finset.sum_eq_single q]
    · have hne : eval (gridPt q) (gridBasis d q) ≠ 0 := by
        intro h; exact (eval_gridBasis d hq hq).1 h rfl
      simp only [map_mul, eval_C]
      field_simp
    · intro p hp hpq
      simp only [map_mul, eval_C]
      rw [(eval_gridBasis d hp hq).2 (Ne.symm hpq), mul_zero]
    · intro h; exact absurd hq h

/-- **Shattering of `M_d` points (Proposition 5.2, existence part).** Every binary labelling of
the `M_d = binom(d+2,2)` grid points is realisable in degree `d`. Together with
`not_shattered`, the largest number of planar points shattered by degree-`d` polynomial
sign classifiers is exactly `M_d`. -/
theorem grid_shattered (d : ℕ) (lab : ℕ × ℕ → Bool) :
    PolySep d (gridPt '' {p | p ∈ monoSet d ∧ lab p = true})
      (gridPt '' {p | p ∈ monoSet d ∧ lab p = false}) := by
  obtain ⟨P, hP, hv⟩ := grid_interpolation d (fun p => if lab p then 1 else -1)
  refine ⟨P, hP, ?_, ?_⟩
  · rintro _ ⟨p, ⟨hp, hl⟩, rfl⟩; rw [hv p hp]; simp [hl]
  · rintro _ ⟨p, ⟨hp, hl⟩, rfl⟩; rw [hv p hp]; simp [hl]

/-- The generic degree bound `d_gen(N) = ⌈(-3 + √(1 + 8N))/2⌉` is the least `d` with
`N ≤ M_d = binom(d+2,2)`. -/
theorem dgen_spec (N d : ℕ) :
    N ≤ (d + 2).choose 2 ↔ ⌈(-3 + Real.sqrt (1 + 8 * N)) / 2⌉ ≤ (d : ℤ) := by
  rw [Int.ceil_le, Nat.choose_two_right]
  have hdiv : (d + 2) * (d + 2 - 1) / 2 = (d + 2) * (d + 1) / 2 := by
    congr 2
  rw [hdiv]
  have key : N ≤ (d + 2) * (d + 1) / 2 ↔ 8 * N + 1 ≤ (2 * d + 3) ^ 2 := by
    have h2 : 2 ∣ (d + 2) * (d + 1) := by
      rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact ⟨(k + 1) * (2 * k + 1), by subst hk; ring⟩
      · exact ⟨(2 * k + 3) * (k + 1), by subst hk; ring⟩
    obtain ⟨m, hm⟩ := h2
    rw [hm, Nat.mul_div_cancel_left _ (by norm_num)]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [key]
  have hy : (0 : ℝ) ≤ 2 * d + 3 := by positivity
  have key2 : 8 * N + 1 ≤ (2 * d + 3) ^ 2 ↔ Real.sqrt (1 + 8 * N) ≤ 2 * d + 3 := by
    rw [Real.sqrt_le_left hy]
    constructor
    · intro h
      have : ((8 * N + 1 : ℕ) : ℝ) ≤ (((2 * d + 3) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this; linarith
    · intro h
      have : ((8 * N + 1 : ℕ) : ℝ) ≤ (((2 * d + 3) ^ 2 : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
  rw [key2]
  have hc : ((d : ℤ) : ℝ) = (d : ℝ) := Int.cast_natCast d
  rw [hc]
  constructor <;> intro h <;> linarith

/-! ### Local upper stability (Theorem 5.4) -/

/-- Positive points of an indexed sample. -/
def lblPos {ι : Type*} (z : ι → Plane) (s : ι → Bool) : Set Plane := z '' {i | s i = true}

/-- Negative points of an indexed sample. -/
def lblNeg {ι : Type*} (z : ι → Plane) (s : ι → Bool) : Set Plane := z '' {i | s i = false}

/-- **Theorem 5.4 (local upper stability).** If a finite labelled sample is separable, then for
some `ε > 0` every perturbation moving each point by less than `ε` (in the max-norm on `ℝ²`,
which in particular covers Euclidean `ε`-balls) is separable with degree at most
`d_*` of the original sample. -/
theorem local_upper_stability {ι : Type*} [Fintype ι] (z : ι → Plane) (s : ι → Bool)
    (hsep : ∃ d, PolySep d (lblPos z s) (lblNeg z s)) :
    ∃ ε > 0, ∀ z' : ι → Plane, (∀ i, dist (z' i) (z i) < ε) →
      PolySep (sepDegree (lblPos z s) (lblNeg z s)) (lblPos z' s) (lblNeg z' s) ∧
      sepDegree (lblPos z' s) (lblNeg z' s) ≤ sepDegree (lblPos z s) (lblNeg z s) := by
  obtain ⟨P, hP, h1, h2⟩ := polySep_sepDegree hsep
  let σ : ι → ℝ := fun i => if s i then 1 else -1
  let U : Set (ι → Plane) := ⋂ i, {y | 0 < σ i * eval (y i) P}
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    exact isOpen_lt continuous_const
      (continuous_const.mul ((MvPolynomial.continuous_eval P).comp (continuous_apply i)))
  have hzU : z ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_setOf_eq]
    intro i
    by_cases hs : s i = true
    · simp only [σ, hs, if_true, one_mul]; exact h1 _ ⟨i, hs, rfl⟩
    · have hs' : s i = false := by simpa using hs
      simp only [σ, hs', Bool.false_eq_true, if_false, neg_mul, one_mul, Left.neg_pos_iff]
      exact h2 _ ⟨i, hs', rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hzU
  refine ⟨ε, hε, fun z' hz' => ?_⟩
  have hz'U : z' ∈ U := hball ((dist_pi_lt_iff hε).2 hz')
  simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at hz'U
  have hsep' : PolySep (sepDegree (lblPos z s) (lblNeg z s)) (lblPos z' s) (lblNeg z' s) := by
    refine ⟨P, hP, ?_, ?_⟩
    · rintro _ ⟨i, hs, rfl⟩
      have := hz'U i
      simp only [σ, show s i = true from hs, if_true, one_mul] at this
      exact this
    · rintro _ ⟨i, hs, rfl⟩
      have := hz'U i
      simp only [σ, show s i = false from hs, Bool.false_eq_true, if_false, neg_mul,
        one_mul, Left.neg_pos_iff] at this
      exact this
  exact ⟨hsep', Nat.sInf_le hsep'⟩

/-! ### Linear-programming normalisation (Appendix A) and SVMs (Section 7) -/

/-- **Appendix A (unit functional margin).** For finite `A, B`, strict degree-`d` separation is
equivalent to feasibility of `s_i c^T Φ_d(z_i) ≥ 1`. -/
theorem polySep_iff_unit_margin (d : ℕ) (A B : Finset Plane) :
    PolySep d ↑A ↑B ↔ ∃ c : Mono d → ℝ,
      (∀ a ∈ A, 1 ≤ ∑ p, c p * veronese d a p) ∧ ∀ b ∈ B, ∑ p, c p * veronese d b p ≤ -1 := by
  classical
  constructor
  · rintro ⟨P, hP, h1, h2⟩
    obtain ⟨c, hc⟩ := exists_coeff_of_totalDegree_le hP
    -- functional margin γ = min over the sample of |P|
    obtain ⟨γ, hγ, hγA, hγB⟩ : ∃ γ : ℝ, 0 < γ ∧ (∀ a ∈ A, γ ≤ eval a P) ∧
        ∀ b ∈ B, γ ≤ -eval b P := by
      let S : Finset ℝ := insert 1 (A.image (fun a => eval a P) ∪ B.image (fun b => -eval b P))
      have hSpos : ∀ x ∈ S, 0 < x := by
        intro x hx
        simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at hx
        rcases hx with rfl | ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
        · exact one_pos
        · exact h1 a ha
        · linarith [h2 b hb]
      refine ⟨S.min' (Finset.insert_nonempty _ _), hSpos _ (Finset.min'_mem _ _), fun a ha =>
        Finset.min'_le _ _ ?_, fun b hb => Finset.min'_le _ _ ?_⟩
      · simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
      · simp only [S, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        exact Or.inr (Or.inr ⟨b, hb, rfl⟩)
    refine ⟨fun p => c p.1 / γ, fun a ha => ?_, fun b hb => ?_⟩
    · have := hγA a ha
      rw [hc, sum_mono_eq] at this
      have e : ∑ p, c p.1 / γ * veronese d a p = (∑ p, c p.1 * veronese d a p) / γ := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e, le_div_iff₀ hγ]; linarith
    · have := hγB b hb
      rw [hc, sum_mono_eq] at this
      have e : ∑ p, c p.1 / γ * veronese d b p = (∑ p, c p.1 * veronese d b p) / γ := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e, div_le_iff₀ hγ]; linarith
  · rintro ⟨c, h1, h2⟩
    rw [polySep_iff_affine_veronese]
    refine ⟨c, 0, ?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩; have := h1 a ha; linarith
    · rintro _ ⟨b, hb, rfl⟩; have := h2 b hb; linarith

/-- Kernel weights `D_d² = diag( binom(d, r+s) · binom(r+s, r) )`. -/
def kernelWeight (d : ℕ) (p : ℕ × ℕ) : ℝ := ((d.choose (p.1 + p.2)) * ((p.1 + p.2).choose p.1) : ℕ)

theorem kernelWeight_pos {d : ℕ} {p : ℕ × ℕ} (hp : p ∈ monoSet d) : 0 < kernelWeight d p := by
  have hp' := mem_monoSet.1 hp
  unfold kernelWeight
  exact_mod_cast Nat.mul_pos (Nat.choose_pos hp') (Nat.choose_pos (by omega))

/-- The weighted Veronese map `Ψ_d = D_d Φ_d` of the inhomogeneous polynomial kernel. -/
def kernelFeature (d : ℕ) (z : Plane) : Mono d → ℝ :=
  fun p => Real.sqrt (kernelWeight d p.1) * veronese d z p

/-- **Polynomial-kernel identity.** `K_d(z,z') = (1 + z·z')^d = Ψ_d(z)·Ψ_d(z')`. -/
theorem kernel_identity (d : ℕ) (z z' : Plane) :
    (1 + ∑ k, z k * z' k) ^ d = ∑ p, kernelFeature d z p * kernelFeature d z' p := by
  classical
  have hw : ∀ p : Mono d, kernelFeature d z p * kernelFeature d z' p =
      kernelWeight d p.1 * ((z 0 * z' 0) ^ p.1.1 * (z 1 * z' 1) ^ p.1.2) := by
    intro p
    simp only [kernelFeature, veronese]
    have := Real.mul_self_sqrt (kernelWeight_pos p.2).le
    calc Real.sqrt (kernelWeight d p.1) * (z 0 ^ p.1.1 * z 1 ^ p.1.2) *
          (Real.sqrt (kernelWeight d p.1) * (z' 0 ^ p.1.1 * z' 1 ^ p.1.2))
        = (Real.sqrt (kernelWeight d p.1) * Real.sqrt (kernelWeight d p.1)) *
          ((z 0 * z' 0) ^ p.1.1 * (z 1 * z' 1) ^ p.1.2) := by ring
      _ = _ := by rw [this]
  simp_rw [hw]
  rw [Finset.sum_coe_sort (monoSet d) (fun p => kernelWeight d p *
    ((z 0 * z' 0) ^ p.1 * (z 1 * z' 1) ^ p.2))]
  have hmono : monoSet d = (Finset.range (d + 1)).biUnion Finset.antidiagonal := by
    ext p
    simp only [mem_monoSet, Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
    constructor
    · intro h; exact ⟨p.1 + p.2, by omega, rfl⟩
    · rintro ⟨k, hk, rfl⟩; omega
  rw [hmono, Finset.sum_biUnion]
  · rw [Fin.sum_univ_two, add_comm, add_pow]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [add_pow, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, one_pow, mul_one,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr' : r ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    simp only [kernelWeight, Nat.add_sub_cancel' hr']
    push_cast
    ring
  · intro i _ j _ hij
    exact Finset.disjoint_left.2 fun p hp hp' => hij ((Finset.mem_antidiagonal.1 hp).symm.trans
      (Finset.mem_antidiagonal.1 hp'))

/-- Feasibility of the degree-`d` polynomial-kernel hard-margin SVM constraints
`s_i w^T Ψ_d(z_i) ≥ 1`. (The primal objective `½‖w‖²` is finite for every `w`, so feasibility
of the primal problem is exactly feasibility of these constraints.) -/
def SVMFeasible (d : ℕ) (A B : Finset Plane) : Prop :=
  ∃ w : Mono d → ℝ, (∀ a ∈ A, 1 ≤ ∑ p, w p * kernelFeature d a p) ∧
    ∀ b ∈ B, ∑ p, w p * kernelFeature d b p ≤ -1

/-- **Proposition 7.1 (first feasible polynomial-SVM degree).** For finite `A, B`, degree-`d`
algebraic separability is equivalent to feasibility of the degree-`d` hard-margin SVM. -/
theorem polySep_iff_svmFeasible (d : ℕ) (A B : Finset Plane) :
    PolySep d ↑A ↑B ↔ SVMFeasible d A B := by
  rw [polySep_iff_unit_margin]
  have hsq : ∀ p : Mono d, Real.sqrt (kernelWeight d p.1) ≠ 0 :=
    fun p => (Real.sqrt_pos.2 (kernelWeight_pos p.2)).ne'
  constructor
  · rintro ⟨c, h1, h2⟩
    refine ⟨fun p => c p / Real.sqrt (kernelWeight d p.1), ?_, ?_⟩
    · intro a ha
      convert h1 a ha using 2 with p
      have := hsq p
      simp only [kernelFeature]; field_simp
    · intro b hb
      convert h2 b hb using 2 with p
      have := hsq p
      simp only [kernelFeature]; field_simp
  · rintro ⟨w, h1, h2⟩
    refine ⟨fun p => w p * Real.sqrt (kernelWeight d p.1), ?_, ?_⟩
    · intro a ha
      convert h1 a ha using 2 with p
      simp only [kernelFeature]; ring
    · intro b hb
      convert h2 b hb using 2 with p
      simp only [kernelFeature]; ring

/-- **Equation (7.4).** For finite disjoint classes, `d_*` is the least degree for which the
polynomial-kernel hard-margin SVM is feasible. -/
theorem sepDegree_eq_min_svm (A B : Finset Plane) :
    sepDegree ↑A ↑B = sInf {d | SVMFeasible d A B} := by
  unfold sepDegree
  congr 1
  ext d
  exact polySep_iff_svmFeasible d A B

/-- **Equation (7.5).** If `w^T Ψ_d = c^T Φ_d` with `c = D_d w`, then `‖w‖² = c^T D_d^{-2} c`. -/
theorem svm_norm_identity (d : ℕ) (w : Mono d → ℝ) :
    ∑ p, w p ^ 2 = ∑ p, (w p * Real.sqrt (kernelWeight d p.1)) ^ 2 / kernelWeight d p.1 := by
  refine Finset.sum_congr rfl fun p _ => ?_
  have hpos := kernelWeight_pos p.2
  rw [mul_pow, Real.sq_sqrt hpos.le]
  field_simp

/-! ### The XOR configuration -/

/-- The XOR configuration: `{(1,1), (-1,-1)}` versus `{(1,-1), (-1,1)}` has `d_* = 2`. -/
theorem xor_sepDegree :
    sepDegree ↑({![1, 1], ![-1, -1]} : Finset Plane) ↑({![1, -1], ![-1, 1]} : Finset Plane) = 2 := by
  have hsep : PolySep 2 ↑({![1, 1], ![-1, -1]} : Finset Plane)
      ↑({![1, -1], ![-1, 1]} : Finset Plane) := by
    refine ⟨X 0 * X 1, ?_, ?_, ?_⟩
    · refine (totalDegree_mul _ _).trans ?_; simp
    · intro a ha
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl <;> simp
    · intro b hb
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hb
      rcases hb with rfl | rfl <;> simp
  have hnot : ¬ PolySep 1 ↑({![1, 1], ![-1, -1]} : Finset Plane)
      ↑({![1, -1], ![-1, 1]} : Finset Plane) := by
    rw [polySep_one_iff_affine]
    rintro ⟨c, u, h1, h2⟩
    have e1 := h1 ![1, 1] (by simp)
    have e2 := h1 ![-1, -1] (by simp)
    have e3 := h2 ![1, -1] (by simp)
    have e4 := h2 ![-1, 1] (by simp)
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at e1 e2 e3 e4
    linarith
  refine le_antisymm ((sepDegree_le_iff ⟨2, hsep⟩).2 hsep) ?_
  by_contra h
  push_neg at h
  exact hnot ((polySep_sepDegree ⟨2, hsep⟩).mono (by omega))

/-! ## Sparse certificates (Section 3) -/

/-! ### Sparse certificates (Corollary 3.4) -/

/-- **Corollary 3.4 (sparse certificate).** If degree-`d` separation of finite `A, B` fails, the
moment certificate can be chosen with at most `M_d + 1` observations of positive weight in
total. -/
theorem sparse_momentCert (d : ℕ) (A B : Finset Plane) (h : ¬ PolySep d ↑A ↑B) :
    ∃ α β, MomentCert d A B α β ∧
      (A.filter (fun a => α a ≠ 0)).card + (B.filter (fun b => β b ≠ 0)).card ≤
        (monoSet d).card + 1 := by
  classical
  obtain ⟨α0, β0, hα0, hα1, hβ0, hβ1, hm⟩ := (not_polySep_iff_momentCert d A B).1 h
  let ι := {a // a ∈ A} ⊕ {b // b ∈ B}
  let V : ι → (Mono d → ℝ) := Sum.elim (fun a => veronese d a.1) (fun b => -veronese d b.1)
  let w0 : ι → ℝ := Sum.elim (fun a => α0 a.1 / 2) (fun b => β0 b.1 / 2)
  have hsumA : ∀ f : Plane → ℝ, ∑ a : {a // a ∈ A}, f a.1 = ∑ a ∈ A, f a :=
    fun f => Finset.sum_coe_sort A f
  have hsumB : ∀ f : Plane → ℝ, ∑ b : {b // b ∈ B}, f b.1 = ∑ b ∈ B, f b :=
    fun f => Finset.sum_coe_sort B f
  have h0 : (0 : Mono d → ℝ) ∈ convexHull ℝ (Set.range V) := by
    refine mem_convexHull_of_exists_fintype w0 V ?_ ?_ (fun i => ⟨i, rfl⟩) ?_
    · rintro (a | b)
      · exact div_nonneg (hα0 a.1 a.2) zero_le_two
      · exact div_nonneg (hβ0 b.1 b.2) zero_le_two
    · rw [Fintype.sum_sum_type]
      simp only [w0, Sum.elim_inl, Sum.elim_inr]
      rw [hsumA (fun a => α0 a / 2), hsumB (fun b => β0 b / 2), ← Finset.sum_div,
        ← Finset.sum_div, hα1, hβ1]
      norm_num
    · funext p
      rw [Fintype.sum_sum_type]
      simp only [w0, V, Sum.elim_inl, Sum.elim_inr, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Pi.zero_apply, veronese]
      rw [hsumA (fun a => α0 a / 2 * (a 0 ^ p.1.1 * a 1 ^ p.1.2)),
        hsumB (fun b => β0 b / 2 * -(b 0 ^ p.1.1 * b 1 ^ p.1.2))]
      have := hm p.1.1 p.1.2 (mem_monoSet.1 p.2)
      have e1 : ∑ a ∈ A, α0 a / 2 * (a 0 ^ p.1.1 * a 1 ^ p.1.2) =
          (∑ a ∈ A, α0 a * (a 0 ^ p.1.1 * a 1 ^ p.1.2)) / 2 := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => by ring
      have e2 : ∑ b ∈ B, β0 b / 2 * -(b 0 ^ p.1.1 * b 1 ^ p.1.2) =
          -(∑ b ∈ B, β0 b * (b 0 ^ p.1.1 * b 1 ^ p.1.2)) / 2 := by
        rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e1, e2, this]; ring
  obtain ⟨ι', _, z, w, hrange, hai, hwpos, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull h0
  have hcard : Fintype.card ι' ≤ (monoSet d).card + 1 := by
    have := hai.card_le_finrank_succ
    have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h2
    omega
  choose j hj using fun i => (hrange ⟨i, rfl⟩ : z i ∈ Set.range V)
  let lam : ι → ℝ := fun k => ∑ i ∈ Finset.univ.filter (fun i => j i = k), w i
  have hlam0 : ∀ k, 0 ≤ lam k := fun k => Finset.sum_nonneg fun i _ => (hwpos i).le
  have hlamsum : ∑ k, lam k = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (j i)), hw1]
  have hlamV : ∑ k, lam k • V k = 0 := by
    simp only [lam, Finset.sum_smul]
    have hx : ∀ x, ∑ i ∈ Finset.univ.filter (fun i => j i = x), w i • V x =
        ∑ i ∈ Finset.univ.filter (fun i => j i = x), w i • V (j i) := fun x =>
      Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]
    rw [Finset.sum_congr rfl fun x _ => hx x,
      Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := j)
      (fun i _ => Finset.mem_univ (j i)) (fun i => w i • V (j i)), ← hwz]
    exact Finset.sum_congr rfl fun i _ => by rw [hj]
  have hlamcount : ∑ k, (if lam k ≠ 0 then 1 else 0) ≤ Fintype.card ι' := by
    calc ∑ k, (if lam k ≠ 0 then 1 else 0)
        ≤ ∑ k, (Finset.univ.filter (fun i => j i = k)).card := by
          refine Finset.sum_le_sum fun k _ => ?_
          split_ifs with hk
          · rw [Nat.one_le_iff_ne_zero]
            intro h0
            rw [Finset.card_eq_zero] at h0
            exact hk (by simp only [lam, h0, Finset.sum_empty])
          · exact Nat.zero_le _
      _ = Fintype.card ι' := by
          rw [← Finset.card_univ, ← Finset.card_eq_sum_card_fiberwise
            (fun i _ => Finset.mem_univ (j i))]
  -- masses of the two classes
  have hcoord : ∀ p : Mono d, ∑ a : {a // a ∈ A}, lam (Sum.inl a) * veronese d a.1 p =
      ∑ b : {b // b ∈ B}, lam (Sum.inr b) * veronese d b.1 p := by
    intro p
    have := congrFun hlamV p
    rw [Fintype.sum_sum_type] at this
    simp only [V, Sum.elim_inl, Sum.elim_inr, Finset.sum_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply, smul_eq_mul, Pi.zero_apply, mul_neg, Finset.sum_neg_distrib] at this
    linarith
  have h00 : ((0, 0) : ℕ × ℕ) ∈ monoSet d := mem_monoSet.2 (by simp)
  have hmass := hcoord ⟨(0, 0), h00⟩
  simp only [veronese, pow_zero, mul_one] at hmass
  have htot : ∑ a : {a // a ∈ A}, lam (Sum.inl a) + ∑ b : {b // b ∈ B}, lam (Sum.inr b) = 1 := by
    rw [← Fintype.sum_sum_type]; exact hlamsum
  have hhalfA : ∑ a : {a // a ∈ A}, lam (Sum.inl a) = 1 / 2 := by linarith
  have hhalfB : ∑ b : {b // b ∈ B}, lam (Sum.inr b) = 1 / 2 := by linarith
  let α : Plane → ℝ := fun a => if ha : a ∈ A then 2 * lam (Sum.inl ⟨a, ha⟩) else 0
  let β : Plane → ℝ := fun b => if hb : b ∈ B then 2 * lam (Sum.inr ⟨b, hb⟩) else 0
  have hsA : ∀ f : Plane → ℝ → ℝ, ∑ a ∈ A, f a (α a) =
      ∑ a : {a // a ∈ A}, f a.1 (2 * lam (Sum.inl a)) := by
    intro f
    rw [← Finset.sum_coe_sort A]
    exact Finset.sum_congr rfl fun a _ => by simp [α, a.2]
  have hsB : ∀ f : Plane → ℝ → ℝ, ∑ b ∈ B, f b (β b) =
      ∑ b : {b // b ∈ B}, f b.1 (2 * lam (Sum.inr b)) := by
    intro f
    rw [← Finset.sum_coe_sort B]
    exact Finset.sum_congr rfl fun b _ => by simp [β, b.2]
  refine ⟨α, β, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a ha; simp only [α, ha, dif_pos]; linarith [hlam0 (Sum.inl ⟨a, ha⟩)]
  · rw [hsA (fun _ x => x), ← Finset.mul_sum, hhalfA]; norm_num
  · intro b hb; simp only [β, hb, dif_pos]; linarith [hlam0 (Sum.inr ⟨b, hb⟩)]
  · rw [hsB (fun _ x => x), ← Finset.mul_sum, hhalfB]; norm_num
  · intro r s hrs
    rw [hsA (fun a x => x * (a 0 ^ r * a 1 ^ s)), hsB (fun b x => x * (b 0 ^ r * b 1 ^ s))]
    have := hcoord ⟨(r, s), mem_monoSet.2 hrs⟩
    simp only [veronese] at this
    simp only [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum, this]
  · have e1 : (A.filter (fun a => α a ≠ 0)).card =
        ∑ a : {a // a ∈ A}, (if lam (Sum.inl a) ≠ 0 then 1 else 0) := by
      rw [Finset.card_filter, ← Finset.sum_coe_sort A]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [α, a.2]
    have e2 : (B.filter (fun b => β b ≠ 0)).card =
        ∑ b : {b // b ∈ B}, (if lam (Sum.inr b) ≠ 0 then 1 else 0) := by
      rw [Finset.card_filter, ← Finset.sum_coe_sort B]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [β, b.2]
    rw [e1, e2, ← Fintype.sum_sum_type (f := fun k => if lam k ≠ 0 then 1 else 0)]
    exact hlamcount.trans hcard

/-! ## Smooth minimum-degree separators (Section 2) -/
open MeasureTheory

/-! ### A smooth decision curve at minimum degree (Theorem 2.6) -/

theorem differentiable_eval_poly (Q : Poly) : Differentiable ℝ (fun y : Plane => eval y Q) := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (differentiable_apply i)

/-- The perturbation `P + v₂ + v₀ x + v₁ y`. -/
def pert (P : Poly) (v : Fin 3 → ℝ) : Poly := P + C (v 2) + C (v 0) * X 0 + C (v 1) * X 1

theorem eval_pert (P : Poly) (v : Fin 3 → ℝ) (z : Plane) :
    eval z (pert P v) = eval z P + v 2 + v 0 * z 0 + v 1 * z 1 := by
  simp [pert]

theorem eval_pderiv0_pert (P : Poly) (v : Fin 3 → ℝ) (z : Plane) :
    eval z (pderiv 0 (pert P v)) = eval z (pderiv 0 P) + v 0 := by
  simp [pert, pderiv_X]

theorem eval_pderiv1_pert (P : Poly) (v : Fin 3 → ℝ) (z : Plane) :
    eval z (pderiv 1 (pert P v)) = eval z (pderiv 1 P) + v 1 := by
  simp [pert, pderiv_X]

/-- **Theorem 2.6 (smooth minimum-degree realisation).** For finite, disjoint, nonempty classes
there is a polynomial of total degree exactly `d_*` that separates them and whose gradient does
not vanish anywhere on its (nonempty) zero set. By the regular value theorem the decision
boundary is therefore a nonempty smooth one-dimensional submanifold of `ℝ²`. -/
theorem smooth_min_degree (A B : Finset Plane) (hAB : Disjoint A B) (hA : A.Nonempty)
    (hB : B.Nonempty) :
    ∃ P : Poly, P.totalDegree = sepDegree ↑A ↑B ∧ (∀ a ∈ A, 0 < eval a P) ∧
      (∀ b ∈ B, eval b P < 0) ∧
      (∀ z, eval z P = 0 → eval z (pderiv 0 P) ≠ 0 ∨ eval z (pderiv 1 P) ≠ 0) ∧
      ∃ z, eval z P = 0 := by
  classical
  have hex := exists_polySep A B hAB
  set d := sepDegree ↑A ↑B with hd_def
  have hd1 : 1 ≤ d := one_le_sepDegree (Finset.coe_nonempty.2 hA) (Finset.coe_nonempty.2 hB) hex
  obtain ⟨P0, hP0, h1, h2⟩ := polySep_sepDegree hex
  set S := A ∪ B
  -- margin η and size bound M
  obtain ⟨η, hη, hηS⟩ : ∃ η : ℝ, 0 < η ∧ ∀ z ∈ S, η ≤ |eval z P0| := by
    let T : Finset ℝ := insert 1 (S.image fun z => |eval z P0|)
    have hT : ∀ x ∈ T, 0 < x := by
      intro x hx
      simp only [T, Finset.mem_insert, Finset.mem_image] at hx
      rcases hx with rfl | ⟨z, hz, rfl⟩
      · exact one_pos
      · rcases Finset.mem_union.1 hz with hz | hz
        · exact abs_pos.2 (h1 z hz).ne'
        · exact abs_pos.2 (h2 z hz).ne
    refine ⟨T.min' (Finset.insert_nonempty _ _), hT _ (Finset.min'_mem _ _), fun z hz =>
      Finset.min'_le _ _ ?_⟩
    simp only [T, Finset.mem_insert, Finset.mem_image]
    exact Or.inr ⟨z, hz, rfl⟩
  set M : ℝ := ∑ z ∈ S, (1 + |z 0| + |z 1|) + 1
  have hMS : ∀ z ∈ S, 1 + |z 0| + |z 1| ≤ M := by
    intro z hz
    have := Finset.single_le_sum (f := fun z : Plane => 1 + |z 0| + |z 1|)
      (fun z _ => by positivity) hz
    simp only [M]; linarith
  have hM : 0 < M := by
    have : 0 ≤ ∑ z ∈ S, (1 + |z 0| + |z 1|) := Finset.sum_nonneg fun z _ => by positivity
    simp only [M]; linarith
  set r := η / M
  have hr : 0 < r := div_pos hη hM
  -- small perturbations keep all labels
  have hgood : ∀ v : Fin 3 → ℝ, (∀ k, |v k| < r) → ∀ z ∈ S,
      |v 2 + v 0 * z 0 + v 1 * z 1| < η := by
    intro v hv z hz
    have e0 : |v 0 * z 0| ≤ r * |z 0| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hv 0).le (abs_nonneg _)
    have e1 : |v 1 * z 1| ≤ r * |z 1| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hv 1).le (abs_nonneg _)
    have hrM : r * M = η := by simp only [r]; field_simp
    calc |v 2 + v 0 * z 0 + v 1 * z 1| ≤ |v 2| + |v 0 * z 0| + |v 1 * z 1| :=
          (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _) |>.trans_eq (by ring)
      _ < r + r * |z 0| + r * |z 1| := by linarith [hv 2]
      _ = r * (1 + |z 0| + |z 1|) := by ring
      _ ≤ r * M := mul_le_mul_of_nonneg_left (hMS z hz) hr.le
      _ = η := hrM
  -- the bad parameter set is contained in a null set
  let emb : (Fin 3 → ℝ) → Plane := fun x => ![x 0, x 1]
  have hemb : Differentiable ℝ emb := by
    rw [differentiable_pi]
    intro i; fin_cases i
    · simpa [emb] using differentiable_apply (0 : Fin 3)
    · simpa [emb] using differentiable_apply (1 : Fin 3)
  let g0 : (Fin 3 → ℝ) → ℝ := fun x => eval (emb x) (pderiv 0 P0)
  let g1 : (Fin 3 → ℝ) → ℝ := fun x => eval (emb x) (pderiv 1 P0)
  let gp : (Fin 3 → ℝ) → ℝ := fun x => eval (emb x) P0
  have hg0 : Differentiable ℝ g0 := (differentiable_eval_poly _).comp hemb
  have hg1 : Differentiable ℝ g1 := (differentiable_eval_poly _).comp hemb
  have hgp : Differentiable ℝ gp := (differentiable_eval_poly _).comp hemb
  let f : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun x =>
    ![-g0 x, -g1 x, -gp x + x 0 * g0 x + x 1 * g1 x]
  have hf : Differentiable ℝ f := by
    rw [differentiable_pi]
    intro i; fin_cases i
    · simpa [f] using hg0.neg
    · simpa [f] using hg1.neg
    · simpa [f] using (hgp.neg.add ((differentiable_apply 0).mul hg0)).add
        ((differentiable_apply 1).mul hg1)
  let Sub : Submodule ℝ (Fin 3 → ℝ) := LinearMap.ker
    (LinearMap.proj 2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)
  have hSub : Sub ≠ ⊤ := by
    intro h
    have : (Pi.single 2 1 : Fin 3 → ℝ) ∈ Sub := h ▸ Submodule.mem_top
    simp [Sub] at this
  have hnull : volume (f '' (Sub : Set (Fin 3 → ℝ))) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hf.differentiableOn
      (Measure.addHaar_submodule volume Sub hSub)
  obtain ⟨v, hvball, hvbad⟩ : ∃ v ∈ Metric.ball (0 : Fin 3 → ℝ) r,
      v ∉ f '' (Sub : Set (Fin 3 → ℝ)) := by
    by_contra hc
    push_neg at hc
    have := measure_mono (μ := volume) hc
    rw [hnull] at this
    exact (Metric.measure_ball_pos volume (0 : Fin 3 → ℝ) hr).ne' (le_antisymm this (zero_le _))
  have hv : ∀ k, |v k| < r := by
    rw [mem_ball_zero_iff, pi_norm_lt_iff hr] at hvball
    simpa [Real.norm_eq_abs] using hvball
  set P := pert P0 v
  have hposA : ∀ a ∈ A, 0 < eval a P := by
    intro a ha
    have hη' := hηS a (Finset.mem_union_left _ ha)
    have hg := hgood v hv a (Finset.mem_union_left _ ha)
    rw [abs_of_pos (h1 a ha)] at hη'
    rw [eval_pert]
    have := neg_abs_le (v 2 + v 0 * a 0 + v 1 * a 1)
    linarith
  have hnegB : ∀ b ∈ B, eval b P < 0 := by
    intro b hb
    have hη' := hηS b (Finset.mem_union_right _ hb)
    have hg := hgood v hv b (Finset.mem_union_right _ hb)
    rw [abs_of_neg (h2 b hb)] at hη'
    rw [eval_pert]
    have := le_abs_self (v 2 + v 0 * b 0 + v 1 * b 1)
    linarith
  have hsepP : PolySep (P.totalDegree) ↑A ↑B := ⟨P, le_rfl, hposA, hnegB⟩
  refine ⟨P, ?_, hposA, hnegB, ?_, ?_⟩
  · refine le_antisymm ?_ (Nat.sInf_le hsepP)
    simp only [P, pert]
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_add _ _).trans (max_le
      ((totalDegree_add _ _).trans (max_le hP0 (by simp))) ?_)) ?_)
    · exact (totalDegree_mul _ _).trans (by simp; omega)
    · exact (totalDegree_mul _ _).trans (by simp; omega)
  · intro z hz
    by_contra hc
    push_neg at hc
    obtain ⟨hc0, hc1⟩ := hc
    rw [eval_pderiv0_pert] at hc0
    rw [eval_pderiv1_pert] at hc1
    rw [eval_pert] at hz
    apply hvbad
    refine ⟨![z 0, z 1, 0], by simp [Sub], ?_⟩
    have hez : emb ![z 0, z 1, 0] = z := by
      funext i; fin_cases i <;> rfl
    funext k; fin_cases k
    · simp only [f, g0, hez]; simp; linarith
    · simp only [f, g1, hez]; simp; linarith
    · simp only [f, g0, g1, gp, hez]; simp
      have e0 : v 0 = -eval z (pderiv 0 P0) := by linarith
      have e1 : v 1 = -eval z (pderiv 1 P0) := by linarith
      rw [e0, e1] at hz
      linarith
  · obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ := hB
    obtain ⟨t, _, ht⟩ := path_meets_zeroSet P (fun t => a + t • (b - a))
      (by fun_prop) (by simpa using hposA a ha) (by simpa using hnegB b hb)
    exact ⟨_, ht⟩



/-- **Remark 4.4 (correction to the definition of "nondegenerate conic").** The pair of parallel
lines `x² = 1` is a *nonsingular affine* real curve of degree two (its gradient `(2x, 0)` never
vanishes on it), but the exact conic law fails on its components: four points `(1, i)`,
`i = 0,1,2,3`, with alternating labels on the component `x = 1` have `R = 3` transitions and
`d_* = 3`, whereas `⌈R/2⌉ = 2`. Hence "nondegenerate" must mean that the conic is irreducible
(nonsingular projective closure), i.e. an ellipse, parabola or hyperbola. -/
theorem conic_definition_counterexample :
    (∀ i : ℕ, (![1, (i : ℝ)] : Plane) 0 ^ 2 - 1 = 0 ∧ 2 * (![1, (i : ℝ)] : Plane) 0 ≠ 0) ∧
      sepDegree (posPts (fun i => ![1, (i : ℝ)]) (fun i => decide (Even i)) 4)
        (negPts (fun i => ![1, (i : ℝ)]) (fun i => decide (Even i)) 4) = 3 ∧
      (trans (fun i => decide (Even i)) 4 + 1) / 2 = 2 := by
  have htr : trans (fun i => decide (Even i)) 4 = 3 := by decide
  have hγ : (fun i : ℕ => (![1, (i : ℝ)] : Plane)) =
      fun i : ℕ => (![1, 0] : Plane) + (i : ℝ) • (![0, 1] : Plane) := by
    funext i j; fin_cases j <;> simp
  have hv : (![0, 1] : Plane) ≠ 0 := by
    intro h; have := congrFun h 1; simp at this
  refine ⟨fun i => ⟨by simp, by simp⟩, ?_, by rw [htr]⟩
  rw [hγ, line_law (![1, 0] : Plane) (![0, 1] : Plane) hv (fun i => (i : ℝ)) _ 4
    (fun i _ => by simp), htr]

/-! ## Generic interpolation capacity (Section 5) -/
/-! ### Generic interpolation capacity (Proposition 5.2) -/

/-- The multivariate Vandermonde matrix `E_d` of a configuration `z_1, …, z_N`. -/
def vandermonde (d : ℕ) {N : ℕ} (z : Fin N → Plane) : Matrix (Fin N) (Mono d) ℝ :=
  fun i p => veronese d (z i) p

/-- A configuration on which every value vector — in particular every binary labelling — is
interpolated by a polynomial of degree at most `d` (i.e. `E_d` is onto). -/
def GoodConfig (d : ℕ) {N : ℕ} (z : Fin N → Plane) : Prop :=
  ∀ v : Fin N → ℝ, ∃ P : Poly, P.totalDegree ≤ d ∧ ∀ i, eval (z i) P = v i

theorem exists_coeffVec_iff (d : ℕ) {N : ℕ} (z : Fin N → Plane) (v : Fin N → ℝ) :
    (∃ P : Poly, P.totalDegree ≤ d ∧ ∀ i, eval (z i) P = v i) ↔
      ∃ c : Mono d → ℝ, (vandermonde d z).mulVec c = v := by
  classical
  constructor
  · rintro ⟨P, hP, hv⟩
    obtain ⟨c, hc⟩ := exists_coeff_of_totalDegree_le hP
    refine ⟨fun p => c p.1, funext fun i => ?_⟩
    rw [← hv i, hc, sum_mono_eq]
    simp only [Matrix.mulVec, dotProduct, vandermonde]
    exact Finset.sum_congr rfl fun p _ => by ring
  · rintro ⟨c, hc⟩
    let c' : ℕ × ℕ → ℝ := fun p => if h : p ∈ monoSet d then c ⟨p, h⟩ else 0
    refine ⟨polyOfCoeff d c', totalDegree_polyOfCoeff_le d c', fun i => ?_⟩
    rw [← hc, eval_polyOfCoeff, sum_mono_eq]
    simp only [Matrix.mulVec, dotProduct, vandermonde]
    exact Finset.sum_congr rfl fun p _ => by simp [c', p.2, mul_comm]

/-- `E_d` is onto iff the Gram determinant `det(E_d E_dᵀ)` (a polynomial in the coordinates of
the points) is nonzero. In particular the good configurations form a Zariski-open set. -/
theorem goodConfig_iff_gram (d : ℕ) {N : ℕ} (z : Fin N → Plane) :
    GoodConfig d z ↔ (vandermonde d z * (vandermonde d z).transpose).det ≠ 0 := by
  classical
  set M := vandermonde d z
  unfold GoodConfig
  simp_rw [exists_coeffVec_iff]
  constructor
  · intro h hdet
    obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    obtain ⟨c, hc⟩ := h u
    -- ‖Mᵀ u‖² = uᵀ M Mᵀ u = 0
    have h1 : M.transpose.mulVec u ⬝ᵥ M.transpose.mulVec u = 0 := by
      calc M.transpose.mulVec u ⬝ᵥ M.transpose.mulVec u
          = Matrix.vecMul u M ⬝ᵥ M.transpose.mulVec u := by rw [Matrix.mulVec_transpose]
        _ = u ⬝ᵥ M.mulVec (M.transpose.mulVec u) := (Matrix.dotProduct_mulVec _ _ _).symm
        _ = u ⬝ᵥ (M * M.transpose).mulVec u := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hu, dotProduct_zero]
    have h2 : M.transpose.mulVec u = 0 := dotProduct_self_eq_zero.1 h1
    have h3 : u ⬝ᵥ u = 0 := by
      calc u ⬝ᵥ u = u ⬝ᵥ M.mulVec c := by rw [hc]
        _ = Matrix.vecMul u M ⬝ᵥ c := Matrix.dotProduct_mulVec _ _ _
        _ = M.transpose.mulVec u ⬝ᵥ c := by rw [Matrix.mulVec_transpose]
        _ = 0 := by rw [h2, zero_dotProduct]
    exact hu0 (dotProduct_self_eq_zero.1 h3)
  · intro hdet v
    refine ⟨M.transpose.mulVec ((M * M.transpose)⁻¹.mulVec v), ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    show (M * M.transpose * (M * M.transpose)⁻¹).mulVec v = v
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]

/-- The triangular grid gives a good configuration of any `N ≤ M_d` points. -/
theorem exists_goodConfig (d N : ℕ) (hN : N ≤ (monoSet d).card) :
    ∃ g : Fin N → Plane, GoodConfig d g := by
  classical
  let e : Fin N → ℕ × ℕ := fun i => ((monoSet d).equivFin.symm (Fin.castLE hN i)).1
  have he : Function.Injective e := by
    intro i j hij
    have := Subtype.ext hij
    have := (monoSet d).equivFin.symm.injective this
    exact Fin.castLE_injective hN this
  have hem : ∀ i, e i ∈ monoSet d := fun i => ((monoSet d).equivFin.symm (Fin.castLE hN i)).2
  refine ⟨fun i => gridPt (e i), fun v => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hNpos
  · exact ⟨0, by simp, fun i => Fin.elim0 i⟩
  haveI : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  obtain ⟨P, hP, hv⟩ := grid_interpolation d (fun p => v (Function.invFun e p))
  refine ⟨P, hP, fun i => ?_⟩
  rw [hv (e i) (hem i), Function.leftInverse_invFun he i]

/-- **Proposition 5.2 (generic arbitrary-label interpolation).** If `N ≤ M_d = binom(d+2,2)`,
the configurations of `N` points on which every value vector (hence every binary labelling) is
realisable in degree `d` form an open dense subset of `(ℝ²)^N`; by `goodConfig_iff_gram` it is
the non-vanishing set of a polynomial in the coordinates, i.e. Zariski open. -/
theorem generic_interpolation (d N : ℕ) (hN : N ≤ (d + 2).choose 2) :
    IsOpen {z : Fin N → Plane | GoodConfig d z} ∧ Dense {z : Fin N → Plane | GoodConfig d z} := by
  classical
  rw [← card_monoSet] at hN
  have hcont : Continuous fun z : Fin N → Plane =>
      (vandermonde d z * (vandermonde d z).transpose).det := by
    have : Continuous fun z : Fin N → Plane => vandermonde d z := by
      refine continuous_pi fun i => continuous_pi fun p => ?_
      simp only [vandermonde, veronese]
      fun_prop
    fun_prop
  constructor
  · simp_rw [goodConfig_iff_gram]
    exact isOpen_ne_fun hcont continuous_const
  · obtain ⟨g, hg⟩ := exists_goodConfig d N hN
    rw [Metric.dense_iff]
    intro z r hr
    -- the Gram determinant along the segment from `z` to `g` is a polynomial in `t`
    let Mt : Matrix (Fin N) (Mono d) (Polynomial ℝ) := fun i p =>
      (Polynomial.C (z i 0) + Polynomial.C (g i 0 - z i 0) * Polynomial.X) ^ p.1.1 *
        (Polynomial.C (z i 1) + Polynomial.C (g i 1 - z i 1) * Polynomial.X) ^ p.1.2
    let q : Polynomial ℝ := (Mt * Mt.transpose).det
    have hq : ∀ t : ℝ, q.eval t =
        (vandermonde d (z + t • (g - z)) * (vandermonde d (z + t • (g - z))).transpose).det := by
      intro t
      rw [show q.eval t = Polynomial.evalRingHom t q from rfl, RingHom.map_det,
        RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map]
      congr 2
      · ext i p
        simp [Mt, vandermonde, veronese]
        ring
      · ext i p
        simp [Mt, vandermonde, veronese]
        ring
    have hq1 : q ≠ 0 := by
      intro h0
      have := hq 1
      rw [h0, Polynomial.eval_zero] at this
      have hg' := (goodConfig_iff_gram d g).1 hg
      apply hg'
      rw [this]
      congr 3 <;> simp
    set δ := r / (‖g - z‖ + 1)
    have hδ : 0 < δ := div_pos hr (by positivity)
    obtain ⟨t, ht, hqt⟩ : ∃ t ∈ Set.Ioo 0 δ, q.eval t ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hq1
      apply Polynomial.eq_zero_of_infinite_isRoot
      exact (Set.Ioo_infinite hδ).mono fun t ht => hc t ht
    refine ⟨z + t • (g - z), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht.1]
      have hlt : t < r / (‖g - z‖ + 1) := ht.2
      rw [lt_div_iff₀ (by positivity)] at hlt
      nlinarith [norm_nonneg (g - z), ht.1]
    · show GoodConfig d (z + t • (g - z))
      rw [goodConfig_iff_gram, ← hq]
      exact hqt

end PlanarSep
