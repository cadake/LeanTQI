import LeanTQI.MatrixPredicate
-- import LeanCopilot

set_option profiler true

variable {𝕂 𝕂' E F α R : Type*}
variable {m n l : Type*}

namespace ENNReal

open scoped NNReal ENNReal

variable (p : ℝ≥0∞)
variable [Fact (1 ≤ p)]

theorem toReal_lt_toReal_if (p q : ℝ≥0∞) (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p < q) : p.toReal < q.toReal := by
  simp_all only [ne_eq, not_false_eq_true, toReal_lt_toReal]

theorem ge_one_ne_zero : p ≠ 0 := by
  have pge1 : 1 ≤ p := Fact.out
  intro peq0
  rw [peq0] at pge1
  simp_all only [nonpos_iff_eq_zero, one_ne_zero]

theorem ge_one_toReal_ne_zero (hp : p ≠ ∞) : p.toReal ≠ 0 := by
  have pge1 : 1 ≤ p := Fact.out
  intro preq0
  have : p = 0 := by
    refine (ENNReal.toReal_eq_toReal_iff' hp ?hy).mp preq0
    trivial
  rw [this] at pge1
  simp_all only [nonpos_iff_eq_zero, one_ne_zero]

end ENNReal


namespace Finset

open scoped NNReal ENNReal

variable (p : ℝ≥0∞)
variable [RCLike 𝕂] [Fintype m] [Fintype n]
variable [Fact (1 ≤ p)]

omit [Fintype m] in
theorem single_le_row [OrderedAddCommMonoid α] (M : m → n → α) (h : ∀ i j, 0 ≤ M i j) (i : m) (j : n) :
    M i j ≤ ∑ k, M i k := by
  apply Finset.single_le_sum (f:=fun j => M i j) (fun i_1 _ ↦ h i i_1) (Finset.mem_univ j)

theorem row_le_sum [OrderedAddCommMonoid α] (M : m → n → α) (h : ∀ i j, 0 ≤ M i j) (i : m) :
    ∑ j, M i j ≤ ∑ k, ∑ l, M k l := by
  exact Finset.single_le_sum (f := fun i => ∑ j, M i j) (fun i _ ↦ Fintype.sum_nonneg (h i)) (Finset.mem_univ i)

theorem single_le_sum' [OrderedAddCommMonoid α] (M : m → n → α) (h : ∀ i j, 0 ≤ M i j) (i : m) (j : n) :
    M i j ≤ ∑ k, ∑ l, M k l := by
  exact Preorder.le_trans (M i j) (∑ k : n, M i k) (∑ k : m, ∑ l : n, M k l)
    (Finset.single_le_row M h i j) (Finset.row_le_sum M h i)

-- theorem single_le_row (i : m) (j : n) : ‖M i j‖ ≤ ∑ k, ‖M i k‖ := by
--   have h : ∀ i j, 0 ≤ ‖M i j‖ := by exact fun i j ↦ norm_nonneg (M i j)
--   change (fun j => norm (M i j)) j ≤ ∑ k, (fun k => norm (M i k)) k
--   apply Finset.single_le_sum (f:=fun j => norm (M i j))
--   intro k
--   exact fun _ ↦ h i k
--   exact Finset.mem_univ j

-- theorem row_le_sum (i : m) : ∑ j, ‖M i j‖ ≤ ∑ k, ∑ l, ‖M k l‖ := by
--   have h : ∀ i j, 0 ≤ ‖M i j‖ := by exact fun i j ↦ norm_nonneg (M i j)
--   change (fun i => ∑ j, norm (M i j)) i ≤ ∑ k : m, ∑ l : n, ‖M k l‖
--   apply Finset.single_le_sum (f := fun i => ∑ j, norm (M i j))
--   exact fun i _ ↦ Fintype.sum_nonneg (h i)
--   exact Finset.mem_univ i

-- theorem single_le_sum (M : Matrix m n 𝕂) : ∀ i j, ‖M i j‖ ≤ ∑ k, ∑ l, ‖M k l‖ := by
--   exact fun i j ↦
--     Preorder.le_trans ‖M i j‖ (∑ k : n, ‖M i k‖) (∑ k : m, ∑ l : n, ‖M k l‖) (single_le_row M i j)
--       (row_le_sum M i)

theorem sum_sum_le_sum_sum [OrderedAddCommMonoid α] (f g : m → n → α) (h : ∀ i j, f i j ≤ g i j) :
    ∑ i, ∑ j, f i j ≤ ∑ i, ∑ j, g i j := by
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact h i j

theorem sum_sum_nonneg [OrderedAddCommMonoid α] (f : m → n → α) (h : ∀ i j, 0 ≤ f i j) :
    0 ≤ ∑ i, ∑ j, f i j := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact h i j



end Finset



noncomputable section

namespace Matrix

section LpNorm

open scoped NNReal ENNReal Finset Matrix

-- local notation "‖" e "‖ₚ" => Norm.norm e

variable (p q p₁ p₂ : ℝ≥0∞)
variable [RCLike 𝕂] [Fintype m] [Fintype n] [Fintype l]
variable [Fact (1 ≤ p)]

/-- synonym for matrix with lp norm-/
@[simp]
abbrev MatrixP (m n α : Type*) (_p : ℝ≥0∞) := Matrix m n α

/-- a function of lpnorm, of which LpNorm p M = ‖M‖ for p-/
@[simp]
def LpNorm (p : ℝ≥0∞) (M : Matrix m n 𝕂) : ℝ :=
  -- if p = 0 then {i | ‖M i‖ ≠ 0}.toFinite.toFinset.card
  if p = ∞ then ⨆ i, ⨆ j, ‖M i j‖
  else (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal)

-- notation "‖" M "‖ₚ" => LpNorm p M
-- notation "‖" M "‖q" => LpNorm q M

/-- a function of lpnorm, of which LpNorm p M = ‖M‖₊ for p-/
@[simp]
def LpNNNorm (p : ℝ≥0∞) (M : Matrix m n 𝕂) : ℝ :=
  if p = ∞ then ⨆ i, ⨆ j, ‖M i j‖₊
  else (∑ i, ∑ j, ‖M i j‖₊ ^ p.toReal) ^ (1 / p.toReal)

variable (M N : Matrix m n 𝕂)
variable (A : Matrix m n 𝕂) (B : Matrix n l 𝕂)
variable (r : R)

/-- Seminormed group instance (using lp norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def lpMatrixSeminormedAddCommGroup  [SeminormedAddCommGroup 𝕂] :
    SeminormedAddCommGroup (MatrixP m n 𝕂 p) :=
  inferInstanceAs (SeminormedAddCommGroup (PiLp p fun _i : m => PiLp p fun _j : n => 𝕂))
#check lpMatrixSeminormedAddCommGroup (m:=m) (n:=n) (𝕂:=𝕂) p

-- todo : notation

/-- Normed group instance (using lp norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def lpMatrixNormedAddCommGroup [Fact (1 ≤ p)] [NormedAddCommGroup 𝕂] :
    NormedAddCommGroup (MatrixP m n 𝕂 p) := by
  let ist := inferInstanceAs (NormedAddCommGroup (PiLp p fun _i : m => PiLp p fun _j : n => 𝕂))
  exact ist

-- def equiv : (MatrixP m n 𝕂 p) ≃ (Matrix m n 𝕂) := Equiv.refl _

-- instance [SMul R (Matrix m n 𝕂)] : SMul R (MatrixP m n 𝕂 p) :=
--   (by infer_instance : SMul R (Matrix m n 𝕂))

-- todo
-- set_option diagnostics true in
-- set_option maxHeartbeats 30000 in
-- set_option trace.Meta.synthInstance true in
-- @[local instance]
-- theorem lpMatrixBoundedSMul [Fact (1 ≤ p)] [SeminormedRing R] [SeminormedAddCommGroup 𝕂] [Module R 𝕂]
--     [BoundedSMul R 𝕂] :
--     BoundedSMul R (WithLp p (Matrix m n 𝕂)) :=
--   (by infer_instance : BoundedSMul R (PiLp p fun i : m => PiLp p fun j : n => 𝕂))

/-- Normed space instance (using lp norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def lpMatrixNormedSpace [NormedField R] [SeminormedAddCommGroup 𝕂] [NormedSpace R 𝕂] :
    NormedSpace R (MatrixP m n 𝕂 p) :=
  (by infer_instance : NormedSpace R (PiLp p fun i : m => PiLp p fun j : n => 𝕂))
#check (inferInstance : PseudoEMetricSpace (MatrixP m n 𝕂 p))

-- @[local instance]
-- def lpMatrixBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup 𝕂] [Module R 𝕂]
--     [BoundedSMul R 𝕂] :
--     BoundedSMul R (MatrixP m n 𝕂 p) where
--   dist_pair_smul' := sorry
--   dist_smul_pair' := sorry

-- instance istPDist : Dist (MatrixP m n 𝕂 p) := {
--   dist := fun M N => ‖M - N‖
-- }

#check (inferInstance : Dist (MatrixP m n 𝕂 p))
#check (inferInstance : MetricSpace (MatrixP m n 𝕂 p))
#check (inferInstance : PseudoMetricSpace (MatrixP m n 𝕂 p))




@[simp]
theorem lp_nnnorm_def (M : MatrixP m n 𝕂 p) (hp : p ≠ ∞) :
    ‖M‖₊ = (∑ i, ∑ j, ‖M i j‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp only [MatrixP, coe_nnnorm, PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp),
    NNReal.coe_rpow, NNReal.coe_sum]
  have : ∀ x, 0 ≤ ∑ x_1 : n, ‖M x x_1‖ ^ p.toReal := by
    intro x
    have : ∀ x_1, 0 ≤ ‖M x x_1‖ ^ p.toReal := by
      intro x_1
      refine Real.rpow_nonneg ?hx p.toReal
      exact norm_nonneg (M x x_1)
    exact Fintype.sum_nonneg this
  have prne0 : p.toReal ≠ 0 := by
    exact ENNReal.ge_one_toReal_ne_zero p hp
  conv_lhs =>
    enter [1, 2]
    intro x
    rw [← Real.rpow_mul,mul_comm,  mul_one_div_cancel, Real.rpow_one]
    rfl
    exact prne0
    exact this x

@[simp]
theorem lp_norm_eq_ciSup (M : MatrixP m n 𝕂 p) (hp : p = ∞) :
    ‖M‖ = ⨆ i, ⨆ j, ‖M i j‖ := by
  have : p ≠ 0 := by exact ENNReal.ge_one_ne_zero p
  have : p ≠ 0 := by exact ENNReal.ge_one_ne_zero p
  simp only [MatrixP, norm, if_neg this, if_pos hp]

omit [Fact (1 ≤ p)] in
@[simp]
theorem lpnorm_eq_ciSup (M : Matrix m n 𝕂) (hp : p = ∞) :
    LpNorm p M = ⨆ i, ⨆ j, ‖M i j‖ := by
  simp only [LpNorm, if_pos hp]

@[simp]
theorem lp_norm_def (M : MatrixP m n 𝕂 p) (hp : p ≠ ∞) :
    ‖M‖ = (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal) :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) (lp_nnnorm_def p M hp)).trans <| by simp only [one_div,
    NNReal.coe_rpow, NNReal.coe_sum, coe_nnnorm]

omit [Fact (1 ≤ p)] in
@[simp]
theorem lpnorm_def (M : Matrix m n 𝕂) (hp : p ≠ ∞) :
    LpNorm p M = (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal) := by
  simp only [LpNorm, if_neg hp]

@[simp]
theorem lp_nnnorm_eq_ciSup (M : MatrixP m n 𝕂 p) (hp : p = ∞) :
    ‖M‖₊ = ⨆ i, ⨆ j, ‖M i j‖₊ := by
  ext
  rw [coe_nnnorm, lp_norm_eq_ciSup, NNReal.coe_iSup]
  simp only [NNReal.coe_iSup, coe_nnnorm]
  assumption

theorem lp_norm_eq_lpnorm : ‖M‖ = LpNorm p M := by
  by_cases h : p = ⊤
  · rw [lp_norm_eq_ciSup p M h, LpNorm, if_pos h]
  · rw [lp_norm_def p M h, LpNorm, if_neg h]

example (hp : p ≠ ∞) :
    ‖M‖₊ = (∑ i, ∑ j, ‖M i j‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  rw [lp_nnnorm_def p M hp]

example (M : (MatrixP m n 𝕂 2)) :
    ‖M‖₊ = (∑ i, ∑ j, ‖M i j‖₊ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [lp_nnnorm_def]
  simp only [ENNReal.toReal_ofNat, NNReal.rpow_ofNat, one_div]
  trivial

-- Lemma lpnorm0_eq0 A : `[ A ] = 0 -> A = 0.
-- #check norm_eq_zero

-- Lemma lpnormZ a A : `[ a *: A ] = `|a| * `[ A ].
-- #check norm_smul
-- example (r : R) [NormedField R] [NormedSpace R (MatrixP m n 𝕂 p)] : ‖r • M‖ = ‖r‖ * ‖M‖ := by
  -- exact norm_smul r M

-- Lemma lpnorm_triangle A B : `[ A + B ] <= `[ A ] + `[ B ].
-- #check norm_add_le M N
theorem lpnorm_triangle : LpNorm p (M + N) ≤ LpNorm p M + LpNorm p N := by
  rw [← lp_norm_eq_lpnorm, ← lp_norm_eq_lpnorm, ← lp_norm_eq_lpnorm]
  exact norm_add_le M N

-- Lemma lpnorm_continuous p m n : continuous (@lpnorm R p m n).
example : Continuous fun (M : MatrixP m n 𝕂 p) => ‖M‖ := by
  exact continuous_norm

theorem lpnorm_continuous_at_m : Continuous (LpNorm (m := m) (n := n) (𝕂 := 𝕂) p) := by
  have : (fun M : MatrixP m n 𝕂 p => ‖M‖) = (LpNorm (m := m) (n := n) (𝕂 := 𝕂) p) := by
    ext
    rw [@lp_norm_eq_lpnorm]
  rw [← this]
  exact continuous_norm






-- todo
theorem lpnorm_tendsto_maxnorm (h : p = ∞) (M : Matrix m n 𝕂) :
    (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal) =  ⨆ i, ⨆ j, ‖M i j‖ := by
  sorry












example [Fact (1 ≤ p)] : p ≠ 0 := ENNReal.ge_one_ne_zero p

example [Fact (1 ≤ p)] (h : p ≠ ⊤) : p⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h

example [Fact (1 ≤ p)] (h : p ≠ ⊤) : p.toReal ≠ 0 := ENNReal.ge_one_toReal_ne_zero p h

example [Fact (1 ≤ p)] (h : p ≠ ⊤) : p.toReal⁻¹ ≠ 0 := inv_ne_zero (ENNReal.ge_one_toReal_ne_zero p h)

example [Fact (1 ≤ p)] : 0 ≤ p := by exact zero_le p

example [Fact (1 ≤ p)] : 0 ≤ p.toReal := by exact ENNReal.toReal_nonneg

omit [Fintype n] in
theorem le_iSup (f : m → n → ℝ) (i : m) : f i ≤ ⨆ i, f i :=
  le_ciSup (Finite.bddAbove_range f) i

omit [Fintype m] in
theorem le_iSup' (f : m → n → ℝ) (j : n) : (f · j) ≤ ⨆ (j : n), (f · j):=
  le_ciSup (f := fun j i => f i j) (Finite.bddAbove_range fun j i ↦ f i j) j

theorem le_iSup_iSup (f : m → n → ℝ) (i : m) (j : n) : f i j ≤ ⨆ i, ⨆ j, f i j :=
  le_trans (le_ciSup (Finite.bddAbove_range (f i)) j)
    (le_ciSup (f := fun i => ⨆ j, f i j) (Finite.bddAbove_range fun i ↦ ⨆ j, f i j) i)

theorem le_iSup_iSup' (f : m → n → ℝ) (i : m) (j : n) : f i j ≤ ⨆ j, ⨆ i, f i j :=
  le_trans (le_ciSup (Finite.bddAbove_range (f i)) j)
    (ciSup_mono (Finite.bddAbove_range fun j ↦ ⨆ i, f i j)
      (fun j => le_ciSup (f := fun i => f i j) (Finite.bddAbove_range fun i ↦ f i j) i))

omit [Fintype m] [Fintype n] in
theorem iSup_iSup_nonneg : 0 ≤ ⨆ i, ⨆ j, ‖M i j‖ :=
  Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => norm_nonneg (M i j)))

theorem elem_le_iSup_iSup (f : m → n → ℝ) (i : m) (j : n) : f i j ≤ ⨆ i, ⨆ j, f i j :=
  le_iSup_iSup (f := fun i j => f i j) i j

theorem elem_le_iSup_iSup' (f : m → n → ℝ) (i : m) (j : n) : f i j ≤ ⨆ j, ⨆ i, f i j :=
  le_iSup_iSup' (f := fun i j => f i j) i j

theorem iSup_comm' (f : m → n → ℝ) (h : ∀ i j, 0 ≤ f i j) : ⨆ i, ⨆ j, f i j = ⨆ j, ⨆ i, f i j := by
  have nneg : 0 ≤ ⨆ i, ⨆ j, f i j := Real.iSup_nonneg (fun i => Real.iSup_nonneg (h i))
  have nneg' : 0 ≤ ⨆ j, ⨆ i, f i j := Real.iSup_nonneg (fun j => Real.iSup_nonneg fun i ↦ h i j)
  apply le_antisymm ((fun a age0 h => Real.iSup_le (fun i => Real.iSup_le (h i) age0) age0)
    (⨆ i, ⨆ j, f j i) nneg' (fun i j => elem_le_iSup_iSup' f i j))
  have : (a : ℝ) → (age0 : 0 ≤ a) → (∀ (i : m) (j : n), f i j ≤ a) → (⨆ j, ⨆ i, f i j ≤ a) :=
    fun a age0 h => Real.iSup_le (fun i => Real.iSup_le (fun i_1 ↦ h i_1 i) age0) age0
  exact this (⨆ i, ⨆ j, f i j) nneg (fun i j => elem_le_iSup_iSup f i j)












theorem lpnorm_eq0_iff : LpNorm p M = 0 ↔ M = 0 := by
  rw [← lp_norm_eq_lpnorm]
  exact norm_eq_zero

theorem lpnorm_nonneg : 0 ≤ LpNorm p M := by
  rw [← lp_norm_eq_lpnorm]
  exact norm_nonneg M

omit [Fact (1 ≤ p)] in
theorem lpnorm_rpow_nonneg : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ p.toReal :=
  Finset.sum_sum_nonneg (fun i j => ‖M i j‖ ^ p.toReal) (fun i j => Real.rpow_nonneg (norm_nonneg (M i j)) _)

theorem lpnorm_rpow_ne0 (h : LpNorm p M ≠ 0) (h' : p ≠ ⊤) : ∑ i, ∑ j, ‖M i j‖ ^ p.toReal ≠ 0 := by
  simp only [LpNorm, one_div, ne_eq] at h
  intro g
  rw [g] at h
  simp only [if_neg h'] at h
  rw [Real.zero_rpow <| inv_ne_zero <| ENNReal.ge_one_toReal_ne_zero p h'] at h
  contradiction

theorem lpnorm_rpow_pos (h : LpNorm p M ≠ 0) (h' : p ≠ ⊤) : 0 < ∑ i, ∑ j, ‖M i j‖ ^ p.toReal := by
  have ge0 := lpnorm_rpow_nonneg p M
  have ne0 := lpnorm_rpow_ne0 p M
  exact lt_of_le_of_ne ge0 fun a ↦ ne0 h h' (id (Eq.symm a))

theorem lpnorm_p_one_nonneg : 0 ≤ ∑ i, ∑ j, ‖M i j‖ := by
  let ge0 := lpnorm_rpow_nonneg 1 M
  simp at ge0
  exact ge0

theorem lpnorm_p_one_ne0 (h : M ≠ 0) : ∑ i, ∑ j, ‖M i j‖ ≠ 0 := by
  have : LpNorm 1 M ≠ 0 := by
    by_contra h
    have : M = 0 := (lpnorm_eq0_iff 1 M).mp h
    contradiction
  let ne0 := lpnorm_rpow_ne0 1 M this (ENNReal.one_ne_top)
  simp only [ENNReal.one_toReal, Real.rpow_one, ne_eq] at ne0
  exact ne0

theorem lpnorm_p_one_pos (h : M ≠ 0) : 0 < ∑ i, ∑ j, ‖M i j‖ := by
  have ge0 := lpnorm_p_one_nonneg M
  have ne0 := lpnorm_p_one_ne0 M
  exact lt_of_le_of_ne ge0 fun a ↦ ne0 h (id (Eq.symm a))

omit [Fintype m] [Fintype n] in
theorem norm_rpow_rpow_inv (i : m) (j : n) (h : ¬p = ⊤) : ‖M i j‖ = (‖M i j‖ ^ p.toReal) ^ p.toReal⁻¹ := by
  exact Eq.symm (Real.rpow_rpow_inv (norm_nonneg (M i j)) (ENNReal.ge_one_toReal_ne_zero p h))

theorem lpnorm_elem_le_norm (i : m) (j : n) : ‖M i j‖ ≤ LpNorm p M := by
  simp only [LpNorm, one_div]
  by_cases h : p = ⊤
  · simp only [if_pos h]
    exact elem_le_iSup_iSup (fun i j => ‖M i j‖) i j
  · simp only [if_neg h]
    rw [norm_rpow_rpow_inv p M i j h]
    have : ‖M i j‖ ^ p.toReal ≤ ∑ i : m, ∑ j : n, ‖M i j‖ ^ p.toReal :=
      Finset.single_le_sum' (M := fun k l => ‖M k l‖ ^ p.toReal)
        (fun i j => Real.rpow_nonneg (norm_nonneg (M i j)) p.toReal) i j
    exact Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg (M i j)) p.toReal) this
      (inv_nonneg_of_nonneg (ENNReal.toReal_nonneg))

theorem lpnorm_elem_div_norm (i : m) (j : n) : 0 ≤ ‖M i j‖ / LpNorm p M ∧ ‖M i j‖ / LpNorm p M ≤ 1 := by
  constructor
  · rw [division_def]
    apply mul_nonneg (norm_nonneg (M i j)) (inv_nonneg_of_nonneg <| lpnorm_nonneg p M)
  · apply div_le_one_of_le₀ (lpnorm_elem_le_norm p M i j) (lpnorm_nonneg p M)

-- Lemma lpnorm_nincr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) :
--   1 <= p1 <= p2 -> lpnorm p1 A >= lpnorm p2 A.
theorem lpnorm_antimono (p₁ p₂ : ℝ≥0∞) [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (h₁ : p₁ ≠ ⊤) (h₂ : p₂ ≠ ⊤) (ple : p₁ ≤ p₂) :
    LpNorm p₂ M ≤ LpNorm p₁ M := by
  by_cases h : p₁ = p₂
  · rw [h]
  by_cases g : LpNorm p₂ M = 0
  · rw [g]
    rw [← lp_norm_eq_lpnorm] at g
    rw [(lpnorm_eq0_iff p₁ M).mpr (norm_eq_zero.mp g)]
  have eq1 : ∑ i, ∑ j, (‖M i j‖ / LpNorm p₂ M)^p₂.toReal = 1 := by
    simp only [LpNorm, one_div, if_neg h₂]
    have : ∀ i j, (‖M i j‖ / (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal) ^ p₂.toReal⁻¹) ^ p₂.toReal =
                  (‖M i j‖ ^ p₂.toReal) / ((∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal)) := by
      intro i j
      rw [Real.div_rpow (norm_nonneg (M i j))]
      congr
      rw [← Real.rpow_mul, mul_comm, CommGroupWithZero.mul_inv_cancel, Real.rpow_one]
      · exact ENNReal.ge_one_toReal_ne_zero p₂ h₂
      · exact lpnorm_rpow_nonneg p₂ M
      · exact Real.rpow_nonneg (lpnorm_rpow_nonneg p₂ M) p₂.toReal⁻¹
    simp_rw [this]
    have : ∑ x : m, ∑ x_1 : n, ‖M x x_1‖ ^ p₂.toReal / ∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal =
           (∑ x : m, ∑ x_1 : n, ‖M x x_1‖ ^ p₂.toReal) / (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal) := by
      simp_rw [div_eq_inv_mul]
      conv_lhs =>
        enter [2]
        intro i
        rw [← Finset.mul_sum]
      rw [← Finset.mul_sum]
    simp_rw [this]
    rw [div_self (lpnorm_rpow_ne0 p₂ M g h₂)]
  have le1 : ∑ i, ∑ j, (‖M i j‖ / LpNorm p₂ M)^p₂.toReal ≤ ∑ i, ∑ j, (‖M i j‖ / LpNorm p₂ M)^p₁.toReal := by
    apply Finset.sum_sum_le_sum_sum
    intro i j
    by_cases h' : ‖M i j‖ / LpNorm p₂ M = 0
    · rw [h', Real.zero_rpow (ENNReal.ge_one_toReal_ne_zero p₁ h₁), Real.zero_rpow (ENNReal.ge_one_toReal_ne_zero p₂ h₂)]
    refine Real.rpow_le_rpow_of_exponent_ge ?h.h.hx0 (lpnorm_elem_div_norm p₂ M i j).2 ((ENNReal.toReal_le_toReal h₁ h₂).mpr ple)
    exact lt_of_le_of_ne (lpnorm_elem_div_norm p₂ M i j).1 fun a ↦ h' (id (Eq.symm a))
  have eq2 : ∑ i, ∑ j, (‖M i j‖ / LpNorm p₂ M) ^ p₁.toReal = ((LpNorm p₁ M) / (LpNorm p₂ M)) ^ p₁.toReal := by
    have : ∀ i j, (‖M i j‖ / LpNorm p₂ M) ^ p₁.toReal = ‖M i j‖ ^ p₁.toReal * ((LpNorm p₂ M) ^ p₁.toReal)⁻¹ := by
      intro i j
      rw [Real.div_rpow (norm_nonneg (M i j)) (lpnorm_nonneg p₂ M), division_def]
    simp_rw [this]
    conv_lhs =>
      enter [2]
      intro i
      rw [← Finset.sum_mul]
    rw [← Finset.sum_mul]
    have : (∑ i : m, ∑ i_1 : n, ‖M i i_1‖ ^ p₁.toReal) = (LpNorm p₁ M) ^ p₁.toReal := by
      simp only [LpNorm, if_neg h₁, one_div, ite_pow]
      rw [← Real.rpow_mul, mul_comm, CommGroupWithZero.mul_inv_cancel, Real.rpow_one]
      exact ENNReal.ge_one_toReal_ne_zero p₁ h₁
      apply lpnorm_rpow_nonneg
    rw [this]
    rw [← division_def, ← Real.div_rpow (lpnorm_nonneg p₁ M) (lpnorm_nonneg p₂ M)]
  have le2 : 1 ≤ ((LpNorm p₁ M) / (LpNorm p₂ M))^p₁.toReal := by
    rw [eq2, eq1] at le1
    exact le1
  have le3 : 1 ≤ (LpNorm p₁ M) / (LpNorm p₂ M) := by
    rw [Eq.symm (Real.one_rpow p₁.toReal)] at le2
    apply (Real.rpow_le_rpow_iff (zero_le_one' ℝ) _ ((ENNReal.toReal_pos_iff_ne_top p₁).mpr h₁)).mp le2
    rw [div_eq_inv_mul]
    exact Left.mul_nonneg (inv_nonneg_of_nonneg <| lpnorm_nonneg p₂ M) (lpnorm_nonneg p₁ M)
  have : 0 < LpNorm p₂ M :=
    lt_of_le_of_ne (lpnorm_nonneg p₂ M) fun a ↦ g (id (Eq.symm a))
  exact (one_le_div₀ this).mp le3


theorem lpnorm_antimono' (p₁ p₂ : ℝ) (hp₁ : 1 ≤ p₁) (hp₂ : 1 ≤ p₂) (ple : p₁ ≤ p₂) (f : m → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, (f i) ^ p₂) ^ p₂⁻¹ ≤ (∑ i, (f i) ^ p₁) ^ p₁⁻¹ := by
  let A : Matrix m Unit ℝ := fun i _ => f i
  have : (∑ i : m, f i ^ p₂) = (∑ i : m, ∑ _ : Unit, (A i ()) ^ p₂) := by
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_const, Finset.card_singleton,
      one_smul]
  simp_rw [this]
  have : (∑ i : m, f i ^ p₁) = (∑ i : m, ∑ _ : Unit, (A i ()) ^ p₁) := by
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_const, Finset.card_singleton,
      one_smul]
  simp_rw [this]
  conv_lhs =>
    enter [1, 2]
    intro i
    enter [2]
    intro
    rw [show A i () = ‖A i ()‖ by exact Eq.symm (Real.norm_of_nonneg (hf i))]
  conv_rhs =>
    enter [1, 2]
    intro i
    enter [2]
    intro
    rw [show A i () = ‖A i ()‖ by exact Eq.symm (Real.norm_of_nonneg (hf i))]
  have : (∑ i : m, ∑ _ : Unit, ‖A i ()‖ ^ p₂) ^ p₂⁻¹ = LpNorm (ENNReal.ofReal p₂) A := by
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Real.norm_eq_abs, Finset.sum_const,
      Finset.card_singleton, one_smul, LpNorm, ENNReal.ofReal_ne_top, ↓reduceIte,
      Finset.sum_singleton, one_div, show PUnit.unit = () by rfl]
    have : (ENNReal.ofReal p₂).toReal = p₂ := by
      simp only [ENNReal.toReal_ofReal_eq_iff]
      linarith
    rw [this]
  rw [this]
  have : (∑ i : m, ∑ _ : Unit, ‖A i ()‖ ^ p₁) ^ p₁⁻¹ = LpNorm (ENNReal.ofReal p₁) A := by
    simp only [Finset.univ_unique, PUnit.default_eq_unit, Real.norm_eq_abs, Finset.sum_const,
      Finset.card_singleton, one_smul, LpNorm, ENNReal.ofReal_ne_top, ↓reduceIte,
      Finset.sum_singleton, one_div, show PUnit.unit = () by rfl]
    have : (ENNReal.ofReal p₁).toReal = p₁ := by
      simp only [ENNReal.toReal_ofReal_eq_iff]
      linarith
    rw [this]
  rw [this]
  have ist1 : Fact (1 ≤ ENNReal.ofReal p₂) := {out := ENNReal.one_le_ofReal.mpr hp₂}
  have ist2 : Fact (1 ≤ ENNReal.ofReal p₁) := {out := ENNReal.one_le_ofReal.mpr hp₁}
  apply lpnorm_antimono
  exact ENNReal.ofReal_ne_top
  exact ENNReal.ofReal_ne_top
  exact ENNReal.ofReal_le_ofReal ple








-- todo

-- Lemma lpnorm_ndecr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) :
--   1 <= p1 <= p2 ->
--   lpnorm p1 A / ((m * n)%:R `^ p1^-1)%:C <= lpnorm p2 A / ((m * n)%:R `^ p2^-1)%:C.
example [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (ple : p₁ ≤ p₂) (m n : ℕ) (M : Matrix (Fin m) (Fin n) 𝕂) :
    LpNorm p₁ M / (m * n) ^ (1 / p₁.toReal) ≤ LpNorm p₂ M / (m * n) ^ (1 / p₂.toReal) := by
  sorry










#check iSup_comm
-- Lemma lpnorm_trmx p q r (M: 'M[C]_(q,r)) : lpnorm p (M^T) = lpnorm p M.
@[simp]
theorem lpnorm_transpose (M : MatrixP m n 𝕂 p) : ‖Mᵀ‖ = ‖M‖ := by
  by_cases hp : p = ⊤
  · rw [lp_norm_eq_ciSup p M hp, lp_norm_eq_ciSup p Mᵀ hp, transpose]
    dsimp only [of_apply]
    rw [eq_comm]
    apply iSup_comm' (fun i j ↦ ‖M i j‖) (fun i j ↦ norm_nonneg (M i j))
  · rw [lp_norm_def p M hp, lp_norm_def p Mᵀ hp, transpose]
    dsimp only [of_apply]
    rw [Finset.sum_comm]

-- Lemma lpnorm_diag p q (D : 'rV[C]_q) : lpnorm p (diag_mx D) = lpnorm p D.
theorem lpnorm_diag [DecidableEq m] (d : m → 𝕂) (h : p ≠ ⊤) :
    LpNorm p (Matrix.diagonal d) = (∑ i, ‖d i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  simp only [LpNorm, one_div, if_neg h, diagonal, of_apply]
  have sum_eq_single : ∀ (i : m), ∑ j, ‖if i = j then d i else 0‖ ^ p.toReal = ‖d i‖ ^ p.toReal := by
    intro i
    nth_rw 2 [← (show (if i = i then d i else 0) = d i by simp only [↓reduceIte])]
    apply Finset.sum_eq_single_of_mem (f := fun j => ‖if i = j then d i else 0‖ ^ p.toReal) i (Finset.mem_univ i)
    intro j _ jnei
    rw [ne_comm] at jnei
    simp only [if_neg jnei, norm_zero, le_refl]
    exact Real.zero_rpow (ENNReal.ge_one_toReal_ne_zero p h)
  conv_lhs =>
    enter [1, 2]
    intro x
    rw [sum_eq_single x]

-- Lemma lpnorm_conjmx p q r (M: 'M[C]_(q,r)) : lpnorm p (M^*m) = lpnorm p M.
@[simp]
theorem lpnorm_conjugate (M : MatrixP m n 𝕂 p) : ‖M^*‖ = ‖M‖ := by
  by_cases hp : p = ⊤
  · simp_rw [lp_norm_eq_ciSup p M hp, lp_norm_eq_ciSup p M^* hp, conjugate,
    RCLike.star_def, map_apply, RCLike.norm_conj]
  · simp_rw [lp_norm_def p M hp, lp_norm_def p M^* hp, conjugate, RCLike.star_def, map_apply,
    (show ∀ i j, ‖(starRingEnd 𝕂) (M i j)‖ = ‖M i j‖ by exact fun i j ↦ RCLike.norm_conj (M i j))]

-- Lemma lpnorm_adjmx p q r (M: 'M[C]_(q,r)) : lpnorm p (M^*t) = lpnorm p M.
@[simp]
theorem lpnorm_conjTranspose [DecidableEq m] [DecidableEq n] (M : MatrixP m n 𝕂 p) : ‖Mᴴ‖ = ‖M‖ := by
  simp only [conjTranspose_transpose_conjugate M, lpnorm_conjugate, lpnorm_transpose]

-- Lemma continuous_lpnorm p m n (A : 'M[C]_(m,n)) :
--   1 < p -> {for p, continuous (fun p0 : R => lpnorm p0 A)}.
theorem lpnorm_continuous_at_p (A : Matrix m n 𝕂) :
    ContinuousOn ((LpNorm (m := m) (n := n) (𝕂 := 𝕂) (M := A))) {p | 1 ≤ p ∧ p ≠ ∞} := by
  simp only [LpNorm]
  refine ContinuousOn.if ?hp ?hf ?hg
  · simp only [Set.setOf_eq_eq_singleton, Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
    intro p _ pnet pint
    simp only [frontier, closure_singleton, interior_singleton, Set.diff_empty,
      Set.mem_singleton_iff] at pint
    exact False.elim (pnet pint)
  · simp only [Set.setOf_eq_eq_singleton, closure_singleton]
    have : {(p : ℝ≥0∞) | 1 ≤ p ∧ p ≠ ⊤} ∩ {⊤} = ∅ := by
      simp only [ne_eq, Set.inter_singleton_eq_empty, Set.mem_setOf_eq, le_top, not_true_eq_false,
        and_false, not_false_eq_true]
    rw [this]
    exact continuousOn_empty fun _ ↦ ⨆ i, ⨆ j, ‖A i j‖
  · have : ({(p : ℝ≥0∞) | 1 ≤ p ∧ p ≠ ⊤} ∩ closure {a | ¬a = ⊤}) = {p | 1 ≤ p ∧ p ≠ ⊤} := by
      simp only [ne_eq, Set.inter_eq_left]
      exact fun p pin ↦ subset_closure pin.right
    rw [this]
    by_cases h : A = 0
    · have : Set.EqOn (fun (p : ℝ≥0∞) ↦ (∑ i : m, ∑ j : n, 0))
          (fun p ↦ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal)) {p | 1 ≤ p ∧ p ≠ ⊤} := by
        intro p pin
        have : Fact (1 ≤ p) := {out := pin.left}
        have : p.toReal ≠ 0 := ENNReal.ge_one_toReal_ne_zero p pin.right
        simp_rw [Finset.sum_const_zero, h, one_div, zero_apply, norm_zero,
          Real.zero_rpow this, Finset.sum_const_zero, Real.zero_rpow (inv_ne_zero this)]
      exact (continuousOn_congr this).mp continuousOn_const
    have eqon : Set.EqOn (fun (p : ℝ≥0∞) ↦ Real.exp (Real.log ((∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal))))
        (fun (p : ℝ≥0∞) ↦ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal)) {p | 1 ≤ p ∧ p ≠ ⊤} := by
      intro p pin
      have : Fact (1 ≤ p) := {out := pin.left}
      dsimp only
      rw [Real.exp_log]
      have ge0 : 0 ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal) :=
        Real.rpow_nonneg (lpnorm_rpow_nonneg p A) (1 / p.toReal)
      have ne0 : (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal) ≠ 0 := by
        rw [show (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal) = LpNorm p A by simp only [LpNorm, if_neg pin.right]]
        by_contra h'
        exact h ((lpnorm_eq0_iff p A).mp h')
      exact lt_of_le_of_ne ge0 (id (Ne.symm ne0))
    apply (continuousOn_congr eqon).mp
    apply ContinuousOn.rexp
    have eqon' : Set.EqOn (fun (y : ℝ≥0∞) ↦ (1 / y.toReal) * Real.log ((∑ i : m, ∑ j : n, ‖A i j‖ ^ y.toReal)))
        (fun y ↦ Real.log ((∑ i : m, ∑ j : n, ‖A i j‖ ^ y.toReal) ^ (1 / y.toReal))) {p | 1 ≤ p ∧ p ≠ ⊤} := by
      intro p pin
      dsimp
      rw [Real.log_rpow]
      have : Fact (1 ≤ p) := {out := pin.left}
      refine lpnorm_rpow_pos p A ?hx.h pin.right
      by_contra h'
      exact h <| (lpnorm_eq0_iff p A).mp h'
    apply (continuousOn_congr eqon').mp
    apply ContinuousOn.mul
    · refine ContinuousOn.div₀ continuousOn_const (ContinuousOn.mono ENNReal.continuousOn_toReal <| fun p pin => pin.right) ?_
      intro p pin
      have : Fact (1 ≤ p) := {out := pin.left}
      exact ENNReal.ge_one_toReal_ne_zero p pin.right
    · apply ContinuousOn.log
      refine continuousOn_finset_sum Finset.univ ?_
      intro i _
      refine continuousOn_finset_sum Finset.univ ?_
      intro j _
      by_cases h : ‖A i j‖ = 0
      · rw [h]
        have : Set.EqOn (fun (x : ℝ≥0∞) => 0) (fun x ↦ (0 : ℝ) ^ x.toReal) {p | 1 ≤ p ∧ p ≠ ⊤} := by
          intro p pin
          have : Fact (1 ≤ p) := {out := pin.left}
          dsimp
          simp_rw [(Real.rpow_eq_zero (Preorder.le_refl 0) (ENNReal.ge_one_toReal_ne_zero p pin.right)).mpr]
        exact (continuousOn_congr this).mp continuousOn_const
      · have : Set.EqOn (fun (x : ℝ≥0∞) ↦ Real.exp <| Real.log <| ‖A i j‖ ^ x.toReal)
            (fun x ↦ ‖A i j‖ ^ x.toReal) {p | 1 ≤ p ∧ p ≠ ⊤} := by
          intro p pin
          have : Fact (1 ≤ p) := {out := pin.left}
          dsimp
          rw [Real.exp_log]
          have ne0 : ‖A i j‖ ^ p.toReal ≠ 0 := (Real.rpow_ne_zero (norm_nonneg (A i j)) (ENNReal.ge_one_toReal_ne_zero p pin.right)).mpr h
          exact lt_of_le_of_ne (Real.rpow_nonneg (norm_nonneg (A i j)) p.toReal) (Ne.symm ne0)
        apply (continuousOn_congr this).mp
        apply ContinuousOn.rexp
        have : Set.EqOn (fun (y : ℝ≥0∞) ↦ y.toReal * Real.log (‖A i j‖)) (fun y ↦ Real.log (‖A i j‖ ^ y.toReal)) {p | 1 ≤ p ∧ p ≠ ⊤} := by
          intro p pin
          have : Fact (1 ≤ p) := {out := pin.left}
          dsimp
          rw [Real.log_rpow]
          exact lt_of_le_of_ne (norm_nonneg (A i j)) (Ne.symm h)
        exact (continuousOn_congr this).mp
          (ContinuousOn.mul (ContinuousOn.mono ENNReal.continuousOn_toReal <| fun p pin => pin.right) (continuousOn_const))
      intro p pin
      have : Fact (1 ≤ p) := {out := pin.left}
      exact lpnorm_rpow_ne0 p A (fun h' => h ((lpnorm_eq0_iff p A).mp h')) pin.right

theorem lpnorm_mul_le (ple2 : p ≤ 2) (h : p ≠ ⊤) : LpNorm p (A * B) ≤ (LpNorm p A) * (LpNorm p B) := by
  simp only [LpNorm, one_div, mul_ite, ite_mul, if_neg h]
  have Arpnn : ∀ i, 0 ≤ ∑ k : n, ‖A i k‖ ^ p.toReal :=
    fun i => Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (A i k)) p.toReal)
  have ApBpnn : 0 ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) * (∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal) := by
    exact Left.mul_nonneg (lpnorm_rpow_nonneg p A) (lpnorm_rpow_nonneg p B)
  have ppos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr h
  rw [← Real.mul_rpow (lpnorm_rpow_nonneg p A) (lpnorm_rpow_nonneg p B),
    Real.rpow_le_rpow_iff (lpnorm_rpow_nonneg p (A * B)) ApBpnn (inv_pos_of_pos ppos)]

  by_cases hp : p.toReal = 1
  -- simp only [hp, Real.rpow_one]
  case pos =>
    calc
      ∑ i : m, ∑ j : l, ‖(A * B) i j‖ ^ p.toReal ≤ ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ * ‖B k j‖) ^ p.toReal := by
        -- todo : extract
        apply Finset.sum_sum_le_sum_sum
        intro i j
        rw [Real.rpow_le_rpow_iff (norm_nonneg <| (A * B) i j)
          (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j))) ppos]
        exact (fun i j => norm_sum_le_of_le Finset.univ (fun k _ => NormedRing.norm_mul (A i k) (B k j))) i j
      _ = ∑ k : n, ∑ i : m, ∑ j : l, ‖A i k‖ * ‖B k j‖ := by
        simp only [hp, Real.rpow_one]
        conv_lhs =>
          enter [2]
          intro j
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
      _ = ∑ k : n, (∑ i : m, ‖A i k‖) * (∑ j : l, ‖B k j‖) := by
        congr
        ext k
        exact Eq.symm (Fintype.sum_mul_sum (fun i ↦ ‖A i k‖) fun j ↦ ‖B k j‖)
      _ ≤ ∑ k : n, (∑ i : m, ‖A i k‖) * ∑ k : n, (∑ j : l, ‖B k j‖) := by
        apply Finset.sum_le_sum
        intro y yin
        by_cases h' : ∑ i : m, ‖A i y‖ = 0
        · simp only [h', zero_mul, le_refl]
        rw [mul_le_mul_left]
        · exact Finset.single_le_sum (f := fun (i : n) => ∑ j : l, ‖B i j‖)
            (fun i _ => Finset.sum_nonneg (fun j _ => norm_nonneg (B i j))) yin
        · exact lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => norm_nonneg (A i y)))
            fun a ↦ h' (id (Eq.symm a))
      _ = (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) * ∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal := by
        simp only [hp, Real.rpow_one]
        rw [Eq.symm
              (Finset.sum_mul Finset.univ (fun i ↦ ∑ i_1 : m, ‖A i_1 i‖) (∑ k : n, ∑ j : l, ‖B k j‖)),
            Finset.sum_comm (f := fun i j => ‖A i j‖)]
  case neg =>
    let q := p.toReal.conjExponent
    have hpq : p.toReal.IsConjExponent q := by
      apply Real.IsConjExponent.conjExponent
      have : 1 ≤ p.toReal := by
        cases ENNReal.dichotomy p
        · contradiction
        assumption
      exact lt_of_le_of_ne this fun a ↦ hp (id (Eq.symm a))
    let q' : ℝ≥0∞ := ENNReal.ofReal q
    have prleq : p.toReal ≤ q := by
      rw [Real.IsConjExponent.conj_eq hpq]
      apply le_div_self (ENNReal.toReal_nonneg) (Real.IsConjExponent.sub_one_pos hpq)
      rw [← add_le_add_iff_right 1]
      simp only [sub_add_cancel]
      rw [one_add_one_eq_two]
      apply ENNReal.toReal_le_of_le_ofReal (by linarith)
      rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by exact ENNReal.ofReal_eq_ofNat.mpr rfl]
      exact ple2
    have hq : q' ≠ ⊤ := ENNReal.ofReal_ne_top
    have qeqqr : q = q'.toReal := by
      refine Eq.symm (ENNReal.toReal_ofReal ?h)
      exact Real.IsConjExponent.nonneg (id (Real.IsConjExponent.symm hpq))
    have pleq : p ≤ q' := by
      apply (ENNReal.le_ofReal_iff_toReal_le h ?hb).mpr prleq
      exact ENNReal.toReal_ofReal_eq_iff.mp (id (Eq.symm qeqqr))

    calc
      ∑ i : m, ∑ j : l, ‖(A * B) i j‖ ^ p.toReal ≤ ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ * ‖B k j‖) ^ p.toReal := by
        -- todo : extract
        apply Finset.sum_sum_le_sum_sum
        intro i j
        rw [Real.rpow_le_rpow_iff (norm_nonneg <| (A * B) i j)
          (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j))) ppos]
        exact (fun i j => norm_sum_le_of_le Finset.univ (fun k _ => NormedRing.norm_mul (A i k) (B k j))) i j
      _ ≤ ∑ i, ∑ j, ((∑ (k : n), ‖A i k‖ ^ p.toReal) ^ p.toReal⁻¹ * (∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal := by
        -- todo : extract
        apply Finset.sum_sum_le_sum_sum
        intro i j
        have : 0 ≤ (∑ k : n, ‖A i k‖ ^ p.toReal) ^ p.toReal⁻¹ * (∑ k : n, ‖B k j‖ ^ q) ^ q⁻¹ :=
          Left.mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (A i k)) p.toReal)) p.toReal⁻¹)
            (Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (B k j)) q)) q⁻¹)
        rw [Real.rpow_le_rpow_iff (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j)))
            this ppos]
        rw [← one_div, ← one_div]
        conv_rhs =>
          enter [1, 1, 2]
          intro k
          enter [1]
          rw [Eq.symm (abs_norm (A i k))]
        conv_rhs =>
          enter [2, 1, 2]
          intro k
          enter [1]
          rw [Eq.symm (abs_norm (B k j))]
        exact Real.inner_le_Lp_mul_Lq (f := fun k => ‖A i k‖) (g := fun k => ‖B k j‖)
          (hpq := hpq) (Finset.univ)
      _ = ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ ^ p.toReal) * ((∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal := by
        conv_lhs =>
          enter [2]
          intro i
          enter [2]
          intro j
          rw [Real.mul_rpow (Real.rpow_nonneg (Arpnn i) p.toReal⁻¹)
              (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (B i j)) q)) q⁻¹),
              ← Real.rpow_mul <| Arpnn i, inv_mul_cancel₀ <| ENNReal.ge_one_toReal_ne_zero p h, Real.rpow_one]
      _ = (∑ i, ∑ (k : n), (‖A i k‖ ^ p.toReal)) * (∑ j, ((∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal) := by
        rw [← Finset.sum_mul_sum Finset.univ Finset.univ (fun i => ∑ (k : n), (‖A i k‖ ^ p.toReal))
          (fun j => ((∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal)]
      _ ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) * ∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal := by
        by_cases h' : ∑ i : m, ∑ k : n, ‖A i k‖ ^ p.toReal = 0
        · simp only [h', zero_mul, le_refl]
        rw [mul_le_mul_left (lt_of_le_of_ne (lpnorm_rpow_nonneg p A) fun a ↦ h' (id (Eq.symm a))), Finset.sum_comm]
        apply Finset.sum_le_sum
        intro i _
        have : ((∑ k : n, ‖B k i‖ ^ q) ^ q⁻¹) ≤ ((∑ k : n, ‖B k i‖ ^ p.toReal) ^ p.toReal⁻¹) := by
          let B' : Matrix n Unit 𝕂 := Matrix.col Unit (fun k : n => B k i)
          rw [show (∑ k : n, ‖B k i‖ ^ q) ^ q⁻¹ = (∑ k : n, ‖B' k ()‖ ^ q) ^ q⁻¹ by rfl,
            show (∑ k : n, ‖B k i‖ ^ p.toReal) ^ p.toReal⁻¹ = (∑ k : n, ‖B' k ()‖ ^ p.toReal) ^ p.toReal⁻¹ by rfl]
          have : (∑ k : n, ‖B' k ()‖ ^ q) ^ q⁻¹ = (∑ k : n, ∑ j : Unit, ‖B' k j‖ ^ q) ^ q⁻¹ := by
            have : ∀ k : n, ∑ _ : Unit, ‖B' k ()‖ ^ q = ‖B' k ()‖ ^ q :=
              fun k => Fintype.sum_unique fun _ ↦ ‖B' k ()‖ ^ q
            simp_rw [this]
          rw [this]
          have : (∑ k : n, ‖B' k ()‖ ^ p.toReal) ^ p.toReal⁻¹ = (∑ k : n, ∑ j : Unit, ‖B' k j‖ ^ p.toReal) ^ p.toReal⁻¹ := by
            have : ∀ k : n, ∑ _ : Unit, ‖B' k ()‖ ^ p.toReal = ‖B' k ()‖ ^ p.toReal :=
              fun k => Fintype.sum_unique fun _ ↦ ‖B' k ()‖ ^ p.toReal
            simp_rw [this]
          rw [this, qeqqr, ← one_div, ← one_div]
          have inst : Fact (1 ≤ q') := by
            refine { out := ?out }
            refine ENNReal.one_le_ofReal.mpr ?out.a
            rw [Real.IsConjExponent.conj_eq hpq]
            rw [one_le_div_iff]
            left
            constructor
            · exact Real.IsConjExponent.sub_one_pos hpq
            · linarith
          rw [← lp_norm_def q' B' hq, lp_norm_eq_lpnorm, ← lp_norm_def p B' h, lp_norm_eq_lpnorm]
          exact lpnorm_antimono B' p q' h hq pleq
        refine (Real.le_rpow_inv_iff_of_pos ?_ ?_ ppos).mp this
        · exact Real.rpow_nonneg (Finset.sum_nonneg (fun i' _ => Real.rpow_nonneg (norm_nonneg (B i' i)) q)) q⁻¹
        exact (Finset.sum_nonneg (fun i' _ => Real.rpow_nonneg (norm_nonneg (B i' i)) p.toReal))

theorem lpnorm_mul_le_lpnorm_pq (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (pge2 : 2 ≤ p)
    (h : Real.IsConjExponent p.toReal q.toReal) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    LpNorm p (A * B) ≤ (LpNorm p A) * (LpNorm q B) := by
  rw [← Real.rpow_le_rpow_iff (z := p.toReal) (lpnorm_nonneg p (A * B))
    (mul_nonneg (lpnorm_nonneg p A) (lpnorm_nonneg q B)) ((ENNReal.toReal_pos_iff_ne_top p).mpr hp)]
  simp only [LpNorm, one_div, if_neg hp, if_neg hq]
  have lpAnn : 0 ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ p.toReal⁻¹ :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (Real.rpow_nonneg (norm_nonneg (A i j)) _)))) _
  have lpBnn : 0 ≤ (∑ i : n, ∑ j : l, ‖B i j‖ ^ q.toReal) ^ q.toReal⁻¹ :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (Real.rpow_nonneg (norm_nonneg (B i j)) _)))) _
  have Arpnn : ∀ i, 0 ≤ ∑ k : n, ‖A i k‖ ^ p.toReal :=
    fun i => Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (A i k)) p.toReal)
  rw [Real.mul_rpow lpAnn lpBnn, ← Real.rpow_mul (lpnorm_rpow_nonneg p (A * B)),
    ← Real.rpow_mul (lpnorm_rpow_nonneg p A), inv_mul_cancel₀ (ENNReal.ge_one_toReal_ne_zero p hp),
    Real.rpow_one, Real.rpow_one]
  have ppos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hp
  calc
    ∑ i : m, ∑ j : l, ‖(A * B) i j‖ ^ p.toReal ≤ ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ * ‖B k j‖) ^ p.toReal := by
      apply Finset.sum_sum_le_sum_sum
      intro i j
      rw [Real.rpow_le_rpow_iff (norm_nonneg <| (A * B) i j)
        (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j))) ppos]
      exact (fun i j => norm_sum_le_of_le Finset.univ (fun k _ => NormedRing.norm_mul (A i k) (B k j))) i j
    _ ≤ ∑ i, ∑ j, ((∑ (k : n), ‖A i k‖ ^ p.toReal) ^ p.toReal⁻¹ * (∑ k, ‖B k j‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal := by
      apply Finset.sum_sum_le_sum_sum
      intro i j
      have : 0 ≤ (∑ k : n, ‖A i k‖ ^ p.toReal) ^ p.toReal⁻¹ * (∑ k : n, ‖B k j‖ ^ q.toReal) ^ q.toReal⁻¹ :=
        Left.mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (A i k)) p.toReal)) p.toReal⁻¹)
          (Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (B k j)) q.toReal)) q.toReal⁻¹)
      rw [Real.rpow_le_rpow_iff (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j)))
          this ppos, ← one_div, ← one_div]
      conv_rhs =>
        enter [1, 1, 2]
        intro k
        enter [1]
        rw [Eq.symm (abs_norm (A i k))]
      conv_rhs =>
        enter [2, 1, 2]
        intro k
        enter [1]
        rw [Eq.symm (abs_norm (B k j))]
      exact Real.inner_le_Lp_mul_Lq (f := fun k => ‖A i k‖) (g := fun k => ‖B k j‖)
        (hpq := h) (Finset.univ)
    _ = ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ ^ p.toReal) * ((∑ k, ‖B k j‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal := by
      conv_lhs =>
        enter [2]
        intro i
        enter [2]
        intro j
        rw [Real.mul_rpow (Real.rpow_nonneg (Arpnn i) p.toReal⁻¹)
            (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (B i j)) q.toReal)) q.toReal⁻¹),
            ← Real.rpow_mul <| Arpnn i, inv_mul_cancel₀ <| ENNReal.ge_one_toReal_ne_zero p hp, Real.rpow_one]
    _ = (∑ i, ∑ (k : n), (‖A i k‖ ^ p.toReal)) * (∑ j, ((∑ k, ‖B k j‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal) := by
      rw [← Finset.sum_mul_sum Finset.univ Finset.univ (fun i => ∑ (k : n), (‖A i k‖ ^ p.toReal))
        (fun j => ((∑ k, ‖B k j‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal)]
    _ ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) * ((∑ i : n, ∑ j : l, ‖B i j‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal := by
      by_cases h' : ∑ i : m, ∑ k : n, ‖A i k‖ ^ p.toReal = 0
      · simp only [zero_mul, le_refl, h']
      have h' : 0 < ∑ i : m, ∑ k : n, ‖A i k‖ ^ p.toReal :=
        lt_of_le_of_ne (lpnorm_rpow_nonneg p A) fun a ↦ h' (id (Eq.symm a))
      rw [mul_le_mul_left h', Finset.sum_comm, ← Real.rpow_mul (lpnorm_rpow_nonneg q fun i j ↦ B j i)]
      conv_lhs =>
        enter [2]
        intro j
        rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (B i j)) q.toReal))]
      rw [← Real.rpow_le_rpow_iff (z := (q.toReal⁻¹ * p.toReal)⁻¹),
        ← Real.rpow_mul (lpnorm_rpow_nonneg q fun i j ↦ B j i), _root_.mul_inv_rev, inv_inv]
      conv_rhs =>
        enter [2]
        rw [← mul_assoc, mul_comm, mul_assoc, mul_inv_cancel₀ (ENNReal.ge_one_toReal_ne_zero p hp),
          mul_one, mul_inv_cancel₀ (ENNReal.ge_one_toReal_ne_zero q hq)]
      rw [Real.rpow_one]
      have : ∑ y : l, ∑ x : n, ‖B x y‖ ^ q.toReal = (∑ y : l, (∑ x : n, ‖B x y‖ ^ q.toReal) ^ (1 : ℝ)) ^ (1 : ℝ)⁻¹ := by
        simp only [Real.rpow_one, inv_one]
      rw [this]
      have : p.toReal⁻¹ * q.toReal = (q.toReal⁻¹ * p.toReal)⁻¹ := by
        simp only [_root_.mul_inv_rev, inv_inv]
      rw [this]
      have : 1 ≤ q.toReal⁻¹ * p.toReal := by
        have : p.toReal * (p.toReal⁻¹ + q.toReal⁻¹) = p.toReal * 1 := by
          exact congrArg (HMul.hMul p.toReal) (h.inv_add_inv_conj)
        rw [mul_add, mul_one, mul_inv_cancel₀] at this
        have : p.toReal * q.toReal⁻¹ = p.toReal - 1 := by
          linarith
        rw [mul_comm] at this
        rw [this, ← add_le_add_iff_right 1, sub_add_cancel, show (1 : ℝ) + 1 = 2 by exact one_add_one_eq_two]
        apply (ENNReal.ofReal_le_iff_le_toReal hp).mp
        rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by exact ENNReal.ofReal_eq_ofNat.mpr rfl]
        exact pge2
        exact ENNReal.ge_one_toReal_ne_zero p hp
      apply lpnorm_antimono' _ _ (Preorder.le_refl 1) this this
      intro i
      exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg (B j i)) q.toReal
      exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg (B j i)) q.toReal) _)
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg (B j i)) q.toReal)) _
      rw [@RCLike.inv_pos]
      exact mul_pos (Real.IsConjExponent.inv_pos (id (Real.IsConjExponent.symm h))) ppos

theorem lpnorm_mul_le_lpnorm_qp (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (pge2 : 2 ≤ p)
    (h : Real.IsConjExponent q.toReal p.toReal) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    LpNorm p (A * B) ≤ (LpNorm q A) * (LpNorm p B) := by
  rw [← Real.rpow_le_rpow_iff (z := p.toReal) (lpnorm_nonneg p (A * B))
    (mul_nonneg (lpnorm_nonneg q A) (lpnorm_nonneg p B)) ((ENNReal.toReal_pos_iff_ne_top p).mpr hp)]
  simp only [LpNorm, one_div, if_neg hp, if_neg hq]
  have lpAnn : 0 ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ q.toReal) ^ q.toReal⁻¹ :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (Real.rpow_nonneg (norm_nonneg (A i j)) _)))) _
  have lpBnn : 0 ≤ (∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal) ^ p.toReal⁻¹ :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (Real.rpow_nonneg (norm_nonneg (B i j)) _)))) _
  have Arpnn : ∀ i, 0 ≤ ∑ k : n, ‖A i k‖ ^ q.toReal :=
    fun i => Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (A i k)) q.toReal)
  rw [Real.mul_rpow lpAnn lpBnn, ← Real.rpow_mul (lpnorm_rpow_nonneg p (A * B)),
    ← Real.rpow_mul (lpnorm_rpow_nonneg p B), inv_mul_cancel₀ (ENNReal.ge_one_toReal_ne_zero p hp),
    Real.rpow_one, Real.rpow_one]
  have ppos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr hp
  calc
    ∑ i : m, ∑ j : l, ‖(A * B) i j‖ ^ p.toReal ≤ ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ * ‖B k j‖) ^ p.toReal := by
      apply Finset.sum_sum_le_sum_sum
      intro i j
      rw [Real.rpow_le_rpow_iff (norm_nonneg <| (A * B) i j)
        (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j))) ppos]
      exact (fun i j => norm_sum_le_of_le Finset.univ (fun k _ => NormedRing.norm_mul (A i k) (B k j))) i j
    _ ≤ ∑ i, ∑ j, ((∑ (k : n), ‖A i k‖ ^ q.toReal) ^ q.toReal⁻¹ * (∑ k, ‖B k j‖ ^ p.toReal) ^ p.toReal⁻¹) ^ p.toReal := by
      apply Finset.sum_sum_le_sum_sum
      intro i j
      have : 0 ≤ (∑ k : n, ‖A i k‖ ^ q.toReal) ^ q.toReal⁻¹ * (∑ k : n, ‖B k j‖ ^ p.toReal) ^ p.toReal⁻¹ :=
        Left.mul_nonneg (Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (A i k)) q.toReal)) q.toReal⁻¹)
          (Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (B k j)) p.toReal)) p.toReal⁻¹)
      rw [Real.rpow_le_rpow_iff (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j)))
          this ppos, ← one_div, ← one_div]
      conv_rhs =>
        enter [1, 1, 2]
        intro k
        enter [1]
        rw [Eq.symm (abs_norm (A i k))]
      conv_rhs =>
        enter [2, 1, 2]
        intro k
        enter [1]
        rw [Eq.symm (abs_norm (B k j))]
      exact Real.inner_le_Lp_mul_Lq (f := fun k => ‖A i k‖) (g := fun k => ‖B k j‖)
        (hpq := h) (Finset.univ)
    _ = ∑ i, ∑ j, (((∑ (k : n), ‖A i k‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal * ((∑ k, ‖B k j‖ ^ p.toReal))) := by
      conv_lhs =>
        enter [2]
        intro i
        enter [2]
        intro j
        rw [Real.mul_rpow (Real.rpow_nonneg (Arpnn i) q.toReal⁻¹)
            (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (B i j)) p.toReal)) p.toReal⁻¹)]
        enter [2]
        rw[← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (B i j)) _)),
          inv_mul_cancel₀ <| ENNReal.ge_one_toReal_ne_zero p hp, Real.rpow_one]
    _ = (∑ i, (((∑ (k : n), ‖A i k‖ ^ q.toReal)) ^ q.toReal⁻¹) ^ p.toReal) * (∑ j, ((∑ k, ‖B k j‖ ^ p.toReal))) := by
      rw [← Finset.sum_mul_sum Finset.univ Finset.univ (fun i => ((∑ k : n, ‖A i k‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal)
        (fun j => (∑ k, ‖B k j‖ ^ p.toReal))]
    _ ≤ ((∑ i : m, ∑ j : n, ‖A i j‖ ^ q.toReal) ^ q.toReal⁻¹) ^ p.toReal * (∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal) := by
      nth_rw 1 [Finset.sum_comm]
      by_cases h' : ∑ i : n, ∑ k : l, ‖B i k‖ ^ p.toReal = 0
      · simp only [h', mul_zero, le_refl]
      have h' : 0 < ∑ i : n, ∑ k : l, ‖B i k‖ ^ p.toReal :=
        lt_of_le_of_ne (lpnorm_rpow_nonneg p B) fun a ↦ h' (id (Eq.symm a))
      rw [mul_le_mul_right h', ← Real.rpow_mul]
      conv_lhs =>
        enter [2]
        intro j
        rw [← Real.rpow_mul (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (A j i)) q.toReal))]
      rw [← Real.rpow_le_rpow_iff (z := (q.toReal⁻¹ * p.toReal)⁻¹),
        ← Real.rpow_mul, _root_.mul_inv_rev, inv_inv]
      conv_rhs =>
        enter [2]
        rw [← mul_assoc, mul_comm, mul_assoc, mul_inv_cancel₀ (ENNReal.ge_one_toReal_ne_zero p hp),
          mul_one, mul_inv_cancel₀ (ENNReal.ge_one_toReal_ne_zero q hq)]
      rw [Real.rpow_one]
      have : ∑ i : m, ∑ j : n, ‖A i j‖ ^ q.toReal = (∑ i : m, (∑ j : n, ‖A i j‖ ^ q.toReal) ^ (1 : ℝ)) ^ (1 : ℝ)⁻¹ := by
        simp only [Real.rpow_one, inv_one]
      rw [this]
      have : p.toReal⁻¹ * q.toReal = (q.toReal⁻¹ * p.toReal)⁻¹ := by
        simp only [_root_.mul_inv_rev, inv_inv]
      rw [this]
      have : 1 ≤ q.toReal⁻¹ * p.toReal := by
        have : p.toReal * (p.toReal⁻¹ + q.toReal⁻¹) = p.toReal * 1 := by
          apply congrArg (HMul.hMul p.toReal)
          exact (id (Real.IsConjExponent.symm h)).inv_add_inv_conj
        rw [mul_add, mul_one, mul_inv_cancel₀] at this
        have : p.toReal * q.toReal⁻¹ = p.toReal - 1 := by
          linarith
        rw [mul_comm] at this
        rw [this, ← add_le_add_iff_right 1, sub_add_cancel, show (1 : ℝ) + 1 = 2 by exact one_add_one_eq_two]
        apply (ENNReal.ofReal_le_iff_le_toReal hp).mp
        rw [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by exact ENNReal.ofReal_eq_ofNat.mpr rfl]
        exact pge2
        exact ENNReal.ge_one_toReal_ne_zero p hp
      apply lpnorm_antimono' _ _ (Preorder.le_refl 1) this this
      intro i
      exact Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg (A i j)) q.toReal
      exact lpnorm_rpow_nonneg q A
      exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (norm_nonneg (A i j)) q.toReal) _)
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg (A i j)) q.toReal)) _
      rw [@RCLike.inv_pos]
      exact mul_pos (Real.IsConjExponent.inv_pos (id h)) ppos
      exact lpnorm_rpow_nonneg q A

theorem lpnorm_hoelder (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] (h : Real.IsConjExponent q.toReal p.toReal)
    (M : Matrix Unit m 𝕂) (N : Matrix m Unit 𝕂) (hp : p ≠ ⊤) (hq : q ≠ ⊤) :
    LpNorm 1 (M * N) ≤ LpNorm p M * LpNorm q N := by
  simp only [LpNorm, ENNReal.one_ne_top, ↓reduceIte, Finset.univ_unique, PUnit.default_eq_unit,
    ENNReal.one_toReal, Real.rpow_one, Finset.sum_singleton, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, ciSup_unique, one_div, if_neg hp, if_neg hq]
  calc
    ‖(M * N) PUnit.unit PUnit.unit‖ ≤ ∑ (k : m), ‖M () k‖ * ‖N k ()‖ := by
      exact (fun i j => norm_sum_le_of_le Finset.univ (fun k _ => NormedRing.norm_mul (M i k) (N k j))) () ()
    _ ≤ (∑ (k : m), ‖M () k‖ ^ p.toReal) ^ p.toReal⁻¹ * (∑ k, ‖N k ()‖ ^ q.toReal) ^ q.toReal⁻¹ := by
      conv_rhs =>
        enter [1, 1, 2]
        intro k
        enter [1]
        rw [Eq.symm (abs_norm (M () k))]
      conv_rhs =>
        enter [2, 1, 2]
        intro k
        enter [1]
        rw [Eq.symm (abs_norm (N k ()))]
      rw [← one_div, ← one_div]
      exact Real.inner_le_Lp_mul_Lq (f := fun k => ‖M () k‖) (g := fun k => ‖N k ()‖)
        (hpq := id (Real.IsConjExponent.symm h)) (Finset.univ)
    _ ≤ (∑ j : m, ‖M PUnit.unit j‖ ^ p.toReal) ^ p.toReal⁻¹ *
        (∑ x : m, ‖N x PUnit.unit‖ ^ q.toReal) ^ q.toReal⁻¹ := by
      simp only [le_refl]

theorem lpnorm_cauchy (M : Matrix Unit m 𝕂) (N : Matrix m Unit 𝕂) :
    ‖Matrix.trace (M * N)‖ ≤ LpNorm 2 M * LpNorm 2 N := by
  have : ‖Matrix.trace (M * N)‖ = LpNorm 1 (M * N) := by
    simp only [trace, Finset.univ_unique, PUnit.default_eq_unit, diag_apply, Finset.sum_singleton,
      LpNorm, ENNReal.one_ne_top, ↓reduceIte, ENNReal.one_toReal, Real.rpow_one, ne_eq, one_ne_zero,
      not_false_eq_true, div_self]
  rw [this]
  let p := ENNReal.ofReal 2
  let q := ENNReal.ofReal 2
  have : Fact (1 ≤ p) := by
    refine { out := ?out }
    refine ENNReal.one_le_ofReal.mpr (by norm_num)
  have : Fact (1 ≤ q) := by
    refine { out := ?out }
  have : (2 : ℝ≥0∞) = p := by
    exact Eq.symm ((fun {r} {n} ↦ ENNReal.ofReal_eq_ofNat.mpr) rfl)
  nth_rw 1 [this]
  have : (2 : ℝ≥0∞) = q := by
    exact Eq.symm ((fun {r} {n} ↦ ENNReal.ofReal_eq_ofNat.mpr) rfl)
  nth_rw 1 [this]
  have hpq : (ENNReal.ofReal 2).toReal.IsConjExponent (ENNReal.ofReal 2).toReal := by
    simp only [ENNReal.ofReal_ofNat, ENNReal.toReal_ofNat]
    exact (Real.isConjExponent_iff 2 2).mpr ⟨one_lt_two, by norm_num⟩
  apply lpnorm_hoelder (ENNReal.ofReal 2) (ENNReal.ofReal 2) hpq M N
    (ENNReal.ofReal_ne_top) (ENNReal.ofReal_ne_top)

@[simp]
theorem trace_eq_l2norm (M : Matrix m n 𝕂) : trace (Mᴴ * M) = RCLike.ofReal ((LpNorm 2 M) ^ (2 : ℝ)) := by
  simp only [LpNorm, if_neg (show (2 : ℝ≥0∞) ≠ ⊤ by exact ENNReal.two_ne_top)]
  have : (1 / ENNReal.toReal 2 * 2) = 1 := by
    simp only [ENNReal.toReal_ofNat, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      inv_mul_cancel₀]
  rw [← Real.rpow_mul, this, Real.rpow_one]
  have : (Mᴴ * M).trace = ∑ (i : n), (Mᴴ * M) i i := by
    simp only [trace]
    congr
  rw [this, Finset.sum_comm]
  have : RCLike.ofReal (∑ y : n, ∑ x : m, ‖M x y‖ ^ ENNReal.toReal 2) =
      (∑ y : n, ∑ x : m, RCLike.ofReal (K:=𝕂) (‖M x y‖ ^ ENNReal.toReal 2)) := by
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, map_sum, map_pow]
  simp_rw [this, Matrix.mul_apply]
  congr
  ext i
  congr
  ext j
  simp only [conjTranspose_apply, RCLike.star_def, ENNReal.toReal_ofNat, Real.rpow_two, map_pow]
  exact RCLike.conj_mul (M j i)
  exact lpnorm_rpow_nonneg 2 M

@[simp]
theorem trace_eq_l2norm' (M : Matrix m n 𝕂) :
    trace (M * Mᴴ) = RCLike.ofReal ((LpNorm 2 M) ^ (2 : ℝ)) := by
  rw [← trace_eq_l2norm, Matrix.trace_mul_comm]


@[simp]
theorem left_unitary_l2norm_preserve [PartialOrder 𝕂] [StarOrderedRing 𝕂] [DecidableEq m]
    (U : Matrix m m 𝕂) (h : IsUnitary U) (N : Matrix m n 𝕂) :
    LpNorm 2 (U * N) = LpNorm 2 N := by
  have : (LpNorm 2 (U * N)) ^ (2 : ℝ) = (LpNorm 2 N) ^ (2 : ℝ) := by
    have : RCLike.ofReal (K:=𝕂) ((LpNorm 2 (U * N)) ^ (2 : ℝ)) = RCLike.ofReal ((LpNorm 2 N) ^ (2 : ℝ)) := by
      rw [← trace_eq_l2norm, ← trace_eq_l2norm]
      have : (U * N)ᴴ * (U * N) = Nᴴ * N := by
        rw [@conjTranspose_mul, @Matrix.mul_assoc]
        have : Uᴴ * (U * N) = Uᴴ * U * N := by rw [@Matrix.mul_assoc]
        rw [this, ((IsUnitary.ext_iff' U).mp h).left]
        simp only [conjTranspose_eq_transpose_of_trivial, Matrix.one_mul]
      rw [this]
    exact RCLike.ofReal_inj.mp this
  exact (Real.rpow_left_inj (lpnorm_nonneg 2 (U * N)) (lpnorm_nonneg 2 N)
    (Ne.symm (NeZero.ne' 2))).mp this

@[simp]
theorem right_unitary_l2norm_preserve [PartialOrder 𝕂] [StarOrderedRing 𝕂] [DecidableEq n]
    (U : Matrix n n 𝕂) (h : IsUnitary U) (N : Matrix m n 𝕂) :
    LpNorm 2 (N * U) = LpNorm 2 N := by
  have : (LpNorm 2 (N * U)) ^ (2 : ℝ) = (LpNorm 2 N) ^ (2 : ℝ) := by
    have : RCLike.ofReal (K:=𝕂) ((LpNorm 2 (N * U)) ^ (2 : ℝ)) = RCLike.ofReal ((LpNorm 2 N) ^ (2 : ℝ)) := by
      rw [← trace_eq_l2norm', ← trace_eq_l2norm', Matrix.trace_mul_comm]
      have : N * U * (N * U)ᴴ = N * Nᴴ := by
        rw [@conjTranspose_mul, @Matrix.mul_assoc]
        have : U * (Uᴴ * Nᴴ) = U * Uᴴ * Nᴴ := by rw [@Matrix.mul_assoc]
        rw [this, ((IsUnitary.ext_iff' U).mp h).right]
        simp only [conjTranspose_eq_transpose_of_trivial, Matrix.one_mul]
      rw [Matrix.trace_mul_comm, this]
    exact RCLike.ofReal_inj.mp this
  exact (Real.rpow_left_inj (lpnorm_nonneg 2 (N * U)) (lpnorm_nonneg 2 N)
    (Ne.symm (NeZero.ne' 2))).mp this

@[simp]
theorem l2norm_unitary [DecidableEq m] (U : Matrix m m 𝕂) (h : IsUnitary U) :
    LpNorm 2 U = (Fintype.card m) ^ (1 / 2 : ℝ) := by
  simp only [LpNorm, ENNReal.two_ne_top, ↓reduceIte, ENNReal.toReal_ofNat, Real.rpow_two]
  have : ∀ i, (∑ j, ‖U i j‖ ^ 2) = 1 := by
    intro i
    sorry
  conv_lhs =>
    enter [1, 2]
    intro i
    rw [this i]
  have : ∑ i : m, (1 : ℝ) = Fintype.card m := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [this]

theorem lpnorm_unit_default_eq1 [Inhabited n] [DecidableEq n] (v : Matrix n Unit 𝕂) :
    v = (fun i _ => if i = default then 1 else 0) → LpNorm p v = 1 := by
  intro hv
  by_cases h : p = ⊤
  · simp only [LpNorm, ciSup_unique, PUnit.default_eq_unit, Finset.univ_unique,
    Finset.sum_singleton, one_div, if_pos h]
    apply le_antisymm
    · apply ciSup_le
      intro x
      by_cases g : x = default
      · simp only [hv, if_pos g, norm_one, le_refl]
      simp only [hv, if_neg g, norm_zero, zero_le_one]
    rw [show 1 = ‖v default ()‖ by simp only [hv, ↓reduceIte, norm_one]]
    apply le_ciSup (f := fun i => ‖v i PUnit.unit‖)
    exact Finite.bddAbove_range fun i ↦ ‖v i PUnit.unit‖
  simp only [LpNorm, ciSup_unique, PUnit.default_eq_unit, Finset.univ_unique, Finset.sum_singleton,
    one_div, if_neg h]
  have : (∑ x : n, ‖if x = default then (1 : 𝕂) else 0‖ ^ p.toReal) = 1 := by
    rw [Finset.sum_eq_single_of_mem default, if_pos, norm_one, Real.one_rpow]
    rfl
    exact Finset.mem_univ default
    intro x _ hx
    rw [if_neg hx, norm_zero, Real.zero_rpow]
    exact ENNReal.ge_one_toReal_ne_zero p h
  rw [hv, this, Real.one_rpow]



theorem unit_nonempty [Inhabited n] [DecidableEq n]:
    Set.Nonempty {(v : Matrix n Unit 𝕂) | LpNorm p v = 1} := by
  let v : Matrix n Unit 𝕂 := fun i _ => if i = default then 1 else 0
  use v
  apply lpnorm_unit_default_eq1
  rfl

theorem unit_bdd  :
    Bornology.IsBounded {(v : Matrix m n 𝕂) | LpNorm p v = 1} := by
  apply isBounded_iff_forall_norm_le.mpr
  use 1
  intro v vin
  have : {v | LpNorm p v = 1} = {(v : Matrix m n 𝕂) | ‖v‖ = 1} := by
    ext v
    constructor <;> intro vin
    have : ‖v‖ = 1 := by
      rw [@lp_norm_eq_lpnorm]
      exact vin
    exact this
    have : LpNorm p v = 1 := by
      rw [← lp_norm_eq_lpnorm]
      exact vin
    exact this
  rw [this] at vin
  exact le_of_eq vin

theorem unit_closed  :
    IsClosed {(v : Matrix m n 𝕂) | LpNorm p v = 1} := by
  let f := fun (v : Matrix m n 𝕂) => LpNorm p v
  have hf : Continuous f := lpnorm_continuous_at_m p
  let t : Set ℝ := {1}
  have ht : IsClosed t := isClosed_singleton
  exact IsClosed.preimage hf ht

theorem unit_compact  :
    IsCompact {(v : Matrix m n 𝕂) | LpNorm p v = 1} := by
  have : ProperSpace (Matrix m n 𝕂) := sorry
    -- apply?
  exact Metric.isCompact_of_isClosed_isBounded (unit_closed p) (unit_bdd p)

theorem div_norm_self_norm_unit (hM : M ≠ 0) : LpNorm p ((1 / LpNorm p M) • M) = 1 := by
  rw [← lp_norm_eq_lpnorm, ← lp_norm_eq_lpnorm]
  simp only [one_div]
  have : ‖‖M‖⁻¹ • M‖ = ‖M‖⁻¹ * ‖M‖ := by
    apply norm_smul_of_nonneg ?ht M
    simp_all only [ne_eq, inv_nonneg, norm_nonneg]
  rw [this, inv_mul_cancel₀]
  simp_all only [ne_eq, norm_eq_zero, not_false_eq_true, inv_mul_cancel₀]


theorem lpnorm_smul [NormedDivisionRing R] [MulActionWithZero R 𝕂] [BoundedSMul R 𝕂](r : R) : LpNorm p (r • M) = ‖r‖ * (LpNorm p M) := by
  simp only [LpNorm, one_div, mul_ite]
  by_cases h : p = ⊤
  · simp only [smul_apply, if_pos h]
    have : ‖r‖ * ⨆ i, ⨆ j, ‖M i j‖ = ⨆ i, ⨆ j, ‖r‖ * ‖M i j‖ := by
      rw [Real.mul_iSup_of_nonneg (norm_nonneg r)]
      conv_lhs =>
        enter [1]
        intro i
        rw [Real.mul_iSup_of_nonneg (norm_nonneg r)]
    rw [this]
    congr
    ext i
    congr
    ext j
    exact norm_smul r (M i j)
  simp only [smul_apply, if_neg h]
  have : ‖r‖ = (‖r‖ ^ p.toReal) ^ p.toReal⁻¹ := by
    refine Eq.symm (Real.rpow_rpow_inv ?hx ?hy)
    exact norm_nonneg r
    exact ENNReal.ge_one_toReal_ne_zero p h
  rw [this, ← Real.mul_rpow]
  congr
  rw [@Finset.mul_sum]
  conv_rhs =>
    enter [2]
    intro i
    rw [@Finset.mul_sum]
  congr
  ext i
  congr
  ext j
  rw [← Real.mul_rpow]
  congr
  exact norm_smul r (M i j)
  exact norm_nonneg r
  exact norm_nonneg (M i j)
  refine Real.rpow_nonneg (norm_nonneg r) p.toReal
  exact lpnorm_rpow_nonneg p M


end LpNorm


section InducedNorm

open scoped NNReal ENNReal Finset Matrix

variable (p q r : ℝ≥0∞)
variable [RCLike 𝕂] [Fintype m] [Fintype n] [Fintype l]
variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]

@[simp]
def IpqNorm (p q : ℝ≥0∞) (M : Matrix m n 𝕂) : ℝ :=
  sSup ((fun v => LpNorm q (M * v)) '' {(v : Matrix n Unit 𝕂) | LpNorm p v = 1})
  -- sSup {x | ∃ (v : Matrix n Unit 𝕂), LpNorm p v = 1 ∧ LpNorm q (M * v) = x}

-- local notation "‖" M "‖ₚq" => IpqNorm p q M

variable (M N : Matrix m n 𝕂)
variable (A : Matrix m n 𝕂) (B : Matrix n l 𝕂)

theorem range_on_unit_eq_range_div : ((fun v ↦ LpNorm q (M * v)) '' {(v : Matrix n Unit 𝕂) | LpNorm p v = 1}) ∪ {0} =
    Set.range fun (v : Matrix n Unit 𝕂) => LpNorm q (M * v) / LpNorm p v := by
  ext x
  constructor <;> intro xin
  · rw [Set.mem_union] at xin
    rcases xin with h₁ | h₂
    · rw [@Set.mem_image] at h₁
      rcases h₁ with ⟨v, hv, heq⟩
      use v
      subst heq
      simp_all only [LpNorm, ciSup_unique, PUnit.default_eq_unit, Finset.univ_unique, Finset.sum_singleton, one_div,
        mul_ite, ↓reduceIte, Set.mem_setOf_eq, div_one, mul_one]
    · rw [h₂, @Set.mem_range]
      use 0
      rw [((lpnorm_eq0_iff p 0).mpr rfl), div_zero]
  · rw [@Set.mem_range] at xin
    rcases xin with ⟨v, heq⟩
    by_cases hv : v = 0
    · rw [hv, ((lpnorm_eq0_iff p 0).mpr rfl), div_zero] at heq
      exact
        Set.mem_union_right
          ((fun v ↦ LpNorm q (M * v)) '' {v | LpNorm p v = 1})
          (id (Eq.symm heq))
    rw [@Set.mem_union]
    left
    use ((1 / (LpNorm p v)) • v)
    constructor
    · exact div_norm_self_norm_unit p v hv
    · dsimp only
      rw [← heq]
      have : LpNorm q (M * (1 / LpNorm p v) • v) = (1 / LpNorm p v) * LpNorm q (M * v) := by
        rw [@mul_smul, @lpnorm_smul]
        have : ‖1 / LpNorm p v‖ = 1 / LpNorm p v :=
          Real.norm_of_nonneg (one_div_nonneg.mpr (lpnorm_nonneg p v))
        rw [this]
      rw [this, mul_comm, div_eq_mul_one_div (LpNorm q (M * v)) (LpNorm p v)]

theorem range_on_unit_eq_range_div' : ((fun v ↦ LpNorm q (M * v) / LpNorm p v * LpNorm p v) ''
    {(v : Matrix n Unit 𝕂) | LpNorm p v = 1}) ∪ {0} =
    Set.range fun (v : Matrix n Unit 𝕂) => LpNorm q (M * v) / LpNorm p v := by
  have : ∀ (v : Matrix n Unit 𝕂), LpNorm q (M * v) / LpNorm p v * LpNorm p v = LpNorm q (M * v) := by
    intro v
    by_cases h : LpNorm p v = 0
    · rw [h, div_zero, mul_zero, ((lpnorm_eq0_iff p v).mp h), Matrix.mul_zero]
      exact id (Eq.symm ((lpnorm_eq0_iff q 0).mpr rfl))
    rw [div_mul, div_self h, div_one]
  simp_rw [this]
  exact range_on_unit_eq_range_div p q M

theorem sup_on_unit_eq_sup_div [DecidableEq n] [Inhabited n] : sSup ((fun v => LpNorm q (M * v)) '' {(v : Matrix n Unit 𝕂) | LpNorm p v = 1}) =
    ⨆ (v : Matrix n Unit 𝕂), (LpNorm q (M * v)) / (LpNorm p v) := by
  have : (fun (v : Matrix n Unit 𝕂) => LpNorm q (M * v)) =
      fun (v : Matrix n Unit 𝕂) => ((LpNorm q (M * v)) / (LpNorm p v)) * (LpNorm p v) := by
    ext v
    by_cases hv : v = 0
    · have : LpNorm p v = 0 := by
        exact (lpnorm_eq0_iff p v).mpr hv
      rw [this, mul_zero]
      have : M * v = 0 := by
        subst hv
        simp only [Matrix.mul_zero]
      rw [this]
      exact (lpnorm_eq0_iff q 0).mpr rfl
    rw [div_mul, div_self, div_one]
    intro hn
    have : v = 0 := by
      rw [@lpnorm_eq0_iff] at hn
      exact hn
    contradiction
  rw [this]
  have : ⨆ (v : Matrix n Unit 𝕂), (LpNorm q (M * v)) / (LpNorm p v) =
      sSup (Set.range (fun (v : Matrix n Unit 𝕂) => LpNorm q (M * v) / LpNorm p v)) := by
    rw [@sSup_range]
  rw [this]
  have : sSup ((fun (v : Matrix n Unit 𝕂) ↦ LpNorm q (M * v) / LpNorm p v * LpNorm p v) '' {v | LpNorm p v = 1}) =
      sSup (((fun (v : Matrix n Unit 𝕂) ↦ LpNorm q (M * v) / LpNorm p v * LpNorm p v) '' {v | LpNorm p v = 1}) ∪ {0}) := by
    apply csSup_eq_csSup_of_forall_exists_le
    · intro x xin
      use x
      constructor
      · rw [@Set.mem_union]
        left
        exact xin
      · exact Preorder.le_refl x
    · intro x xin
      rw [@Set.mem_union] at xin
      rcases xin with h₁ | h₂
      · use x
      · rw [h₂]
        have : ∀ x ∈ (fun v ↦ (LpNorm q (M * v)) / (LpNorm p v) * (LpNorm p v)) '' {(v : Matrix n Unit 𝕂) | LpNorm p v = 1}, 0 ≤ x := by
          intro y yin
          rw [@Set.mem_image] at yin
          rcases yin with ⟨z, _, hz⟩
          rw [← hz]
          exact mul_nonneg (div_nonneg (lpnorm_nonneg q (M * z)) (lpnorm_nonneg p z)) (lpnorm_nonneg p z)
        let v : Matrix n Unit 𝕂 := fun i _ => if i = default then 1 else 0
        use (LpNorm q (M * v))
        constructor
        · simp only [Set.mem_image, Set.mem_setOf_eq]
          use v
          have hv : LpNorm p v = 1 := lpnorm_unit_default_eq1 p v rfl
          constructor
          · assumption
          · rw [div_mul, div_self, div_one]
            exact ne_zero_of_eq_one hv
        · exact lpnorm_nonneg q (M * v)
  rw [this, range_on_unit_eq_range_div']

theorem ipqnorm_def [DecidableEq n] [Inhabited n] :
    IpqNorm p q M = ⨆ (v : Matrix n Unit 𝕂), (LpNorm q (M * v)) / (LpNorm p v) := by
  simp only [IpqNorm]
  exact sup_on_unit_eq_sup_div p q M

omit [Fact (1 ≤ p)] in
theorem ipqnorm_nonneg : 0 ≤ IpqNorm p q M := by
  simp only [IpqNorm]
  refine Real.sSup_nonneg ?_
  intro x xin
  have : ∀ (v : Matrix n Unit 𝕂), 0 ≤ (fun v ↦ LpNorm q (M * v)) v :=
    fun v => lpnorm_nonneg q (M * v)
  simp_all only [LpNorm, ciSup_unique, PUnit.default_eq_unit, Finset.univ_unique,
    Finset.sum_singleton, one_div,Set.mem_image, Set.mem_setOf_eq, ge_iff_le]
  obtain ⟨w, h⟩ := xin
  obtain ⟨_, right⟩ := h
  subst right
  simp_all only

theorem ipqnorm_bddabove :
    BddAbove ((fun v => LpNorm q (M * v)) '' {(v : Matrix n Unit 𝕂) | LpNorm p v = 1}) := by
  have hf : ContinuousOn (fun (v : Matrix n Unit 𝕂) => LpNorm q (M * v))
      {(v : Matrix n Unit 𝕂) | LpNorm p v = 1} := by
    have := lpnorm_continuous_at_m q (m:=n) (n:=Unit) (𝕂:=𝕂)
    apply Continuous.comp_continuousOn'
    exact lpnorm_continuous_at_m q
    have : Continuous fun (v : Matrix n Unit 𝕂) => M * v := by
      apply Continuous.matrix_mul
      exact continuous_const
      exact continuous_id'
    exact Continuous.continuousOn this
  apply IsCompact.bddAbove_image (unit_compact p) hf

theorem ipqnorm_bddabove' :
    BddAbove (Set.range fun (v : Matrix n Unit 𝕂) ↦ LpNorm q (M * v) / LpNorm p v) := by
  rw [← range_on_unit_eq_range_div]
  apply BddAbove.union
  exact ipqnorm_bddabove p q M
  exact bddAbove_singleton

theorem lqnorm_le_ipq_lp [DecidableEq n] [Inhabited n] (v : Matrix n Unit 𝕂) :
    LpNorm q (M * v) ≤ (IpqNorm p q M) * (LpNorm p v) := by
  simp only [ipqnorm_def]
  have : LpNorm q (M * v) / LpNorm p v ≤
      (⨆ (v : Matrix n Unit 𝕂), LpNorm q (M * v) / LpNorm p v) := by
    apply le_ciSup (f:=fun (v : Matrix n Unit 𝕂) => LpNorm q (M * v) / LpNorm p v)
    exact ipqnorm_bddabove' p q M
  by_cases h : LpNorm p v = 0
  · rw [h, (lpnorm_eq0_iff p v).mp h, mul_zero, Matrix.mul_zero,
      (lpnorm_eq0_iff q 0).mpr rfl]
  rw [← div_le_iff₀ (lt_of_le_of_ne (lpnorm_nonneg p v) fun a ↦ h (id (Eq.symm a)))]
  exact this

theorem lpnorm_le_ipp_lp [DecidableEq n] [Inhabited n] (v : Matrix n Unit 𝕂) :
    LpNorm p (M * v) ≤ (IpqNorm p p M) * (LpNorm p v) := by
  exact lqnorm_le_ipq_lp p p M v

theorem lpnorm_le_ipq_lp [DecidableEq n] [Inhabited n] (v : Matrix n Unit 𝕂) :
    LpNorm p (M * v) ≤ (IpqNorm p p M) * (LpNorm p v) :=
  lqnorm_le_ipq_lp p p M v

theorem lqnorm_div_lp_le_ipq [DecidableEq n] [Inhabited n] (v : Matrix n Unit 𝕂) :
    LpNorm q (M * v) / (LpNorm p v) ≤ IpqNorm p q M := by
  by_cases h : LpNorm p v = 0
  · rw [h, div_zero]
    exact ipqnorm_nonneg p q M
  rw [div_le_iff₀ (lt_of_le_of_ne (lpnorm_nonneg p v) fun a ↦ h (id (Eq.symm a)))]
  exact lqnorm_le_ipq_lp p q M v

theorem lpnorm_div_lp_le_ipq [DecidableEq n] [Inhabited n] (v : Matrix n Unit 𝕂) :
    LpNorm q (M * v) / (LpNorm p v) ≤ IpqNorm p q M :=
  lqnorm_div_lp_le_ipq p q M v

theorem ipqnorm_exists [Inhabited n] [DecidableEq n]:
    ∃ v ∈ {(v : Matrix n Unit 𝕂) | LpNorm p v = 1}, IpqNorm p q M = LpNorm q (M * v) := by
  rw [IpqNorm]
  apply IsCompact.exists_sSup_image_eq (unit_compact p)
  · exact unit_nonempty p
  · refine Continuous.comp_continuousOn' ?_ ?_
    exact lpnorm_continuous_at_m q
    refine continuousOn_of_forall_continuousAt ?_
    intro v _
    refine Continuous.continuousAt ?_
    refine continuous_matrix ?_
    intro i j
    refine Continuous.matrix_dotProduct ?_ ?_
    exact continuous_const
    refine continuous_pi ?_
    intro i
    refine Continuous.matrix_elem ?_ i j
    exact continuous_id'

theorem ipq_triangle [DecidableEq n] [Inhabited n] : IpqNorm p q (M + N) ≤ IpqNorm p q M + IpqNorm p q N := by
  have lp_triangle : ∀ (v : Matrix n Unit 𝕂),
      LpNorm q ((M + N) * v) ≤ LpNorm q (M * v) + LpNorm q (N * v) := by
    intro v
    rw [Matrix.add_mul]
    exact lpnorm_triangle q (M * v) (N * v)
  have lp_add_le_ipq_add : ∀ (v : Matrix n Unit 𝕂),
      LpNorm q (M * v) + LpNorm q (N * v) ≤
        (IpqNorm p q M) * (LpNorm p v) + (IpqNorm p q N) * (LpNorm p v) := by
    intro v
    exact add_le_add (lqnorm_le_ipq_lp p q M v) (lqnorm_le_ipq_lp p q N v)
  have lp_le_ipq  : ∀ (v : Matrix n Unit 𝕂),
      LpNorm q ((M + N) * v) ≤
        (IpqNorm p q M) * (LpNorm p v) + (IpqNorm p q N) * (LpNorm p v) := by
    intro v
    apply le_trans (lp_triangle v) (lp_add_le_ipq_add v)
  have : ∀ (v : Matrix n Unit 𝕂),
      (LpNorm q ((M + N) * v)) / (LpNorm p v) ≤ IpqNorm p q M + IpqNorm p q N := by
    intro v
    have := lp_le_ipq v
    rw [← add_mul] at this
    by_cases h : LpNorm p v = 0
    · rw [h, div_zero]
      apply add_nonneg (ipqnorm_nonneg p q M) (ipqnorm_nonneg p q N)
    rw [div_le_iff₀ (lt_of_le_of_ne (lpnorm_nonneg p v) fun a ↦ h (id (Eq.symm a)))]
    exact this
  rw [ipqnorm_def]
  exact ciSup_le this

theorem ipqnorm_eq0_iff [DecidableEq n] [Inhabited n] : IpqNorm p q M = 0 ↔ M = 0 := by
  constructor
  · intro h
    sorry
  · intro h
    simp only [ipqnorm_def]
    have : ∀ (v : Matrix n Unit 𝕂), LpNorm q (M * v) / LpNorm p v = 0 := by
      intro v
      simp_rw [h, Matrix.zero_mul, (lpnorm_eq0_iff q 0).mpr, zero_div]
    simp_rw [this, ciSup_const]

theorem ipqnorm_smul [DecidableEq n] [Inhabited n] (r : 𝕂) [SMul R (Matrix m n 𝕂)] [SMul R (Matrix m Unit 𝕂)] [Norm R] :
    IpqNorm p q (r • M) = ‖r‖ * IpqNorm p q M := by
  simp only [ipqnorm_def]
  conv_lhs =>
    enter [1]
    intro v
    rw [Matrix.smul_mul r M v, lpnorm_smul q (M * v) r, ← mul_div]
  exact Eq.symm (Real.mul_iSup_of_nonneg (norm_nonneg r) fun i ↦ LpNorm q (M * i) / LpNorm p i)

theorem ipq_mul_le_ipr_mul_irq [DecidableEq l] [Inhabited l] [DecidableEq n] [Inhabited n] (M : Matrix m n 𝕂) (N : Matrix n l 𝕂) :
    IpqNorm p q (M * N) ≤ (IpqNorm p r N) * (IpqNorm r q M) := by
  have le1 : ∀ (v : Matrix l Unit 𝕂), LpNorm q (M * (N * v)) ≤
      (IpqNorm r q M) * (LpNorm r (N * v)) := by
    intro v
    apply lqnorm_le_ipq_lp
  have le2 : ∀ (v : Matrix l Unit 𝕂), LpNorm r (N * v) ≤
      (IpqNorm p r N) * (LpNorm p v) := by
    intro v
    apply lqnorm_le_ipq_lp
  have le3 : ∀ (v : Matrix l Unit 𝕂), LpNorm q (M * (N * v)) ≤
      (IpqNorm r q M) * (IpqNorm p r N) * (LpNorm p v) := by
    intro v
    have h₁ := le1 v
    have h₂ := le2 v
    rw [mul_assoc]
    apply le_mul_of_le_mul_of_nonneg_left h₁ h₂
    exact ipqnorm_nonneg r q M
  have le4 : ∀ (v : Matrix l Unit 𝕂), LpNorm q (M * (N * v)) / (LpNorm p v) ≤
      (IpqNorm r q M) * (IpqNorm p r N) := by
    intro v
    by_cases h : LpNorm p v = 0
    · rw [h, div_zero]
      apply mul_nonneg_iff.mpr
      left
      constructor
      · exact ipqnorm_nonneg r q M
      · exact ipqnorm_nonneg p r N
    have : 0 < LpNorm p v :=
      lt_of_le_of_ne (lpnorm_nonneg p v) fun a ↦ h (id (Eq.symm a))
    exact (div_le_iff₀ this).mpr (le3 v)
  have le5 : ⨆ (v : Matrix l Unit 𝕂), LpNorm q (M * (N * v)) / (LpNorm p v) ≤
      ⨆ (_ : Matrix l Unit 𝕂), (IpqNorm r q M) * (IpqNorm p r N) := by
    refine Real.iSup_le ?hS ?ha
    · intro v
      rw [ciSup_const]
      exact le4 v
    · rw [ciSup_const]
      apply mul_nonneg_iff.mpr
      left
      constructor
      · exact ipqnorm_nonneg r q M
      · exact ipqnorm_nonneg p r N
  simp_rw [← Matrix.mul_assoc] at le5
  rw [← ipqnorm_def, ciSup_const, mul_comm] at le5
  exact le5

@[simp]
abbrev IpNorm p (M : Matrix m n 𝕂) := IpqNorm p p M

@[simp]
abbrev I1Norm (M : Matrix m n 𝕂) := IpNorm 1 M

@[simp]
abbrev ItNorm (M : Matrix m n 𝕂) := IpNorm ⊤ M

theorem i1norm_eq_max_col [Nonempty n] [DecidableEq n] :
    I1Norm M = ⨆ (j : n), LpNorm 1 (Matrix.col Unit (M · j)) := by
  apply le_antisymm
  · simp only [I1Norm, IpNorm, IpqNorm]
    have : ∀ x ∈ ((fun (v : Matrix n Unit 𝕂) ↦ LpNorm 1 (M * v)) '' {x | LpNorm 1 x = 1}),
        x ≤ ⨆ j, LpNorm 1 (col Unit fun x ↦ M x j) := by
      intro x xin
      have : ∀ v ∈ {(x : Matrix n Unit 𝕂) | LpNorm 1 x = 1},
          (fun v ↦ LpNorm 1 (M * v)) v ≤ ⨆ j, LpNorm 1 (col Unit fun x ↦ M x j) := by
        intro v vin
        have : (1 : ℝ≥0∞) ≠ ⊤ := by exact ENNReal.one_ne_top
        dsimp only
        simp only [LpNorm, if_neg this, Matrix.mul_apply, Finset.univ_unique, PUnit.default_eq_unit,
          ENNReal.one_toReal, Real.rpow_one, Finset.sum_singleton, ne_eq, one_ne_zero, not_false_eq_true,
          div_self, col_apply, Finset.sum_const, Finset.card_singleton, one_smul, ge_iff_le]
        have : ∑ x : m, ‖∑ j : n, M x j * v j PUnit.unit‖ ≤
            ∑ x : m, ∑ j : n, ‖M x j‖ * ‖v j PUnit.unit‖ := by
          apply Finset.sum_le_sum
          intro i _
          apply norm_sum_le_of_le Finset.univ
          intro j _
          exact NormedRing.norm_mul (M i j) (v j PUnit.unit)
        apply le_trans this
        have : ∑ x : m, ∑ j : n, ‖M x j‖ * ‖v j PUnit.unit‖ =
            ∑ j : n, ‖v j PUnit.unit‖ * ∑ x : m,  ‖M x j‖ := by
          conv_lhs =>
            enter [2]
            intro x
            enter [2]
            intro j
            rw [mul_comm]
          rw [Finset.sum_comm]
          conv_lhs =>
            enter [2]
            intro x
            rw [← Finset.mul_sum]
        rw [this]
        have : ∀ (j : n), ∑ x : m, ‖M x j‖ ≤ ⨆ (j : n), ∑ x : m, ‖M x j‖ := by
          intro j
          apply le_ciSup (f := fun j => ∑ x : m, ‖M x j‖)
          exact Finite.bddAbove_range fun j ↦ ∑ x : m, ‖M x j‖
        have : ∑ j : n, ‖v j PUnit.unit‖ * ∑ x : m, ‖M x j‖ ≤
            ∑ j : n, ‖v j PUnit.unit‖ * ⨆ (j : n), ∑ x : m, ‖M x j‖ :=
          Finset.sum_le_sum (fun i _ => mul_le_mul (Preorder.le_refl ‖v i PUnit.unit‖) (this i)
            (Finset.sum_nonneg (fun j _ => norm_nonneg (M j i))) (norm_nonneg (v i PUnit.unit)))
        apply le_trans this
        have : ∑ j : n, ‖v j PUnit.unit‖ * ⨆ j, ∑ x : m, ‖M x j‖ =
            (∑ j : n, ‖v j PUnit.unit‖) * (⨆ j, ∑ x : m, ‖M x j‖) := by
          conv_lhs =>
            enter [2]
            intro j
            rw [mul_comm]
          rw [← Finset.mul_sum, mul_comm]
        rw [this]
        have : ∑ j : n, ‖v j PUnit.unit‖ = 1 := by
          simp only [LpNorm, ENNReal.one_ne_top, ↓reduceIte, Finset.univ_unique,
            PUnit.default_eq_unit, ENNReal.one_toReal, Real.rpow_one, Finset.sum_singleton, ne_eq,
            one_ne_zero, not_false_eq_true, div_self, Set.mem_setOf_eq] at vin
          exact vin
        rw [this, one_mul]
      simp_all only [LpNorm, ENNReal.one_ne_top, ↓reduceIte, Finset.univ_unique, PUnit.default_eq_unit,
        ENNReal.one_toReal, Real.rpow_one, Finset.sum_singleton, ne_eq, one_ne_zero, not_false_eq_true,
        div_self, Set.mem_image, Set.mem_setOf_eq, col_apply, Finset.sum_const, Finset.card_singleton,
        one_smul, ge_iff_le]
      obtain ⟨w, h⟩ := xin
      obtain ⟨left, right⟩ := h
      subst right
      simp_all only
    refine Real.sSup_le this ?_
    have : ∀ (j : n), 0 ≤ LpNorm 1 (col Unit fun x ↦ M x j) :=
      fun j ↦ lpnorm_nonneg 1 (col Unit fun x ↦ M x j)
    exact Real.iSup_nonneg this
  · simp only [I1Norm, IpNorm, IpqNorm]
    refine Real.iSup_le ?_ ?_
    · have : ∀ (i : n), LpNorm 1 (col Unit fun x ↦ M x i) ≤
          ⨆ (i : n), LpNorm 1 (col Unit fun x ↦ M x i) := by
        intro i
        apply le_ciSup (f := fun i => LpNorm 1 (col Unit fun x ↦ M x i))
        exact Finite.bddAbove_range fun i ↦ LpNorm 1 (col Unit fun x ↦ M x i)
      intro i
      apply le_trans (this i)
      apply le_csSup
      exact ipqnorm_bddabove 1 1 M
      refine
        (Set.mem_image (fun v ↦ LpNorm 1 (M * v)) {x | LpNorm 1 x = 1}
              (⨆ i, LpNorm 1 (col Unit fun x ↦ M x i))).mpr
          ?_
      conv =>
        enter [1]
        intro x
        enter [2]
        rw [eq_comm]
      have : ∃ (i : n), LpNorm 1 (col Unit fun x ↦ M x i) =
          ⨆ i, LpNorm 1 (col Unit fun x ↦ M x i) := by
        refine exists_eq_ciSup_of_finite
      rcases this with ⟨x, hx⟩
      let v : Matrix n Unit 𝕂 := fun i _ => if i = x then 1 else 0
      use v
      constructor
      · simp only [LpNorm, ENNReal.one_ne_top, ↓reduceIte, Finset.univ_unique, PUnit.default_eq_unit,
          ENNReal.one_toReal, Real.rpow_one, Finset.sum_singleton, ne_eq, one_ne_zero,
          not_false_eq_true, div_self, Set.mem_setOf_eq, v]
        rw [Finset.sum_eq_single_of_mem x]
        simp only [↓reduceIte, norm_one]
        exact Finset.mem_univ x
        intros
        simp only [norm_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false]
        assumption
      · simp only [LpNorm, ENNReal.one_ne_top, ↓reduceIte, Finset.univ_unique,
          PUnit.default_eq_unit, col_apply, ENNReal.one_toReal, Real.rpow_one, Finset.sum_const,
          Finset.card_singleton, one_smul, ne_eq, one_ne_zero, not_false_eq_true, div_self,
          Finset.sum_singleton, v]
        have : ⨆ i, ∑ x : m, ‖M x i‖ = ⨆ i, LpNorm 1 (col Unit fun x ↦ M x i) := by
          congr
          ext i
          simp only [LpNorm, ENNReal.one_ne_top, ↓reduceIte, Finset.univ_unique,
            PUnit.default_eq_unit, col_apply, ENNReal.one_toReal, Real.rpow_one, Finset.sum_const,
            Finset.card_singleton, one_smul, ne_eq, one_ne_zero, not_false_eq_true, div_self]
        rw [this, ← hx, LpNorm]
        have : (1 : ℝ≥0∞) ≠ ⊤ := by exact ENNReal.one_ne_top
        simp only [if_neg this, Finset.univ_unique, PUnit.default_eq_unit, col_apply,
          ENNReal.one_toReal, Real.rpow_one, Finset.sum_const, Finset.card_singleton, one_smul,
          ne_eq, one_ne_zero, not_false_eq_true, div_self, mul_apply]
        simp_all only [LpNorm, ↓reduceIte, Finset.univ_unique, PUnit.default_eq_unit,
          ENNReal.one_toReal, Real.rpow_one, Finset.sum_singleton, ne_eq, one_ne_zero,
          not_false_eq_true, div_self, Set.mem_image, Set.mem_setOf_eq,col_apply,
          Finset.sum_const, Finset.card_singleton, one_smul, exists_exists_and_eq_and,
          ENNReal.one_ne_top,mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
    · rw [← IpqNorm]
      exact ipqnorm_nonneg 1 1 M

theorem sum_norm_eq_norm_sum_ofreal (f : n → 𝕂) : ∑ x : n, ‖f x‖ = ‖∑ x : n, RCLike.ofReal (K:=𝕂) ‖f x‖‖ := by
  have : ∑ x : n, ‖f x‖ = ‖∑ x : n, ↑‖f x‖‖ := by
    simp only [Real.norm_eq_abs]
    rw [abs_eq_self.mpr]
    apply Finset.sum_nonneg
    intro j _
    exact norm_nonneg (f j)
  rw [this]
  have : ‖∑ x : n, ‖f x‖‖ = ‖∑ x : n, (‖f x‖ : 𝕂)‖ := by
    simp only [Real.norm_eq_abs]
    have : (∑ x : n, (RCLike.ofReal ‖f x‖)) = (RCLike.ofReal (K:=𝕂) (∑ x : n, ‖f x‖)) := by
      simp only [map_sum]
    rw [this, RCLike.norm_ofReal]
  rw [this]

theorem itnorm_eq_max_row [DecidableEq n] [Inhabited n] [Nonempty m] [LE 𝕂] :
    ItNorm M = ⨆ (i : m), LpNorm 1 (Matrix.row Unit (M i)) := by
  apply le_antisymm
  · simp only [ItNorm, IpNorm, ipqnorm_def]
    apply Real.iSup_le
    · intro v
      by_cases h : LpNorm ⊤ v = 0
      · rw [h, div_zero]
        exact Real.iSup_nonneg (fun i => lpnorm_nonneg 1 (row Unit (M i)))
      rw [div_le_iff₀ (lt_of_le_of_ne (lpnorm_nonneg ⊤ v) fun a ↦ h (id (Eq.symm a)))]
      simp only [LpNorm, ↓reduceIte, ciSup_unique, PUnit.default_eq_unit, ENNReal.one_ne_top,
        Finset.univ_unique, row_apply, ENNReal.one_toReal, Real.rpow_one, Finset.sum_const,
        Finset.card_singleton, one_smul, ne_eq, one_ne_zero, not_false_eq_true, div_self]
      apply ciSup_le
      intro i
      simp only [mul_apply]
      have : ‖∑ j : n, M i j * v j PUnit.unit‖ ≤ ∑ j : n, ‖M i j‖ * ‖v j PUnit.unit‖ :=
        norm_sum_le_of_le Finset.univ (fun b _ => NormedRing.norm_mul (M i b) (v b PUnit.unit))
      apply le_trans this
      have : ∀ j, ‖v j PUnit.unit‖ ≤ ⨆ i, ‖v i PUnit.unit‖ :=
        fun j => le_ciSup (f := fun i => ‖v i PUnit.unit‖)
          (Finite.bddAbove_range fun i ↦ ‖v i PUnit.unit‖) j
      have : ∑ j : n, ‖M i j‖ * ‖v j PUnit.unit‖ ≤
          (∑ j : n, ‖M i j‖) * (⨆ j, ‖v j PUnit.unit‖) := by
        rw [Finset.sum_mul]
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul
        exact Preorder.le_refl ‖M i j‖
        apply le_ciSup (f := fun j => ‖v j PUnit.unit‖)
          (Finite.bddAbove_range fun j ↦ ‖v j PUnit.unit‖)
        exact norm_nonneg (v j PUnit.unit)
        exact norm_nonneg (M i j)
      apply le_trans this
      apply mul_le_mul
      · apply le_ciSup (f := fun i => ∑ x : n, ‖M i x‖)
          (Finite.bddAbove_range fun i ↦ ∑ x : n, ‖M i x‖)
      exact Preorder.le_refl (⨆ j, ‖v j PUnit.unit‖)
      apply Real.iSup_nonneg (fun i => norm_nonneg (v i PUnit.unit))
      apply Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => norm_nonneg (M i j)))
    · apply Real.iSup_nonneg
      intro i
      exact lpnorm_nonneg 1 (row Unit (M i))
  · have : ∃ i, LpNorm 1 (row Unit (M i)) = ⨆ i, LpNorm 1 (row Unit (M i)) := by
      exact exists_eq_ciSup_of_finite
    rcases this with ⟨i, hi⟩
    let v : Matrix n Unit 𝕂 := fun j _ => if M i j = 0 then 1 else (star (M i j)) / ‖M i j‖
    have hv : LpNorm ⊤ v = 1 := by
      simp only [LpNorm, ↓reduceIte, RCLike.star_def, ciSup_unique, v]
      have : (1 : ℝ) = ⨆ (j : n), 1 := by
        exact Eq.symm ciSup_const
      rw [this]
      congr
      ext x
      by_cases h : M i x = 0
      · simp only [h, ↓reduceIte, norm_one]
      simp only [h, ↓reduceIte, norm_div, RCLike.norm_conj, norm_algebraMap', norm_norm, ne_eq,
        norm_eq_zero, not_false_eq_true, div_self]
    rw [← hi, ItNorm, IpNorm, ipqnorm_def]
    have : LpNorm 1 (row Unit (M i)) ≤ ‖(M * v) i PUnit.unit‖ := by
      simp only [LpNorm, ENNReal.one_ne_top, ↓reduceIte, Finset.univ_unique, PUnit.default_eq_unit,
        row_apply, ENNReal.one_toReal, Real.rpow_one, Finset.sum_const, Finset.card_singleton,
        one_smul, ne_eq, one_ne_zero, not_false_eq_true, div_self, v, mul_apply]
      simp only [RCLike.star_def, mul_ite, mul_one]
      have : ∀ x, M i x * ((starRingEnd 𝕂) (M i x) / ↑‖M i x‖) = ↑‖M i x‖ := by
        intro x
        by_cases h : (RCLike.ofReal ‖M i x‖) = (0 : 𝕂)
        · simp only [h, div_zero, mul_zero]
        rw [mul_div, @RCLike.mul_conj, pow_two, ← mul_div, div_self, mul_one]
        assumption
      simp_rw [this]
      have : (∑ x : n, if M i x = 0 then M i x else RCLike.ofReal ‖M i x‖) =
          ∑ x : n, RCLike.ofReal ‖M i x‖ := by
        congr
        ext x
        by_cases h : M i x = 0
        · simp only [h, if_pos, norm_zero, map_zero]
        simp only [if_neg h]
      rw [this, sum_norm_eq_norm_sum_ofreal]
    apply le_trans this
    have : ‖(M * v) i PUnit.unit‖ ≤ ⨆ j, ‖(M * v) j PUnit.unit‖ := by
      apply le_ciSup (f := fun i => ‖(M * v) i PUnit.unit‖)
      exact Finite.bddAbove_range fun i ↦ ‖(M * v) i PUnit.unit‖
    apply le_trans this
    have : ⨆ j, ‖(M * v) j PUnit.unit‖ = LpNorm ⊤ (M * v) := by
      simp only [LpNorm, ↓reduceIte, ciSup_unique, PUnit.default_eq_unit]
    rw [this, ← div_one (LpNorm ⊤ (M * v)), ← hv]
    apply le_ciSup (f := fun v => LpNorm ⊤ (M * v) / LpNorm ⊤ v)
    exact ipqnorm_bddabove' ⊤ ⊤ M

theorem i2tnorm_eq_max_l2norm_row [DecidableEq n] [Inhabited n] [LE 𝕂] [Nonempty m] :
    IpqNorm 2 ⊤ M = ⨆ (i : m), LpNorm 2 (Matrix.row Unit (M i)) := by
  apply le_antisymm
  · simp only [ipqnorm_def]
    apply ciSup_le
    intro v
    by_cases h : LpNorm 2 v = 0
    · rw [h, div_zero]
      apply Real.iSup_nonneg
      intro i
      exact lpnorm_nonneg 2 (row Unit (M i))
    rw [div_le_iff₀ (lt_of_le_of_ne (lpnorm_nonneg 2 v) fun a ↦ h (id (Eq.symm a))), LpNorm, if_pos]
    simp only [ciSup_unique, PUnit.default_eq_unit, mul_apply]
    have : ⨆ i, ‖∑ x : n, M i x * v x PUnit.unit‖ ≤
        ⨆ i, (∑ x : n, ‖(M i x)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) *
          (∑ x, ‖(v x PUnit.unit)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
      have : ∀ i, ‖∑ x : n, M i x * v x PUnit.unit‖ ≤ ∑ x : n, ‖M i x‖ * ‖v x PUnit.unit‖ :=
        fun i => norm_sum_le_of_le Finset.univ
          (fun b _ => NormedRing.norm_mul (M i b) (v b PUnit.unit))
      have : ∀ i, ‖∑ x : n, M i x * v x PUnit.unit‖ ≤
          (∑ x : n, ‖(M i x)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) * (∑ x, ‖(v x PUnit.unit)‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        fun i => le_trans (this i) (Real.inner_le_Lp_mul_Lq_of_nonneg
          Finset.univ ((Real.isConjExponent_iff_eq_conjExponent (one_lt_two)).mpr (by norm_num))
          (fun j _ => norm_nonneg (M i j)) (fun j _ => norm_nonneg (v j PUnit.unit)))
      refine ciSup_mono ?B this
      exact
        Finite.bddAbove_range fun i ↦
          (∑ x : n, ‖M i x‖ ^ 2) ^ (1 / 2) * (∑ x : n, ‖v x PUnit.unit‖ ^ 2) ^ (1 / 2)
    apply le_trans this
    have : (∑ x : n, ‖v x PUnit.unit‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = LpNorm 2 v := by
      simp only [LpNorm, ENNReal.two_ne_top, ↓reduceIte, Finset.univ_unique, PUnit.default_eq_unit,
        ENNReal.toReal_ofNat, Real.rpow_two, Finset.sum_singleton, one_div]
    conv_lhs =>
      enter [1]
      intro i
      rw [mul_comm, this]
    rw [← Real.mul_iSup_of_nonneg (lpnorm_nonneg 2 v), mul_comm]
    have : (⨆ i, (∑ x : n, ‖M i x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) = (⨆ i, LpNorm 2 (row Unit (M i))) := by
      apply iSup_congr
      intro i
      simp only [LpNorm, ENNReal.two_ne_top, PUnit.default_eq_unit, ↓reduceIte,
        Finset.univ_unique, PUnit.default_eq_unit, row_apply, Finset.sum_const,
        Finset.card_singleton, one_smul, ENNReal.toReal_ofNat]
    rw [this]
    rfl
  · have : ∃ i, LpNorm 2 (row Unit (M i)) =  ⨆ i, LpNorm 2 (row Unit (M i)) := by
      refine exists_eq_ciSup_of_finite
    rcases this with ⟨x, hx⟩
    let v : Matrix n Unit 𝕂 := fun j _ => (star (M x j)) / (LpNorm 2 (row Unit (M x)))
    have hv : LpNorm 2 v = 1 := by
      sorry
    rw [ipqnorm_def]
    have : ⨆ i, LpNorm 2 (row Unit (M i)) ≤ LpNorm ⊤ (M * v) / LpNorm 2 v := by
      rw [hv, div_one, ← hx]
      have : LpNorm 2 (row Unit (M x)) = ‖((M * v) x ())‖ := by
        simp only [mul_apply, v, RCLike.star_def]
        conv_rhs =>
          enter [1, 2]
          intro y
          rw [mul_div, mul_comm]
        have : ∀ y, M x y * (starRingEnd 𝕂) (M x y) = RCLike.ofReal (‖M x y‖ ^ (2 : ℝ)) := by
          intro y
          rw [RCLike.mul_conj]
          simp only [Real.rpow_two, map_pow]
        conv_rhs =>
          enter [1, 2]
          intro y
          rw [mul_comm, this y]
        have : ∀ y, (RCLike.ofReal (K:=𝕂) (‖M x y‖ ^ (2 : ℝ))) / (RCLike.ofReal (LpNorm 2 (row Unit (M x)))) = RCLike.ofReal ((‖M x y‖ ^ (2 : ℝ)) / (LpNorm 2 (row Unit (M x)))) := by
          intro y
          norm_cast
        conv_rhs =>
          enter [1, 2]
          intro y
          rw [this y]
        rw [← RCLike.ofReal_sum, @norm_algebraMap', Real.norm_eq_abs, abs_eq_self.mpr]
        simp_rw [div_eq_inv_mul]
        rw [← Finset.mul_sum]
        have : ∑ i : n, ‖M x i‖ ^ (2 : ℝ) = (LpNorm 2 (row Unit (M x))) ^ (2 : ℝ) := by
          have : (2 : ℝ≥0∞) ≠ ⊤ := by exact ENNReal.two_ne_top
          simp only [LpNorm, if_neg this, Finset.univ_unique,
            PUnit.default_eq_unit, row_apply, Finset.sum_const,
            Finset.card_singleton, one_div, one_smul]
          rw [← Real.rpow_mul]
          have : (ENNReal.toReal 2)⁻¹ * 2 = 1 := by
            simp only [ENNReal.toReal_ofNat, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              inv_mul_cancel₀]
          rw [this, Real.rpow_one]
          simp only [Real.rpow_two, ENNReal.toReal_ofNat]
          apply Finset.sum_nonneg
          intro y _
          apply Real.rpow_nonneg
          exact norm_nonneg (M x y)
        rw [this, Real.rpow_two]
        generalize LpNorm 2 (row Unit (M x)) = a
        by_cases h : a = 0
        · rw [h, zero_pow, mul_zero]
          exact Ne.symm (Nat.zero_ne_add_one 1)
        rw [@sq, ← mul_assoc, inv_mul_cancel₀, one_mul]
        assumption
        apply Finset.sum_nonneg
        intro y _
        rw [div_nonneg_iff]
        left
        constructor
        · simp only [Real.rpow_two, norm_nonneg, pow_nonneg]
        · exact lpnorm_nonneg 2 (row Unit (M x))
      rw [this]
      simp only [LpNorm, ↓reduceIte, ciSup_unique, PUnit.default_eq_unit]
      apply le_ciSup (f := fun i => ‖(M * v) i PUnit.unit‖)
      exact Finite.bddAbove_range fun i ↦ ‖(M * v) i PUnit.unit‖
    apply le_trans this
    apply le_ciSup (f := fun v => LpNorm ⊤ (M * v) / LpNorm 2 v)
    exact ipqnorm_bddabove' 2 ⊤ M


theorem i12norm_eq_max_l2norm_col [DecidableEq n] [Inhabited n] :
    IpqNorm 1 2 M = ⨆ (j : n), LpNorm 2 (Matrix.col Unit (M · j)) := by
  sorry







end InducedNorm

end Matrix
