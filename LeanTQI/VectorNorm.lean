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
  apply (ENNReal.ofReal_lt_ofReal_iff_of_nonneg _).mp
  rw [ENNReal.ofReal_toReal, ENNReal.ofReal_toReal] <;> assumption
  exact ENNReal.toReal_nonneg

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

end Finset



noncomputable section

namespace Matrix


-- NormRC
section lpnorm

open scoped NNReal ENNReal Finset Matrix

-- local notation "‖" e "‖ₚ" => Norm.norm e

variable (p p₁ p₂ : ℝ≥0∞)
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

/-- a function of lpnorm, of which LpNorm p M = ‖M‖₊ for p-/
@[simp]
def LpNNNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix m n 𝕂) : ℝ :=
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

theorem lp_norm_eq_ciSup (M : MatrixP m n 𝕂 p) (hp : p = ∞) :
    ‖M‖ = ⨆ i, ⨆ j, ‖M i j‖ := by
  have : p ≠ 0 := by exact ENNReal.ge_one_ne_zero p
  have : p ≠ 0 := by exact ENNReal.ge_one_ne_zero p
  simp only [MatrixP, norm, if_neg this, if_pos hp]

theorem lp_norm_def (M : MatrixP m n 𝕂 p) (hp : p ≠ ∞) :
    ‖M‖ = (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal) :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) (lp_nnnorm_def p M hp)).trans <| by simp only [one_div,
    NNReal.coe_rpow, NNReal.coe_sum, coe_nnnorm]

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
theorem lpnorm_rpow_nonneg : 0 ≤ ∑ i, ∑ j, ‖M i j‖ ^ p.toReal := by
  apply Fintype.sum_nonneg
  have : ∀ i, 0 ≤ (fun i ↦ ∑ j : n, ‖M i j‖ ^ p.toReal) i := by
    intro i
    simp only
    apply Fintype.sum_nonneg
    intro j
    simp only [Pi.zero_apply]
    exact Real.rpow_nonneg (norm_nonneg (M i j)) p.toReal
  exact this

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
  · apply div_le_one_of_le (lpnorm_elem_le_norm p M i j) (lpnorm_nonneg p M)

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
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
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
theorem lpnorm_diag [DecidableEq m] (d : m → 𝕂) (h : p ≠ ⊤) : LpNorm p (Matrix.diagonal d) = (∑ i, ‖d i‖ ^ p.toReal) ^ (1 / p.toReal) := by
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

example (ple2 : p ≤ 2) (h : p ≠ ⊤) : LpNorm p (A * B) ≤ (LpNorm p A) * (LpNorm p B) := by
  simp only [LpNorm, one_div, mul_ite, ite_mul, if_neg h]
  have ABpnn : 0 ≤ (∑ i : m, ∑ j : l, ‖(A * B) i j‖ ^ p.toReal) := by
    exact lpnorm_rpow_nonneg p (A * B)
  have Apnn : 0 ≤ ∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal := by
    exact lpnorm_rpow_nonneg p A
  have Arpnn : ∀ i, 0 ≤ ∑ k : n, ‖A i k‖ ^ p.toReal :=
    fun i => Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (norm_nonneg (A i k)) p.toReal)
  have Bpnn : 0 ≤ ∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal := by
    exact lpnorm_rpow_nonneg p B
  have ApBpnn : 0 ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) * (∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal) := by
    exact Left.mul_nonneg Apnn Bpnn
  have ppos : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).mpr h
  have pinvpos : 0 < p.toReal⁻¹ := inv_pos_of_pos ppos
  rw [← Real.mul_rpow Apnn Bpnn, Real.rpow_le_rpow_iff ABpnn ApBpnn pinvpos]

  have : ∀ (i : m) (j : l), ‖(A * B) i j‖ ≤ ∑ (k : n), ‖A i k‖ * ‖B k j‖ := by
    intro i j
    simp [Matrix.mul_apply]
    exact norm_sum_le_of_le Finset.univ (fun k kin => NormedRing.norm_mul (A i k) (B k j))

  -- by_cases hp : p = 1
  -- · simp only [hp, ENNReal.one_toReal, Real.rpow_one, ge_iff_le]
  by_cases hp : p.toReal = 1
  · sorry
  let q := p.toReal.conjExponent
  have hpq : p.toReal.IsConjExponent q := by
    refine Real.IsConjExponent.conjExponent ?h
    have : 1 ≤ p.toReal := by
      cases ENNReal.dichotomy p
      · contradiction
      assumption
    exact lt_of_le_of_ne this fun a ↦ hp (id (Eq.symm a))
  have s : Finset n := Finset.univ
  calc
    ∑ i : m, ∑ j : l, ‖(A * B) i j‖ ^ p.toReal ≤ ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ * ‖B k j‖) ^ p.toReal := by
      apply Finset.sum_le_sum
      intro i iin
      apply Finset.sum_le_sum
      intro j jin
      rw [Real.rpow_le_rpow_iff (norm_nonneg <| (A * B) i j)
        (Finset.sum_nonneg  fun k _ => mul_nonneg (norm_nonneg (A i k)) (norm_nonneg (B k j))) ppos]
      exact this i j
    _ ≤ ∑ i, ∑ j, ((∑ (k : n), ‖A i k‖ ^ p.toReal) ^ p.toReal⁻¹ * (∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal := by
      apply Finset.sum_le_sum
      intro i iin
      apply Finset.sum_le_sum
      intro j jin
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
      exact Real.inner_le_Lp_mul_Lq (f := fun k => ‖A i k‖) (g := fun k => ‖B k j‖) (hpq := hpq) (Finset.univ)
    _ = ∑ i, ∑ j, (∑ (k : n), ‖A i k‖ ^ p.toReal) * ((∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal := by
      conv_lhs =>
        enter [2]
        intro i
        conv =>
          enter [2]
          intro j
          rw [Real.mul_rpow (Real.rpow_nonneg (Arpnn i) p.toReal⁻¹)
              (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg (B i j)) q)) q⁻¹),
              ← Real.rpow_mul <| Arpnn i, inv_mul_cancel₀ <| ENNReal.ge_one_toReal_ne_zero p h, Real.rpow_one]
    _ = (∑ i, ∑ (k : n), (‖A i k‖ ^ p.toReal)) * (∑ j, ((∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal) := by
      rw [← Finset.sum_mul_sum Finset.univ Finset.univ (fun i => ∑ (k : n), (‖A i k‖ ^ p.toReal)) (fun j => ((∑ k, ‖B k j‖ ^ q) ^ q⁻¹) ^ p.toReal)]
    _ ≤ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) * ∑ i : n, ∑ j : l, ‖B i j‖ ^ p.toReal := by
      by_cases h' : ∑ i : m, ∑ k : n, ‖A i k‖ ^ p.toReal = 0
      · simp only [h', zero_mul, le_refl]
      have h' : 0 < ∑ i : m, ∑ k : n, ‖A i k‖ ^ p.toReal := by
        have : 0 ≤ ∑ i : m, ∑ k : n, ‖A i k‖ ^ p.toReal := by
          apply Finset.sum_nonneg
          intro i iin
          apply Finset.sum_nonneg
          intro j jin
          exact Real.rpow_nonneg (norm_nonneg (A i j)) p.toReal
        exact lt_of_le_of_ne Apnn fun a ↦ h' (id (Eq.symm a))
      rw [mul_le_mul_left h', Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i iin
      have : ((∑ k : n, ‖B k i‖ ^ q) ^ q⁻¹) ≤ ((∑ k : n, ‖B k i‖ ^ p.toReal) ^ p.toReal⁻¹) := by
        have : p.toReal ≤ q := by
          sorry

        let B' : Matrix n Unit 𝕂 := Matrix.col Unit (fun k : n => B k i)
        have : (∑ k : n, ‖B k i‖ ^ q) ^ q⁻¹ = (∑ k : n, ‖B' k ()‖ ^ q) ^ q⁻¹ := by
          exact rfl
        rw [this]
        have : (∑ k : n, ‖B k i‖ ^ p.toReal) ^ p.toReal⁻¹ = (∑ k : n, ‖B' k ()‖ ^ p.toReal) ^ p.toReal⁻¹ := by
          exact rfl
        rw [this]

        have : (∑ k : n, ‖B' k ()‖ ^ q) ^ q⁻¹ = (∑ k : n, ∑ j : Unit, ‖B' k j‖ ^ q) ^ q⁻¹ := by
          have : ∀ k : n, ∑ j : Unit, ‖B' k ()‖ ^ q = ‖B' k ()‖ ^ q := by
            intro k
            exact Fintype.sum_unique fun x ↦ ‖B' k ()‖ ^ q
          simp_rw [this]
        rw [this]
        have : (∑ k : n, ‖B' k ()‖ ^ p.toReal) ^ p.toReal⁻¹ = (∑ k : n, ∑ j : Unit, ‖B' k j‖ ^ p.toReal) ^ p.toReal⁻¹ := by
          have : ∀ k : n, ∑ j : Unit, ‖B' k ()‖ ^ p.toReal = ‖B' k ()‖ ^ p.toReal := by
            intro k
            exact Fintype.sum_unique fun x ↦ ‖B' k ()‖ ^ p.toReal
          simp_rw [this]
        rw [this]


        let q' : ℝ≥0∞ := ENNReal.ofReal q
        have hq : q' ≠ ⊤ := ENNReal.ofReal_ne_top
        have : q = q'.toReal := by
          refine Eq.symm (ENNReal.toReal_ofReal ?h)
          exact Real.IsConjExponent.nonneg (id (Real.IsConjExponent.symm hpq))
        rw [this, ← one_div, ← one_div]
        have inst : Fact (1 ≤ q') := by
          refine { out := ?out }
          refine ENNReal.one_le_ofReal.mpr ?out.a
          rw [show q = p.toReal / (p.toReal - 1) by rfl]
          rw [one_le_div_iff]
          left
          sorry
        have pleq : p ≤ q' := by
          refine (ENNReal.le_ofReal_iff_toReal_le h ?hb).mpr (by assumption)
          exact ENNReal.toReal_ofReal_eq_iff.mp (id (Eq.symm this))


        rw [← lp_norm_def q' B' hq, lp_norm_eq_lpnorm, ← lp_norm_def p B' h, lp_norm_eq_lpnorm]
        apply lpnorm_antimono B' p q' h hq pleq

      refine (Real.le_rpow_inv_iff_of_pos ?_ ?_ ppos).mp this
      · exact Real.rpow_nonneg (Finset.sum_nonneg (fun i' _ => Real.rpow_nonneg (norm_nonneg (B i' i)) q)) q⁻¹
      exact (Finset.sum_nonneg (fun i' _ => Real.rpow_nonneg (norm_nonneg (B i' i)) p.toReal))

#check Singleton



end lpnorm




end Matrix
