import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import LeanTQI.MatrixPredicate
-- import LeanCopilot

set_option profiler true

variable {𝕂 𝕂' E F α R : Type*}
variable {m n : Type*}


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

-- #print Norm
-- #check Norm
-- #print NormedSpace
-- #print Module

section

variable [NormedField 𝕂] [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
variable [NormedSpace 𝕂 E] [NormedSpace 𝕂 F]

-- normv0
-- #check norm_zero

-- norm_zero
-- #check norm_eq_zero

-- normvMn
-- todo

-- normvMn
-- #check norm_neg

-- normv_ge0
-- #check norm_nonneg

-- norm_nonneg
-- todo

-- normv_real
-- #check Norm.norm

-- normv_gt0
-- #check norm_pos_iff

-- lev_normB
-- #check norm_sub_le

-- lev_distD
-- #check dist_triangle

-- levB_normD
-- todo

-- levB_dist
-- #check norm_sub_norm_le

-- lev_dist_dist
-- #check abs_norm_sub_norm_le

-- normv_sum
-- #check norm_tsum_le_tsum_norm


-- normvZV
-- todo

-- #check add_le_add_left

-- #check norm_smul

end


-- todo: seq_nth_ord_size_true


-- hoelder_ord: infinite NNReal
#check NNReal.inner_le_Lp_mul_Lq_tsum


-- NormRC
section lpnorm

open scoped NNReal ENNReal Matrix

-- local notation "‖" e "‖ₚ" => Norm.norm e

variable (p : ℝ≥0∞)
variable [RCLike 𝕂] [Fintype m] [Fintype n]
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
  by_cases h' : M = 0
  · simp only [zero_apply, h', norm_zero, Real.ciSup_const_zero, h, ENNReal.top_toReal,]
    simp only [Real.rpow_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, div_zero,
      one_ne_zero]
    sorry
    -- rw [Real.zero_rpow, mul_zero, mul_zero, Real.zero_rpow]

  have h₁ : 0 < (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal) := sorry
  have h₂ : 0 < ⨆ i, ⨆ j, ‖M i j‖ := sorry
  rw [← Real.exp_log h₁, ← Real.exp_log h₂, Real.exp_eq_exp, Real.log_rpow]
  have le : 1 / p.toReal * Real.log (∑ i : m, ∑ j : n, ‖M i j‖ ^ p.toReal) ≤ Real.log (⨆ i, ⨆ j, ‖M i j‖) := sorry
  have ge : Real.log (⨆ i, ⨆ j, ‖M i j‖) ≤  1 / p.toReal * Real.log (∑ i : m, ∑ j : n, ‖M i j‖ ^ p.toReal) := sorry
  apply Real.partialOrder.proof_4 _ _ le ge
  sorry







-- deprecated
-- Lemma lpnorm_nincr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) :
--   1 <= p1 <= p2 -> lpnorm p1 A >= lpnorm p2 A.
-- example (p₁ p₂ : ℝ≥0∞) [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (h₁ : p₁ ≠ ⊤) (h₂ : p₂ ≠ ⊤) (ple : p₁ ≤ p₂) :
--     LpNorm p₂ M ≤ LpNorm p₁ M := by
--   by_cases peq : p₁ = p₂
--   · rw [peq]
--   have pgt : p₁ < p₂ := by exact LE.le.lt_of_ne ple peq
--   simp only [LpNorm, if_neg h₁, if_neg h₂]
--   have eq1 : ∀ i j, ‖M i j‖ ^ p₂.toReal = ‖M i j‖ ^ p₁.toReal * ‖M i j‖ ^ (p₂.toReal - p₁.toReal) := by
--     intro i j
--     by_cases h : ‖M i j‖ = 0
--     · rw [h, Real.zero_rpow, Real.zero_rpow, Real.zero_rpow, zero_mul]
--       by_contra h'
--       have : p₁.toReal < p₂.toReal := by exact ENNReal.toReal_lt_toReal_if p₁ p₂ h₁ h₂ pgt
--       have p₁₂eq : p₂.toReal = p₁.toReal := by exact eq_of_sub_eq_zero h'
--       rw [p₁₂eq] at this
--       simp_all only [ne_eq, norm_eq_zero, sub_self, lt_self_iff_false]
--       exact ENNReal.ge_one_toReal_ne_zero p₁ h₁
--       exact ENNReal.ge_one_toReal_ne_zero p₂ h₂
--     · rw [← Real.rpow_add]
--       congr
--       linarith
--       apply (LE.le.gt_iff_ne (show ‖M i j‖ ≥ 0 by exact norm_nonneg (M i j))).mpr
--       exact h
--   have le1 : (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal) ≤
--       (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) * (∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal)) := by
--     calc
--       (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal) = (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal * ‖M i j‖ ^ (p₂.toReal - p₁.toReal)) := by
--         simp_rw [eq1]
--       _ ≤ (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal * ((∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal)))) := by
--         have : ∀ i j, ‖M i j‖ ^ (p₂.toReal - p₁.toReal) ≤ ∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal) :=
--           fun i j => Finset.single_le_sum' (M := fun i => fun j => ‖M i j‖ ^ (p₂.toReal - p₁.toReal))
--             (fun k l => Real.rpow_nonneg (norm_nonneg (M k l)) (p₂.toReal - p₁.toReal)) i j
--         have : ∀ i j, ‖M i j‖ ^ p₁.toReal * ‖M i j‖ ^ (p₂.toReal - p₁.toReal) ≤
--             ‖M i j‖ ^ p₁.toReal * ∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal) := by
--           intro i j
--           apply mul_le_mul (Preorder.le_refl (‖M i j‖ ^ p₁.toReal)) (this i j)
--           apply Real.rpow_nonneg (norm_nonneg (M i j)) (p₂.toReal - p₁.toReal)
--           apply Real.rpow_nonneg (norm_nonneg (M i j))
--         apply Finset.sum_le_sum
--         intro i iin
--         apply Finset.sum_le_sum
--         intro j jin
--         exact this i j
--       _ = (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) * (∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal)) := by
--         simp only [Finset.sum_mul]
--   have le2 : (∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal)) ≤
--       (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ ((p₂.toReal - p₁.toReal) / p₁.toReal) := by
--     have : (p₂.toReal - p₁.toReal) = p₁.toReal * (p₂.toReal - p₁.toReal) / p₁.toReal := by
--       rw [division_def, mul_assoc, mul_comm, mul_assoc, mul_comm p₁.toReal⁻¹, CommGroupWithZero.mul_inv_cancel, mul_one]
--       exact ENNReal.ge_one_toReal_ne_zero p₁ h₁
--     nth_rw 1 [this]
--     have : ∀ i j, ‖M i j‖ ^ (p₁.toReal * (p₂.toReal - p₁.toReal) / p₁.toReal) = (‖M i j‖ ^ p₁.toReal) ^ ((p₂.toReal - p₁.toReal) / p₁.toReal) := by
--       sorry
--     conv_lhs =>
--       enter [2]
--       intro i
--       conv =>
--         enter [2]
--         intro j
--         rw [this i j]
--     generalize (p₂.toReal - p₁.toReal) / p₁.toReal = p
--     sorry
--     -- apply lp.sum_rpow_le_norm_rpow

--   have le3 : (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) * (∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal)) ≤
--       (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ (p₂.toReal / p₁.toReal) := by
--     calc
--       (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) * (∑ i : m, ∑ j : n, ‖M i j‖ ^ (p₂.toReal - p₁.toReal)) ≤
--           (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) * (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ ((p₂.toReal - p₁.toReal) / p₁.toReal) := by
--         apply mul_le_mul_of_nonneg_left (a:=(∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal)) le2 (by sorry)
--       _ = (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ (p₂.toReal / p₁.toReal) := by
--         rw [← Real.rpow_one_add']
--         congr
--         ring_nf
--         rw [CommGroupWithZero.mul_inv_cancel]
--         linarith
--         exact ENNReal.ge_one_toReal_ne_zero p₁ h₁
--         apply Finset.sum_nonneg
--         intro i iin
--         apply Finset.sum_nonneg
--         intro j jin
--         apply Real.rpow_nonneg
--         exact norm_nonneg (M i j)
--         ring_nf
--         rw [CommGroupWithZero.mul_inv_cancel, ← add_sub_assoc, add_comm, add_sub_assoc, sub_self, add_zero, ← one_div, div_eq_mul_one_div]
--         simp only [one_div, one_mul, ne_eq, mul_eq_zero, inv_eq_zero, not_or]
--         -- rw [← ne_eq, ← ne_eq]
--         exact ⟨ENNReal.ge_one_toReal_ne_zero p₂ h₂, ENNReal.ge_one_toReal_ne_zero p₁ h₁⟩
--         exact ENNReal.ge_one_toReal_ne_zero p₁ h₁
--   have le4 : (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal) ≤
--       (∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ (p₂.toReal / p₁.toReal) := by
--     apply le_trans le1 le3
--   let tt := (Real.rpow_le_rpow_iff (x:=(∑ i : m, ∑ j : n, ‖M i j‖ ^ p₂.toReal)) (y:=(∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ (p₂.toReal / p₁.toReal)) (z:=(1/p₂.toReal)) (by sorry) (by sorry) (by sorry)).mpr le4
--   have : ((∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ (p₂.toReal / p₁.toReal)) ^ p₂.toReal⁻¹ = ((∑ i : m, ∑ j : n, ‖M i j‖ ^ p₁.toReal) ^ p₁.toReal⁻¹) := by
--     rw [← Real.rpow_mul]
--     ring_nf
--     nth_rw 2 [mul_comm]
--     rw [mul_assoc]
--     have : (p₂.toReal * p₂.toReal⁻¹) = 1 := by
--       ring_nf
--       refine CommGroupWithZero.mul_inv_cancel p₂.toReal ?_
--       exact ENNReal.ge_one_toReal_ne_zero p₂ h₂
--     rw [this, mul_one]
--     apply Finset.sum_nonneg
--     intro i iin
--     apply Finset.sum_nonneg
--     intro j jin
--     apply Real.rpow_nonneg (norm_nonneg (M i j))
--   simp only [one_div] at tt
--   rw [this] at tt
--   simp only [one_div, ge_iff_le]
--   exact tt





example [Fact (1 ≤ p)] : p ≠ 0 := ENNReal.ge_one_ne_zero p

example [Fact (1 ≤ p)] (h : p ≠ ⊤) : p⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h

example [Fact (1 ≤ p)] (h : p ≠ ⊤) : p.toReal ≠ 0 := ENNReal.ge_one_toReal_ne_zero p h

example [Fact (1 ≤ p)] (h : p ≠ ⊤) : p.toReal⁻¹ ≠ 0 := inv_ne_zero (ENNReal.ge_one_toReal_ne_zero p h)

example [Fact (1 ≤ p)] : 0 ≤ p := by exact zero_le p

example [Fact (1 ≤ p)] : 0 ≤ p.toReal := by exact ENNReal.toReal_nonneg











theorem lpnorm_eq0_iff : LpNorm p M = 0 ↔ M = 0 := by
  rw [← lp_norm_eq_lpnorm]
  exact norm_eq_zero

theorem lpnorm_nonneg : 0 ≤ LpNorm p M := by
  rw [← lp_norm_eq_lpnorm]
  exact norm_nonneg M

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

theorem lpnorm_elem_le_norm (i : m) (j : n) : ‖M i j‖ ≤ LpNorm p M := by
  simp only [LpNorm, one_div]
  by_cases h : p = ⊤
  · simp only [if_pos h]
    have le1 : ∀ i j, ‖M i j‖ ≤ (⨆ j, ‖M i j‖) := by
      intro i j
      change (fun j => ‖M i j‖) j ≤ iSup (fun j => ‖M i j‖)
      have : j ∈ Fintype.elems := by exact Fintype.complete j
      sorry
      -- apply Finset.le_sup (f:=fun j => ‖M i j‖) (this)
    have le2 : ∀ i, ⨆ j, ‖M i j‖ ≤ ⨆ i, ⨆ j, ‖M i j‖ := by sorry
    exact Preorder.le_trans ‖M i j‖ (⨆ j, ‖M i j‖) (⨆ i, ⨆ j, ‖M i j‖) (le1 i j) (le2 i)
  · simp only [if_neg h]
    sorry

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







-- just an example
-- example (p₁ p₂ : ℝ≥0∞) (hp₁ : p₁ ≠ ⊤) (hp₂ : p₂ ≠ ⊤) [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)]
--     (ple : p₁ ≤ p₂) :
--     ‖(M : MatrixP m n 𝕂 p₁)‖ ≤ ‖(M : MatrixP m n 𝕂 p₂)‖ := by
  -- simp?
  -- simp [ist₁.norm]
  -- rw [lp_norm_def p₁ A hp₁, lp_norm_def p₂ A' hp₂]






-- todo
-- Lemma lpnorm_ndecr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) :
--   1 <= p1 <= p2 ->
--   lpnorm p1 A / ((m * n)%:R `^ p1^-1)%:C <= lpnorm p2 A / ((m * n)%:R `^ p2^-1)%:C.









-- todo
-- #check CompleteLattice.toSupSet
-- #check
#check OrderBot
#check Finset.comp_sup_eq_sup_comp
#check iSup_comm
#check Finset.sup_comm
-- Lemma lpnorm_trmx p q r (M: 'M[C]_(q,r)) : lpnorm p (M^T) = lpnorm p M.
-- Proof. by rewrite lpnorm.unlock lpnormrc_trmx. Qed.
set_option trace.Meta.synthInstance true in
@[simp]
theorem lpnorm_transpose (M : MatrixP m n 𝕂 p) : ‖Mᵀ‖ = ‖M‖ := by
  by_cases hp : p = ⊤
  · rw [lp_norm_eq_ciSup p M hp, lp_norm_eq_ciSup p Mᵀ hp, transpose]
    dsimp only [of_apply]
    let norm' (m:=M) := fun i j => norm (M i j)
    have : ∀ i j, ‖M i j‖ = norm' M i j := by simp only [implies_true]
    simp_rw [this]
    -- let ttt : ⨆ i, ⨆ j, norm' M j i = ⨆ i, ⨆ j, norm' M i j := eq_of_forall_ge_iff fun a => by simpa using forall_swap
    -- let tt := Finset.sup_comm m n (norm' M)
    sorry
    -- show ⨆ i, ⨆ j, norm' M j i = ⨆ i, ⨆ j, norm' M i j
    -- let tt := Set.finite_range (fun i => fun j => ‖M i j‖)
    -- let ttt := Fintype.toCompleteLattice tt
    -- rw [iSup_comm (f:=norm' M)]
  · rw [lp_norm_def p M hp, lp_norm_def p Mᵀ hp, transpose]
    dsimp only [of_apply]
    rw [Finset.sum_comm]









-- todo
-- Lemma lpnorm_diag p q (D : 'rV[C]_q) : lpnorm p (diag_mx D) = lpnorm p D.





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
    · have : Set.EqOn (fun (p : ℝ≥0∞) ↦ (∑ i : m, ∑ j : n, 0)) (fun p ↦ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal)) {p | 1 ≤ p ∧ p ≠ ⊤} := by
        intro p pin
        have : Fact (1 ≤ p) := {out := pin.left}
        have : p.toReal ≠ 0 := ENNReal.ge_one_toReal_ne_zero p pin.right
        simp_rw [Finset.sum_const_zero, h, one_div, zero_apply, norm_zero,
          Real.zero_rpow this, Finset.sum_const_zero, Real.zero_rpow (inv_ne_zero this)]
      exact (continuousOn_congr this).mp continuousOn_const
    have eqon : Set.EqOn (fun (p : ℝ≥0∞) ↦ Real.exp (Real.log ((∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal)))) (fun (p : ℝ≥0∞) ↦ (∑ i : m, ∑ j : n, ‖A i j‖ ^ p.toReal) ^ (1 / p.toReal)) {p | 1 ≤ p ∧ p ≠ ⊤} := by
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
    have eqon' : Set.EqOn (fun (y : ℝ≥0∞) ↦ (1 / y.toReal) * Real.log ((∑ i : m, ∑ j : n, ‖A i j‖ ^ y.toReal))) (fun y ↦ Real.log ((∑ i : m, ∑ j : n, ‖A i j‖ ^ y.toReal) ^ (1 / y.toReal))) {p | 1 ≤ p ∧ p ≠ ⊤} := by
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
      · have : Set.EqOn (fun (x : ℝ≥0∞) ↦ Real.exp <| Real.log <| ‖A i j‖ ^ x.toReal) (fun x ↦ ‖A i j‖ ^ x.toReal) {p | 1 ≤ p ∧ p ≠ ⊤} := by
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
        exact (continuousOn_congr this).mp (ContinuousOn.mul (ContinuousOn.mono ENNReal.continuousOn_toReal <| fun p pin => pin.right) (continuousOn_const))
      intro p pin
      have : Fact (1 ≤ p) := {out := pin.left}
      exact lpnorm_rpow_ne0 p A (fun h' => h ((lpnorm_eq0_iff p A).mp h')) pin.right








end lpnorm

end Matrix
