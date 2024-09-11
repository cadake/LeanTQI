/-copyright todo-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Lp.PiLp
-- import LeanCopilot

set_option profiler true

noncomputable section

namespace Matrix

-- #print Norm
-- #check Norm
-- #print NormedSpace
-- #print Module

variable {𝕂 𝕂' E F α R : Type*}
variable {m n : Type*}

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
-- #check NNReal.inner_le_Lp_mul_Lq_tsum


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
def LpNorm (p : ℝ≥0∞) (M : Matrix m n 𝕂) : ℝ :=
  -- if p = 0 then {i | ‖M i‖ ≠ 0}.toFinite.toFinset.card
  if p = ∞ then ⨆ i, ⨆ j, ‖M i j‖
  else (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal)

/-- a function of lpnorm, of which LpNorm p M = ‖M‖₊ for p-/
def NNLpNorm (p : ℝ≥0∞) [Fact (1 ≤ p)] (M : Matrix m n 𝕂) : ℝ :=
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

-- set_option quotPrecheck false in
-- local notation "‖" e ":" "MatrixP" $m $n $𝕂 $p "‖ₚ" => (Norm (self := (lpMatrixSeminormedAddCommGroup (m:=$m) (n:=$n) (𝕂:=$𝕂) $p).toNorm)).norm e
-- set_option trace.Meta.synthInstance true in
-- example : ‖ M : MatrixP m n 𝕂 p‖ₚ = (0 : ℝ) := by sorry

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
    exact ge_one_toReal_ne_zero p hp
  conv_lhs =>
    enter [1, 2]
    intro x
    rw [← Real.rpow_mul,mul_comm,  mul_one_div_cancel, Real.rpow_one]
    rfl
    exact prne0
    exact this x

theorem lp_norm_eq_ciSup (M : MatrixP m n 𝕂 p) (hp : p = ∞) :
    ‖M‖ = ⨆ i, ⨆ j, ‖M i j‖ := by
  have : p ≠ 0 := by exact ge_one_ne_zero p
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
-- Lemma continuous_lpnorm p m n (A : 'M[C]_(m,n)) :
--   1 < p -> {for p, continuous (fun p0 : R => lpnorm p0 A)}.
theorem lpnorm_continuous_at_p (A : Matrix m n 𝕂) :
    ContinuousOn ((LpNorm (m := m) (n := n) (𝕂 := 𝕂) (M := A))) {p | 1 ≤ p} := by
  simp only [ContinuousOn, Set.mem_setOf_eq, ContinuousWithinAt, LpNorm]
  sorry

-- Lemma lpnorm_nincr (p1 p2 : R) (m n : nat) (A : 'M[C]_(m,n)) :
--   1 <= p1 <= p2 -> lpnorm p1 A >= lpnorm p2 A.
example (p₁ p₂ : ℝ≥0∞) [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)] (ple : p₁ ≤ p₂) :
    LpNorm p₁ M ≥ LpNorm p₂ M := by
  sorry

example (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤)
(ist₁ : Norm (Matrix m n 𝕂) := (lpMatrixNormedAddCommGroup p).toNorm)
: ist₁.norm M = 0 := by
  sorry
  -- rw [lp_norm_def p M hp]
example [Norm ℕ] : ‖(0 : ℝ)‖ = ‖(0 : ℕ)‖ := by sorry

example (p₁ p₂ : ℝ≥0∞) (hp₁ : p₁ ≠ ⊤) (hp₂ : p₂ ≠ ⊤) [Fact (1 ≤ p₁)] [Fact (1 ≤ p₂)]
    (ple : p₁ ≤ p₂) :
    ‖(M : MatrixP m n 𝕂 p₁)‖ ≤ ‖(M : MatrixP m n 𝕂 p₂)‖ := by
  -- simp?
  -- simp [ist₁.norm]
  -- rw [lp_norm_def p₁ A hp₁, lp_norm_def p₂ A' hp₂]
  sorry


end lpnorm

end Matrix
