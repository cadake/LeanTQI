import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Deprecated.Group
-- import LeanCopilot

#check OrderedAddCommMonoid
#check OrderedSMul
#check Module

universe u v w

variable {R M N : Type*}
variable {U V W : Type*}
-------------------------------------order

-- scalerNN
-- todo

-- lev_add2rP : forall (z x y : T), x ⊑ y -> (x + z) ⊑ (y + z);
#check OrderedAddCommGroup.add_le_add_left
-- lev_pscale2lP : forall (e : R) (x y : T), 0 < e -> x ⊑ y -> (e *: x) ⊑ (e *: y);
#check OrderedSMul.smul_lt_smul_of_pos

-- todo: orderedField
class OrderedVectorSpace (R : Type u) (M : Type v)
  [OrderedRing R] [OrderedAddCommGroup M]
  extends Module R M, PosSMulMono R M
#print OrderedVectorSpace

-- pscalev_lge0 : forall (x : T) (e : R), 0 ⊏ x -> 0 ⊑ (e *: x) = (0 <= e);
class CanVOrderedVectorSpace (R : Type u) (M : Type v)
  [OrderedRing R] [OrderedAddCommGroup M]
  extends OrderedVectorSpace R M where
  pscalev_lge0 : ∀ (e : R) (x : M), 0 < x → (0 ≤ e • x ↔ 0 ≤ e)

instance CanVOrderedVectorSpace.toSMulPosReflectLE [OrderedRing R] [OrderedAddCommGroup M] [CanVOrderedVectorSpace R M] : SMulPosReflectLE R M where
  elim := by
    intro y ygt0 e₁ e₂ eyle
    have : 0 ≤ (e₂ - e₁) • y := by
      let g := tsub_le_tsub_right eyle (e₁ • y)
      rw [Eq.symm (sub_smul e₂ e₁ y), sub_self] at g
      assumption
    let g := (pscalev_lge0 (e₂ - e₁) y ygt0).mp this
    exact sub_nonneg.mp g

instance CanVOrderedVectorSpace.toSMulPosMono [OrderedRing R] [OrderedAddCommGroup M] [CanVOrderedVectorSpace R M] : SMulPosMono R M where
  elim := fun ⦃b⦄ hb ⦃a₁ a₂⦄ ha ↦ smul_le_smul_of_nonneg_right ha hb

-- instance CanVOrderedVectorSpace.toSMulPosStrictMono [OrderedRing R] [OrderedAddCommGroup M] [CanVOrderedVectorSpace R M] : SMulPosStrictMono R M where
--   elim := by
--     intro y ygt0 e₁ e₂ elte
--     let r := SMulPosMono.toSMulPosStrictMono (α:=R) (β :=M)






#check le_of_smul_le_smul_right
theorem smul_nonneg_iff_nonneg_left_of_pos_right [OrderedRing R] [OrderedAddCommGroup M] [OrderedVectorSpace R M] [SMulPosReflectLE R M]
  (e : R) (x : M) (xge0 : 0 < x) :
  0 ≤ e • x ↔ 0 ≤ e := by
  constructor <;> intro h
  · rw [← zero_smul R x] at h
    apply le_of_smul_le_smul_right h
    assumption
  refine smul_nonneg h ?mpr.hb
  exact le_of_lt xge0


class BRegVOrder {U V W : Type*} [OrderedAddCommGroup U] [OrderedAddCommGroup V] [OrderedAddCommGroup W]
  (f : U →+ V →+ W) where
  -- left_additive : ∀ v : V, IsAddHom (op · v)
  -- right_additive : ∀ u : U, IsAddHom (op u)
  bregv_eq0 u v : f u v = 0 ↔ u = 0 ∨ v = 0
  pbregv_rge0 u v (ugt0 : 0 < u) : 0 ≤ f u v ↔ 0 ≤ v
  pbregv_lge0 u v (vgt0 : 0 < v) : 0 ≤ f u v ↔ 0 ≤ u

-- attribute [simp] BRegVOrder.bregv_eq0
-- attribute [simp] BRegVOrder.pbregv_rge0
-- attribute [simp] BRegVOrder.pbregv_lge0

namespace VectorOrder

variable {R M N : Type*}
variable {U V W : Type*}

section OrderedVectorSpace

variable [OrderedRing R] [OrderedAddCommGroup M] [OrderedVectorSpace R M]

theorem smul_le_smul_of_pos_left {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂ : β} [SMul α β] [Preorder α]
  [Preorder β] [Zero α] [PosSMulMono α β] (hb : b₁ ≤ b₂) (ha : 0 < a) :
  a • b₁ ≤ a • b₂ := by
  apply smul_le_smul_of_nonneg_left (by assumption) (le_of_lt (by assumption))

-- subv_ge0
#check sub_nonneg

-- subv_gt0
-- subv_le0
-- subv_lt0

-- levN2
-- ltvN2
-- todo

end OrderedVectorSpace


section CanVOrderedVectorSpace

variable [OrderedRing R] [OrderedAddCommGroup M] [CanVOrderedVectorSpace R M]
variable (r : R) (m : M)

-- Lemma pscalev_lgt0 y a : '0 ⊏ y -> ('0 ⊏ a *: y) = (0 < a).
theorem pscalev_lgt0 [NoZeroSMulDivisors R M] (ygt0 : 0 < m) :
  0 < r • m ↔ 0 < r := by
  let leiff := CanVOrderedVectorSpace.pscalev_lge0 r m ygt0
  constructor <;> intro h
  · have : 0 ≤ r := leiff.mp (le_of_lt h)
    have : 0 ≠ r := by
      by_contra g
      have : r • m = 0 := smul_eq_zero_of_left (id (Eq.symm g)) m
      simp_all only [lt_self_iff_false]
    simp_all only [ne_eq, gt_iff_lt]
    positivity
  · have rmge0 : 0 ≤ r • m := leiff.mpr (le_of_lt h)
    have rmne0 : r • m ≠ 0 := by
      by_contra g
      let eq0or := (smul_eq_zero (c:=r) (x:=m)).mp g
      rcases eq0or with req0 | feq0
      · simp_all only [lt_self_iff_false]
      · rw [feq0] at ygt0
        simp_all only [lt_self_iff_false]
    exact lt_of_le_of_ne rmge0 (id (Ne.symm rmne0))









end CanVOrderedVectorSpace




section BRegVOrder

variable [OrderedAddCommGroup U] [OrderedAddCommGroup V] [OrderedAddCommGroup W]
variable (op : U →+ V →+ W) [BRegVOrder op]
variable (u u₁ u₂ : U) (v v₁ v₂ : V)

open BRegVOrder
open Function

-- bregv0r
@[simp]
theorem bregv0r : op u 0 = 0 := AddMonoidHom.map_zero (op u)

-- Lemma bregvNr a : {morph f a : x / - x}. Proof. exact: raddfN. Qed.
@[simp]
theorem bregvNr : op u (-v) = - op u v :=
  AddMonoidHom.map_neg (op u) v

-- Lemma bregvDr a : {morph f a : x y / x + y}. Proof. exact: raddfD. Qed.
@[simp]
theorem bregvDr : op u (v₁ + v₂) = op u v₁ + op u v₂ :=
  AddMonoidHom.map_add (op u) v₁ v₂

-- Lemma bregvBr a : {morph f a : x y / x - y}. Proof. exact: raddfB. Qed.
@[simp]
theorem bregvBr : op u (v₁ - v₂) = op u v₁ - op u v₂ :=
  AddMonoidHom.map_sub (op u) v₁ v₂

-- Lemma bregv0l x : f 0 x = 0. Proof. by rewrite -applyarE raddf0. Qed.
@[simp]
theorem bregv0l : op 0 v = 0 := AddMonoidHom.map_one₂ op v

-- Lemma bregvNl x : {morph f^~ x : x / - x}.
@[simp]
theorem bregvNl : op (-u) v = - op u v :=
  AddMonoidHom.map_inv₂ op u v

-- Lemma bregvDl x : {morph f^~ x : x y / x + y}.
@[simp]
theorem bregvDl : op (u₁ + u₂) v = op u₁ v + op u₂ v :=
  AddMonoidHom.map_mul₂ op u₁ u₂ v

-- Lemma bregvBl x : {morph f^~ x : x y / x - y}.
@[simp]
theorem bregvBl : op (u₁ - u₂) v = op u₁ v - op u₂ v :=
  AddMonoidHom.map_div₂ op u₁ u₂ v

-- Lemma bregvNN a x : f (-a) (-x) = f a x.
@[simp]
theorem bregvNN : op (-u) (-v) = op u v := by
  simp_all only [map_neg, AddMonoidHom.neg_apply, neg_neg]

-- pbregv_rgt0
@[simp]
theorem pbregv_rgt0 (ugt0 : 0 < u) :
  0 < op u v ↔ 0 < v := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, pbregv_rge0 (f:=op) u v ugt0, ne_comm, ne_comm (a:=0)]
  have : op u v ≠ 0 ↔ v ≠ 0 := by
    refine Iff.ne ?_
    simp only [bregv_eq0, or_iff_right_iff_imp]
    intro a
    subst a
    simp_all only [lt_self_iff_false]
  rw [this]

-- pbregv_lgt0
@[simp]
theorem pbregv_lgt0 (vgt0 : 0 < v) :
  0 < op u v ↔ 0 < u := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, pbregv_lge0 (f:=op) u v vgt0, ne_comm, ne_comm (a:=0)]
  have : op u v ≠ 0 ↔ u ≠ 0 := by
    refine Iff.symm (Iff.ne ?_)
    simp_all only [bregv_eq0, iff_self_or]
    intro a
    subst a
    simp_all only [lt_self_iff_false]
  rw [this]

-- Lemma bregvI_eq0 a x : a != 0 -> (f a x == 0) = (x == 0).
@[simp]
theorem bregvI_eq0 (une0 : u ≠ 0) :
  op u v = 0 ↔ v = 0 := by
  constructor <;> intro h
  · have : u = 0 ∨ v = 0 := (bregv_eq0 (f:=op) u v).mp h
    simp_all only [ne_eq, false_or]
  · apply (bregv_eq0 (f:=op) u v).mpr
    right
    assumption

-- Lemma bregvI a : a != 0 -> injective (f a).
theorem bregvI :
  u ≠ 0 → Injective (op u) := by
  intro une0
  intro v₁ v₂ opeq
  have opeq : op u v₁ + (- op u v₂) = 0 := add_neg_eq_zero.mpr opeq
  have : op u v₁ + (- op u v₂) = op u (v₁ + - v₂) := Eq.symm (AddMonoidHom.map_add_neg (op u) v₁ v₂)
  rw [this] at opeq
  have : u = 0 ∨ v₁ + -v₂ = 0 := (bregv_eq0 u (v₁ + -v₂)).mp opeq
  cases this
  · contradiction
  · exact add_neg_eq_zero.mp (by assumption)

-- Lemma bregIv_eq0 x a : x != 0 -> (f a x == 0) = (a == 0).
@[simp]
theorem bregIv_eq0 (une0 : u ≠ 0) : op u v = 0 ↔ v = 0 :=
  bregvI_eq0 op u v une0

-- Lemma bregIv x : x != 0 -> injective (f^~ x).
theorem bregIv : v ≠ 0 → Injective (op · v) := by
  intro vne0
  simp only [Injective]
  intro u₁ u₂ opeq
  have opeq : op u₁ v + (- op u₂ v) = 0 := add_neg_eq_zero.mpr opeq   --todo
  have : op (u₁ + -u₂) v = op u₁ v + -op u₂ v := by
    rw [AddMonoidHom.map_add_neg op u₁ u₂]
    exact rfl
  rw [← this] at opeq
  have : u₁ + - u₂ = 0 ∨ v = 0 := (bregv_eq0 (u₁ + -u₂) v).mp opeq
  cases this
  · exact add_neg_eq_zero.mp (by assumption)
  · contradiction

-- Lemma lev_pbreg2lP a x y : l0 ⊏ a -> x ⊑ y -> (f a x) ⊑ (f a y).
theorem lev_pbreg2lP (ugt0 : 0 < u) (vlev : v₁ ≤ v₂) :
  op u v₁ ≤ op u v₂ := by
  have := pbregv_rge0 (f:=op) u (v₂ - v₁) ugt0
  simp_all only [map_sub, sub_nonneg, iff_true]

-- Lemma lev_pbreg2l a : l0 ⊏ a -> {mono (f a) : x y / x ⊑ y}.
theorem lev_pbreg2l (ugt0 : 0 < u) : Monotone (op u) :=
  fun v₁ v₂ vlev => lev_pbreg2lP op u v₁ v₂ ugt0 vlev


#check U →+o V -- todo

-- Lemma ltv_pbreg2l a : l0 ⊏ a -> {mono (f a) : x y / x ⊏ y}.
theorem ltv_pbreg2l (ugt0 : 0 < u) :
  StrictMono (op u) := by
  refine Monotone.strictMono_of_injective ?h₁ ?h₂
  · exact lev_pbreg2l op u ugt0
  · refine bregvI op u ?h₂.a
    exact Ne.symm (ne_of_lt ugt0)

-- Lemma lev_pbreg2r x : r0 ⊏ x -> {mono f^~ x : x y / x ⊑ y}.
theorem lev_pbreg2r (vgt0 : 0 < v) : Monotone (op · v) := by
  -- fun u₁ u₂ uleu =>
  intro u₁ u₂ uleu
  have := pbregv_lge0 (f:=op) (u₂ - u₁) v vgt0
  simp_all only [map_sub, sub_nonneg, iff_true]
  exact sub_nonneg.mp this

-- Lemma ltv_pbreg2r x : r0 ⊏ x -> {mono f^~ x : x y / x ⊏ y}.
theorem ltv_pbreg2r (vgt0 : 0 < v) :
  StrictMono (op · v) := by
  refine Monotone.strictMono_of_injective ?h₁ ?h₂
  · exact lev_pbreg2r op v vgt0
  · refine bregIv op v ?h₂.a
    exact Ne.symm (ne_of_lt vgt0)

-- Lemma lev_nbreg2l a : a ⊏ 0 -> {mono (f a) : x y /~ x ⊑ y}.
theorem lev_nbreg2l (ult0 : u < 0) : Antitone (op u) := by
  intro v₁ v₂ vlev
  suffices h : op u v₂ - op u v₁ ≤ 0 by exact tsub_nonpos.mp h
  rw [Eq.symm (bregvBr op u v₂ v₁), ← neg_neg u, map_neg, AddMonoidHom.neg_apply]
  suffices h : 0 ≤ op (-u) (v₂ - v₁) by exact Right.neg_nonpos_iff.mpr h
  exact (pbregv_rge0 (-u) (v₂ - v₁) (Left.neg_pos_iff.mpr ult0)).mpr (sub_nonneg_of_le vlev)


  -- have : (op u) v₂ - (op u) v₁ ≤ 0 := by
  --   calc
  --     (op u) v₂ - (op u) v₁ = op u (v₂ - v₁) := Eq.symm (bregvBr op u v₂ v₁)
  --     _ = - op (-u) (v₂ - v₁) := by
  --       simp only [map_sub, map_neg, AddMonoidHom.neg_apply, sub_neg_eq_add, neg_add_rev, neg_neg]
  --       exact sub_eq_neg_add ((op u) v₂) ((op u) v₁)
  --     _ ≤ 0 := by
  --       refine Right.neg_nonpos_iff.mpr ?_
  --       have nu : 0 < -u := Left.neg_pos_iff.mpr ult0
  --       have vmv : 0 ≤ v₂ - v₁ := sub_nonneg_of_le vlev
  --       exact (pbregv_rge0 (-u) (v₂ - v₁) nu).mpr vmv
  -- exact tsub_nonpos.mp this

-- Lemma ltv_nbreg2l a : a ⊏ 0 -> {mono (f a) : x y /~ x ⊏ y}.
theorem ltv_nbreg2l (ult0 : u < 0) : StrictAnti (op u) := by
  simp only [StrictAnti]
  intro v₁ v₂ vlev
  have ople : op u v₂ ≤ op u v₁ := by
    apply lev_nbreg2l
    assumption
    exact le_of_lt vlev
  have opne : op u v₁ ≠ op u v₂ := by
    by_contra h
    let opeq :=bregvI op u (Ne.symm (ne_of_gt ult0)) h
    simp_all only [lt_self_iff_false, opeq]
  exact lt_of_le_of_ne ople (id (Ne.symm opne))


-- Lemma lev_wpbreg2l a : l0 ⊑ a -> {homo (f a) : y z / y ⊑ z}.
theorem lev_wpbreg2l (uge0 : 0 ≤ u) : ∀ v₁ v₂, v₁ ≤ v₂ ↔ op u v₁ ≤ op u v₂ := by
  intro v₁ v₂
  by_cases h : u = 0
  · simp only [h, map_zero, AddMonoidHom.zero_apply, le_refl, iff_true]
    sorry --???
  · have ugt0 : 0 < u := lt_of_le_of_ne uge0 fun a ↦ h (id (Eq.symm a))
    constructor
    · apply lev_pbreg2l op u ugt0
    · intro ople
      have : op u v₁ - op u v₁ ≤ op u v₂ - op u v₁ := by
        exact tsub_le_tsub_right ople ((op u) v₁)
      -- have fs : op u 0 = 0 := by exact bregv0r op u
      rw [Eq.symm (bregvBr op u v₂ v₁), sub_self] at this
      have : 0 ≤ v₂ - v₁ := (pbregv_rge0 u (v₂ - v₁) ugt0).mp this
      exact sub_nonneg.mp this
















end BRegVOrder


end VectorOrder
