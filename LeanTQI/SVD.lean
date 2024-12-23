import Mathlib

namespace LinearMap

variable {E F 𝕂 : Type*} [RCLike 𝕂]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕂 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕂 F]
  [FiniteDimensional 𝕂 E] [FiniteDimensional 𝕂 F]

variable (T : E →ₗ[𝕂] F)
variable {n m : ℕ} (hn : Module.finrank 𝕂 E = n) (hm : Module.finrank 𝕂 F = m)

open LinearMap
#check Matrix.IsHermitian.rank_eq_card_non_zero_eigs
#check LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply
@[simp]
noncomputable def AdjMulSelf : E →ₗ[𝕂] E := (adjoint T) ∘ₗ T

@[simp]
noncomputable def SelfMulAdj : F →ₗ[𝕂] F := T ∘ₗ (adjoint T)

theorem adj_mul_self_isSelfAdj : IsSelfAdjoint T.AdjMulSelf := by
  simp only [IsSelfAdjoint, star, AdjMulSelf, adjoint_comp, adjoint_adjoint]

theorem self_mul_adj_isSelfAdj : IsSelfAdjoint T.SelfMulAdj := by
  simp only [IsSelfAdjoint, star, SelfMulAdj, adjoint_comp, adjoint_adjoint]

theorem adj_mul_self_isSymm : IsSymmetric T.AdjMulSelf := by
  simp only [AdjMulSelf]
  exact (isSymmetric_iff_isSelfAdjoint T.AdjMulSelf).2 (adj_mul_self_isSelfAdj T)

theorem self_mul_adj_isSymm : IsSymmetric T.SelfMulAdj := by
  simp only [SelfMulAdj]
  exact (isSymmetric_iff_isSelfAdjoint T.SelfMulAdj).2 (self_mul_adj_isSelfAdj T)

@[simp]
noncomputable def sSingularValues' : Fin n → ℝ :=
  fun i => √((IsSymmetric.eigenvalues (adj_mul_self_isSymm T) hn) i)

-- def FinReverse : Fin n → Fin n := fun i =>
--   if n = 0 then (Fin.mk 0 (show 0 < n by exact Fin.pos i))
--   else (Fin.mk (n - 1 - i) (Nat.sub_one_sub_lt i.isLt))

-- theorem antitone_finreverse : Antitone (FinReverse (n:=n)) := by
--   dsimp [Antitone, FinReverse]
--   intro a b hab
--   by_cases hn : n = 0
--   · simp only [if_pos hn, le_refl]
--   simp only [if_neg hn, @sub_le_sub_iff_left, Fin.mk_le_mk, Nat.sub_sub]
--   exact Nat.sub_le_sub_left (Nat.add_le_add_left hab 1) n

-- @[simp]
-- noncomputable def sSingularValues : Fin n → ℝ :=
--   ((sSingularValues' T hn) ∘ (Tuple.sort (sSingularValues' T hn))) ∘ (FinReverse (n:=n))

noncomputable def DecPerm : (Fin n) ≃ (Fin n) where
  toFun := (Tuple.sort (sSingularValues' T hn)) ∘ (Fin.revPerm)
  invFun := (Fin.revPerm) ∘ (Tuple.sort (sSingularValues' T hn)).invFun
  left_inv := by
    simp only [Function.LeftInverse, Equiv.invFun_as_coe, Function.comp_apply, Fin.revPerm_apply,
      Equiv.symm_apply_apply, Fin.rev_rev, implies_true]
  right_inv := by
    simp only [Function.RightInverse, Function.LeftInverse]
    intro i
    simp only [Equiv.invFun_as_coe, Function.comp_apply, Fin.revPerm_apply, Fin.rev_rev,
      Equiv.apply_symm_apply]

@[simp]
noncomputable def sSingularValues : Fin n → ℝ :=
  (sSingularValues' T hn) ∘ ((Tuple.sort (sSingularValues' T hn)) ∘ (Fin.revPerm))

local notation "svdσ" T => sSingularValues T hn

@[simp]
noncomputable def mSingularValues' : Fin m → ℝ :=
  fun i => √((IsSymmetric.eigenvalues (self_mul_adj_isSymm T) hm) i)

@[simp]
noncomputable def mSingularValues : Fin m → ℝ :=
  (mSingularValues' T hm) ∘ ((Tuple.sort (mSingularValues' T hm)) ∘ (Fin.revPerm))

theorem singular_values_nonneg (i : Fin n) : 0 ≤ (svdσ T) i := by
  simp only [sSingularValues, Function.comp_apply, Fin.revPerm_apply, sSingularValues', AdjMulSelf,
    Real.sqrt_nonneg]

theorem antitone_singular_values : Antitone (svdσ T) := by
  rw [sSingularValues, ← Function.comp_assoc]
  apply Monotone.comp_antitone
  apply Tuple.monotone_sort
  intro a b hab
  simp only [Fin.revPerm_apply, Fin.rev_le_rev]
  assumption

-- todo: rank of (adjoint A) * A equals rank of A
example : Cardinal.toNat T.AdjMulSelf.rank = Cardinal.toNat T.rank := by
  sorry

example (T : E →ₗ[𝕂] E) : Cardinal.toNat T.rank = Fintype.card {i // (Module.End.Eigenvalues.val T) i ≠ 0} := by
  sorry

theorem rank_eq_card_nonzero_sigs : Cardinal.toNat T.rank =
    Fintype.card {i // (svdσ T) i ≠ 0} := by
  sorry

theorem sigs_pos_before_rank (i : Fin n) (hi : i < Cardinal.toNat T.rank) : 0 < (svdσ T) i := by
  by_contra! g
  have hσi : (svdσ T) i = 0 := le_antisymm g (singular_values_nonneg T hn i)
  have hij' : ∀ j, i ≤ j → (svdσ T) j = 0 := by
    intro j hij
    have : (svdσ T) i ≥ (svdσ T) j := antitone_singular_values T hn hij
    rw [hσi] at this
    exact le_antisymm this (singular_values_nonneg T hn j)
  have h₁ : Fintype.card {i // (svdσ T) i = 0} = Fintype.card (Fin n) - Fintype.card {i // (svdσ T) i ≠ 0} := by
      simp_rw [← @Fintype.card_subtype_compl, ne_eq, Decidable.not_not]
  have h₂ : Fintype.card { j // i ≤ j } ≤ Fintype.card { j // (svdσ T) j = 0} := by
      exact Fintype.card_subtype_mono (LE.le i) (fun x ↦ (svdσ T) x = 0) hij'
  rw [h₁, ← rank_eq_card_nonzero_sigs] at h₂
  have h₃ : Fintype.card { j // i ≤ j } > Fintype.card (Fin n) - Cardinal.toNat T.rank := by
    have : Fintype.card { j // i ≤ j } = Fintype.card (Fin n) - i := by
      have : Fintype.card { j // j < i } = i := Fintype.card_fin_lt_of_le Fin.is_le'
      simp_rw [← this, ← @Fintype.card_subtype_compl, not_lt]
    rw [this, Fintype.card_fin]
    exact Nat.sub_lt_sub_left (i.isLt) hi
  have h₄ : Fintype.card (Fin n) - Cardinal.toNat T.rank < Fintype.card (Fin n) - Cardinal.toNat T.rank := by
    exact Nat.lt_of_lt_of_le h₃ h₂
  rw [lt_self_iff_false] at h₄
  exact h₄

theorem sigs_zero_after_rank (i : Fin n) (hi : i ≥ Cardinal.toNat T.rank) : (svdσ T) i = 0 := by
  by_contra! g
  have hσi : (svdσ T) i > 0 :=
    lt_of_le_of_ne ((singular_values_nonneg T hn i)) (_root_.id (Ne.symm g))
  have hij' : ∀ j, j ≤ i → (svdσ T) j > 0 :=
    fun j hij => gt_of_ge_of_gt (antitone_singular_values T hn hij) hσi
  have hij'' : ∀ j, j ≤ i → (svdσ T) j ≠ 0 := by
    intro j hj
    exact Ne.symm (ne_of_lt (hij' j hj))
  have h₁ : Fintype.card {i // (svdσ T) i ≠ 0} = Fintype.card (Fin n) - Fintype.card {i // (svdσ T) i = 0} := by
    simp_rw [← @Fintype.card_subtype_compl]
  have h₂ : Fintype.card { j // j ≤ i } ≤ Fintype.card { j // (svdσ T) j ≠ 0} := by
    exact Fintype.card_subtype_mono (fun x ↦ x ≤ i) (fun x ↦ (svdσ T) x ≠ 0) hij''
  rw [h₁] at h₂
  have h₃ : Fintype.card { j // j ≤ i } > Cardinal.toNat T.rank := by
    have : Fintype.card { j // j ≤ i } = i + 1 := by
      have : Fintype.card { j // j < i } = i := Fintype.card_fin_lt_of_le Fin.is_le'
      have : Fintype.card { j // j ≤ i } = Fintype.card { j // j < (Fin.mk (n:=n) (i.val + 1) (by sorry))} := by
        sorry
      simp_rw [this]
      apply Fintype.card_fin_lt_of_le Fin.is_le'
    rw [this]
    exact Order.lt_add_one_iff.mpr hi
  have h₄ : Cardinal.toNat T.rank < Fintype.card (Fin n) - Fintype.card { i // (svdσ T) i = 0 } := by
    exact Nat.lt_of_lt_of_le h₃ h₂
  rw [← h₁, rank_eq_card_nonzero_sigs T hn, lt_self_iff_false] at h₄
  exact h₄


#check Orthonormal
#check LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis
#check LinearMap.IsSymmetric.apply_eigenvectorBasis

@[simp]
noncomputable def RightSingularVectors' : OrthonormalBasis (Fin n) 𝕂 E :=
  LinearMap.IsSymmetric.eigenvectorBasis (T := T.AdjMulSelf) (adj_mul_self_isSymm T) hn

@[simp]
noncomputable def RightSingularVectors : (Fin n) → E :=
  (RightSingularVectors' T hn).toBasis ∘ ((Tuple.sort (sSingularValues' T hn)) ∘ (Fin.revPerm))

local notation "svdV" T => RightSingularVectors T hn

theorem adjmulself_eigenvalues_nonneg (i : Fin n) : 0 ≤ (adj_mul_self_isSymm T).eigenvalues hn i := by
  let μ := (adj_mul_self_isSymm T).eigenvalues hn i
  have hμ : Module.End.HasEigenvalue T.AdjMulSelf μ := by
    exact IsSymmetric.hasEigenvalue_eigenvalues (adj_mul_self_isSymm T) hn i
  apply eigenvalue_nonneg_of_nonneg hμ
  intro v
  rw [AdjMulSelf, coe_comp, Function.comp_apply, @adjoint_inner_right, @inner_self_eq_norm_mul_norm]
  exact mul_nonneg (norm_nonneg (T v)) (norm_nonneg (T v))

theorem adjmulself_eigvec_eq_sig_square_smul_eigvec (i : Fin n) : (T.AdjMulSelf) ((svdV T) i) =
    ((svdσ T) i ^ 2 : 𝕂) • (svdV T) i := by
  simp only [AdjMulSelf, RightSingularVectors, RightSingularVectors', OrthonormalBasis.coe_toBasis,
    Function.comp_apply, Fin.revPerm_apply, IsSymmetric.apply_eigenvectorBasis, sSingularValues,
    sSingularValues', map_pow]
  norm_cast
  have : ((1 / 2) * (2 : ℝ) = 1) := by linarith
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_mul, this, Real.rpow_one]
  exact adjmulself_eigenvalues_nonneg T hn ((Tuple.sort (T.sSingularValues' hn)) i.rev)

#check Matrix.PosSemidef.eigenvalues_nonneg
#check Matrix.IsHermitian.rank_eq_card_non_zero_eigs
#check toMatrix

theorem orthonormal_right_singular_vectors : Orthonormal 𝕂 (svdV T) := by
  rw [RightSingularVectors]
  refine Orthonormal.comp ?_ (⇑(Tuple.sort (T.sSingularValues' hn)) ∘ ⇑Fin.revPerm) ?_
  apply OrthonormalBasis.orthonormal
  simp only [Function.Injective, Function.comp_apply, Fin.revPerm_apply,
    EmbeddingLike.apply_eq_iff_eq, Fin.rev_inj, imp_self, implies_true]

-- todo: rank of a linearmap equals nums of nonzero eigenvalues
example (T : E →ₗ[𝕂] E) (hT : T.IsSymmetric) : Cardinal.toNat T.rank =
    (Matrix.diagonal (hT.eigenvalues hn)).rank := by
  dsimp [rank]
  rw [← Submodule.finrank_eq_rank]
  sorry

-- todo: rank of a linearmap equals nums of nonzero singularvalues
example : Cardinal.toNat T.rank = (Matrix.diagonal (svdσ T)).rank := by
  simp only [sSingularValues]
  sorry


noncomputable def LeftSingularVectors' : OrthonormalBasis (Fin m) 𝕂 F :=
  LinearMap.IsSymmetric.eigenvectorBasis (T := T.SelfMulAdj) (self_mul_adj_isSymm T) hm

noncomputable def LeftSingularVectors : (Fin m) → F :=
  (LeftSingularVectors' T hm).toBasis ∘ ((Tuple.sort (mSingularValues' T hm)) ∘ (Fin.revPerm))

local notation "svdU" T => LeftSingularVectors T hm

theorem orthonormal_left_singular_vectors : Orthonormal 𝕂 (svdU T) := by
  rw [LeftSingularVectors]
  refine Orthonormal.comp ?_ (⇑(Tuple.sort (T.mSingularValues' hm)) ∘ ⇑Fin.revPerm) ?_
  apply OrthonormalBasis.orthonormal
  simp only [Function.Injective, Function.comp_apply, Fin.revPerm_apply,
    EmbeddingLike.apply_eq_iff_eq, Fin.rev_inj, imp_self, implies_true]

open scoped InnerProductSpace


#check svdσ T
#check hn

#check Isometry
theorem singular_value_decomposition (T : E →ₗ[𝕂] F) :
    ∃ (r : ℕ) (σ : Fin r → ℝ) (hσ : Antitone σ) (hσ' : ∀ i, 0 ≤ σ i) (V : Fin r → E) (W : Fin r → F)
    (hv : Orthonormal 𝕂 V) (hw : Orthonormal 𝕂 W),
    ∀ (v : E), T v = ∑ (i : Fin r), ((σ i) * ⟪v,  (V i)⟫_𝕂) • (W i) := by
  let re := Cardinal.toNat (Module.rank 𝕂 E)
  let rf := Cardinal.toNat (Module.rank 𝕂 F)
  have hre : Module.finrank 𝕂 E = re := rfl
  have hrf : Module.finrank 𝕂 F = rf := rfl
  let σ := (sSingularValues T (n:=re) hre)
  let r := Cardinal.toNat T.rank
  -- let σ' := fun (i : Fin (min r r')) => σ i
  -- have hσ : Antitone σ := antitone_singular_values T hr
  -- have hσ' : ∀ i, 0 ≤ σ i := fun i ↦ singular_values_nonneg T hr i
  -- let V := (RightSingularVectors T hr)
  -- let W := (LeftSingularVectors T hr')
  -- use Nat.min r r'
  sorry

end LinearMap
