-- import LeanCopilot
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

-- set_option profiler true
-- set_option profiler.threshold 50

namespace Matrix

variable {m n l R 𝕂 : Type*}
variable {α β γ : Type*}
variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]
variable [RCLike 𝕂]

open RCLike
open scoped ComplexOrder
open ComplexConjugate

section ConjugateAdjointMatrix

variable (M N : Matrix m n α )

section Star

variable [Star α]

def conjugate (M : Matrix m n α) : Matrix m n α :=
  M.map star

postfix:1024 "^*" => conjugate

-- def conjTranspose [Star α] (M : Matrix m n α ) : Matrix n m α :=
--   M.transpose.map star

@[simp]
theorem conjugate_eq_map_star :
  M^* = M.map star := rfl

@[simp]
theorem adjoint_eq_trans_map_star :
  Mᴴ = (Mᵀ)^* := rfl

@[simp]
theorem conjugate_element (i j) :
  M^* i j = star (M i j) := rfl

-- same with : conjTranspose_apply
@[simp]
theorem adjoint_element (i j) :
  Mᴴ j i = star (M i j) := rfl

end Star

-- why [Add α] and [Star α] should be canceled here?
@[simp]
theorem conjugate_add [AddMonoid α] [StarAddMonoid α] (M N : Matrix m n α) :
  (M + N)^* = M^* + N^* := by
  ext
  simp

@[simp]
theorem conjugate_smul [Star α] [Star β] [SMul β α] [StarModule β α] (s : β) (M : Matrix m n α ) :
  (s • M)^* = (star s) • (M^*) := by
  ext
  simp

@[simp]
theorem conjugate_smul_add [Star β] [SMul β α] [AddMonoid α] [StarAddMonoid α] [StarModule β α] (s : β) (M N : Matrix m n α ) :
  (s • (M + N))^* = (star s) • (M^* + N^*) := by
  calc
    (s • (M + N))^* = (star s) • (M + N)^* := by
      exact conjugate_smul s (M + N)
    _ = (star s) • (M^* + N^*) := by
      rw [conjugate_add M N]

@[simp]
theorem conjugate_zero [AddMonoid α] [StarAddMonoid α] : conjugate (0 : Matrix m n α) = 0 := by
  simp only [conjugate_eq_map_star, star_zero, Matrix.map_zero]


-- ??? it's not true when α is not mul_comm
@[simp]
theorem conjmxM [Fintype n] [NonUnitalSemiring α] [StarRing α] (M : Matrix m n α) (N : Matrix n l α ) :
  (M * N)^* = M^* * N^* := by
  sorry
  -- ext i j
  -- simp [map, mul_apply]
  -- congr
  -- ext k


section InvolutiveStar

variable [InvolutiveStar α]

-- conjmxK
@[simp]
theorem conjugate_conjugate :
  (M^*)^* = M := by
  simp [conjugate_eq_map_star, map, Function.comp_apply]
  exact rfl

open Function

-- todo: simplify
theorem conjugate_injective :
  Injective (conjugate : (Matrix m n α ) → (Matrix m n α )) := by
  intro m1 m2 heq
  ext i j
  simp only [conjugate, map, EmbeddingLike.apply_eq_iff_eq] at heq
  let f := fun i => fun j => star (m1 i j)
  let g := fun i => fun j => star (m2 i j)
  have feqg : f = g := by assumption
  have : f i j = g i j := by
    have : f i = g i := by
      apply funext_iff.mp
      assumption
    apply funext_iff.mp
    assumption
  simp only [star_inj, f, g] at this
  exact this

end InvolutiveStar

-- todo : why [Zero (Matrix m n α )] should be canceled here
-- note : duplicate class instance causes errors, such as Zero, Star ...
@[simp]
theorem conjugate_eq_zero [AddMonoid α] [StarAddMonoid α] (M : Matrix m n α) :
  M^* = 0 ↔ M = 0 := by
  constructor
  case mpr =>
    intro h
    simp only [conjugate_eq_map_star, star_zero, Matrix.map_zero, h]
  case mp =>
    intro h
    have : (0 : Matrix m n α)^* = 0 := by
      apply conjugate_zero
    apply conjugate_injective
    rw [h, this]


-- todo
-- theorem det_conj
theorem conjugate_det [Star α] [CommRing α] (M : Matrix n n α) :
  det M^* = star (det M) := by
  simp only [conjugate_eq_map_star, det]
  sorry


@[simp]
theorem conjugate_diagonal [AddMonoid α] [StarAddMonoid α] (a : α) :
  (diagonal (fun _ => a) : Matrix m m α)^* = diagonal (fun _ => (star a)) := by
  ext i j
  simp [diagonal]
  by_cases h : i = j <;> simp [h]


@[simp]
theorem conjugate_one [Semiring α] [StarRing α] :
  (1 : Matrix m m α)^* = 1 := by
  ext i j
  by_cases h : i = j <;> simp [h, one_apply]

@[simps]
def conjugateAddMonoidHom [AddMonoid α] [StarAddMonoid α] : Matrix m n α →+ Matrix m n α where
  toFun := conjugate
  map_zero' := conjugate_zero
  map_add' m n := conjugate_add m n

@[simps]
def conjugateAntiLinearMap [CommSemiring R] [StarRing R] [AddCommMonoid α] [Module R α] [StarAddMonoid α] [StarModule R α] : Matrix m n α →ₗ⋆[R] Matrix m n α :=
  {conjugateAddMonoidHom with map_smul' := conjugate_smul}

-- adjmxTC
@[simp]
theorem conjTranspose_transpose_conjugate [Star α] (M : Matrix m n α) :
  Mᴴ = (Mᵀ)^* := by
  simp only [adjoint_eq_trans_map_star, conjugate_eq_map_star]

-- adjmxCT
@[simp]
theorem conjTranspose_conjugate_tranpose [Star α] (M : Matrix m n α) :
  Mᴴ = (M^*)ᵀ := by
  ext i j
  simp

-- adjmxD
-- conjTranspose_add

-- adjmxZ
-- conjTranspose_smul

-- adjmxP
@[simp]
theorem conjTranspose_smul_add [Star β] [SMul β α] [AddMonoid α] [StarAddMonoid α] [StarModule β α] (s : β) (M N : Matrix m n α) : (s • (M + N))ᴴ = (star s) • (Mᴴ + Nᴴ) := by
  ext i j
  simp only [conjTranspose_apply, smul_apply, add_apply, star_smul, star_add,
    adjoint_eq_trans_map_star, conjugate_eq_map_star, map_apply, transpose_apply]

-- adjmxM
-- conjTranspose_mul

-- adjmxK
-- conjTranspose_conjTranspose

-- adjmxi_inj
-- conjTranspose_injective

-- adjmx_eq0
-- conjTranspose_eq_zero

-- todo : det_adj

-- adjmx_scale
-- diagonal_conjTranspose


-- adjmx1
-- conjTranspose_one


-- todo delta matrix
-- conjmx_delta
-- adjmx_delta


-- trmxCA
@[simp]
theorem transpose_conjugate_conjTranspose [InvolutiveStar α] (M : Matrix m n α) :
  Mᵀ = (M^*)ᴴ := by
  ext
  simp

-- trmxAC
@[simp]
theorem transpose_conjTranspose_conjugate [InvolutiveStar α] (M : Matrix m n α) :
  Mᵀ = (Mᴴ)^* := by
  rw [conjTranspose_transpose_conjugate, conjugate_conjugate]


-- conjmxAT : conj M = trans (adj M)
@[simp]
theorem conjugate_conjTranspose_transpose [InvolutiveStar α] (M : Matrix m n α) :
  M^* = (Mᴴ)ᵀ := by
  rw [transpose_conjTranspose_conjugate, conjTranspose_conjTranspose]

-- - conjmxTA : conj M = adj (trans M)
@[simp]
theorem conjugate_transpose_conjTranspose [InvolutiveStar α] (M : Matrix m n α) :
  M^* = (Mᵀ)ᴴ := by
  rw [transpose_conjugate_conjTranspose, conjTranspose_conjTranspose]

-- - mxCAC : adj (conj M) = conj (adj M)
-- - mxACC : conj (adj M) = adj (conj M)
@[simp]
theorem conjugate_conjTranspose_comm [InvolutiveStar α] (M : Matrix m n α) :
  (M^*)ᴴ = (Mᴴ)^* := by
  rw [conjugate_transpose_conjTranspose, conjTranspose_conjTranspose, ← transpose_conjTranspose_conjugate]


-- - mxATC : trans (adj M) = adj (trans M)
-- - mxTAC : adj (trans M) = trans (adj M)
@[simp]
theorem conjTranspose_transpose_comm [InvolutiveStar α] (M : Matrix m n α) :
  (Mᴴ)ᵀ = (Mᵀ)ᴴ := by
  rw [← conjugate_transpose_conjTranspose, ← conjugate_conjTranspose_transpose]


-- - mxCTC : trans (conj M) = conj (trans M)
-- - mxTCC : conj (trans M) = trans (conj M)
@[simp]
theorem conjugate_transpose_comm [InvolutiveStar α] (M : Matrix m n α) :
  (M^*)ᵀ = (Mᵀ)^* := by
  rw [← conjTranspose_transpose_conjugate, ← conjTranspose_conjugate_tranpose]


variable [AddCommMonoid α]


-- - mxtrace_adj : trace (adj M) = (trace M)^*
-- trace_conjTranspose


-- - mxtrace_conj : trace (conj M) = (trace M)^*
@[simp]
theorem trace_conjugate [StarAddMonoid α] (M : Matrix m m α) :
  trace M^* = star (trace M) := by
  simp only [trace, conjugate_eq_map_star, diag_apply, map_apply, star_sum]

-- todo
-- - adj_row : adj (ith row of M) = ith col of adj M

-- todo
-- - adj_col : adj (ith col of M) = ith row of adj M


-- - mxrank_adj : rank (adj M) = rank M
-- rank_conjTranspose


-- todo
-- - adjmx_castV : castmx (eqS : (n = n') * (m = m')) (adjmx A) = adjmx (castmx (eqS.2, eqS.1) A)
-- - trmx_castV : castmx (eqS : (n = n') * (m = m')) (A^T) = trans (castmx (eqS.2, eqS.1) A)


end ConjugateAdjointMatrix


section MatrixPredicate

variable [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]


section RCLikeMatrix

variable (M : Matrix m n 𝕂)

-- def IsEntryReal : Prop := ∀ i j, M i j = (re (M i j) : 𝕂)
def IsEntryReal : Prop := ∀ i j, M i j = conj (M i j)


-- theorem IsEntryReal.ext_iff :
--   M.IsEntryReal ↔ ∀ i j, M i j = (re (M i j) : 𝕂) := by rfl
theorem IsEntryReal.ext_iff :
  M.IsEntryReal ↔ ∀ i j, M i j = conj (M i j) := by rfl

def IsEntryPos : Prop := ∀ i j, M i j > 0

theorem IsEntryPos.ext_iff :
  M.IsEntryPos ↔ ∀ i j, M i j > 0 := by rfl

def IsEntryNonneg : Prop := ∀ i j, M i j ≥ 0

theorem IsEntryNonneg.ext_iff :
  M.IsEntryNonneg ↔ ∀ i j, M i j ≥ 0 := by rfl

def IsEntryUint : Prop := ∀ i j, M i j ≤ 1 ∧ M i j ≥ 0

theorem IsEntryUint.ext_iff :
  M.IsEntryUint ↔ ∀ i j, M i j ≤ 1 ∧ M i j ≥ 0 := by rfl

def IsEntryBool : Prop := ∀ i j, M i j = 0 ∨ M i j = 1

theorem IsEntryBool.ext_iff :
  M.IsEntryBool ↔ ∀ i j, M i j = 0 ∨ M i j = 1 := by rfl

end RCLikeMatrix

section SquareMatrix

variable (M : Matrix n n 𝕂) (hM : M.IsHermitian)

-- def IsHermitian (A : Matrix n n α) : Prop := Aᴴ = A

-- def IsSymm (A : Matrix n n α) : Prop :=
--   Aᵀ = A

-- def IsDiag [Zero α] (A : Matrix n n α) : Prop :=
--   Pairwise fun i j => A i j = 0

-- def PosSemidef (M : Matrix n n R) :=
--   M.IsHermitian ∧ ∀ x : n → R, 0 ≤ dotProduct (star x) (M *ᵥ x)

theorem PosSemidef.ext_iff (M : Matrix n n R) :
  M.PosSemidef ↔ M.IsHermitian ∧ ∀ x : n → R, 0 ≤ dotProduct (star x) (M *ᵥ x) := by
  rfl


-- def PosDef (M : Matrix n n R) :=
--   M.IsHermitian ∧ ∀ x : n → R, x ≠ 0 → 0 < dotProduct (star x) (M *ᵥ x)

def IsNormal : Prop := M * Mᴴ = Mᴴ * M

theorem IsNormal.ext_iff :
  M.IsNormal ↔ M * Mᴴ = Mᴴ * M := by rfl

def IsUnitary (M : Matrix n n R) : Prop := M ∈ Matrix.unitaryGroup n R

theorem IsUnitary.ext_iff (M : Matrix n n R) :
  M.IsUnitary ↔ M ∈ Matrix.unitaryGroup n R := by rfl

theorem IsUnitary.ext_iff' (M : Matrix n n R) :
  M.IsUnitary ↔ Mᴴ * M = 1 ∧ M * Mᴴ = 1 := by
  rw [IsUnitary, unitaryGroup]
  exact unitary.mem_iff

-- todo: unitmx

def IsDensity : Prop := PosSemidef M ∧ trace M ≤ 1

theorem IsDensity.ext_iff :
  M.IsDensity ↔ M.PosSemidef ∧ trace M ≤ 1 := by rfl

def IsDensityTraceOne : Prop := PosSemidef M ∧ trace M = 1

theorem IsDensityTraceOne.ext_iff :
  M.IsDensityTraceOne ↔ M.PosSemidef ∧ trace M = 1 := by rfl

noncomputable abbrev spectral_diag : Matrix n n 𝕂 := diagonal (RCLike.ofReal ∘ hM.eigenvalues)

-- todo
def IsObservable : Prop := (spectral_diag M hM).IsEntryUint

theorem IsObservable.ext_iff :
  M.IsObservable hM ↔ (spectral_diag M hM).IsEntryUint := by rfl

-- todo
def IsProjector : Prop := (spectral_diag M hM).IsEntryBool

theorem IsProjector.ext_iff :
  M.IsProjector hM ↔ (spectral_diag M hM).IsEntryBool := by rfl

def IsProjectorOne : Prop := M.IsProjector hM ∧ rank M = 1

theorem IsProjectorOne.ext_iff :
  M.IsProjectorOne hM ↔ M.IsProjector hM ∧ rank M = 1 := by rfl

end SquareMatrix


section RealMatrix


-- realmx_real_det
-- theorem det_real (M : Matrix n n 𝕂) (h : IsEntryReal M) :
--   det M = (re (det M) : 𝕂) := by
--   sorry
theorem det_real (M : Matrix n n 𝕂) (h : IsEntryReal M) :
  det M = conj (det M) := by
  sorry

-- todo
-- realmx_real_cofactor


--realmx_real_adj
-- theorem conjTranspose_real_real (M : Matrix m n 𝕂) (h : IsEntryReal M) : IsEntryReal Mᴴ := by
--   apply ext_iff.mpr
--   simp only [conjTranspose, map]
--   ext i j
--   simp [h]
--   rw [h j i]
--   simp
theorem conjTranspose_real_real (M : Matrix m n 𝕂) (h : IsEntryReal M) : IsEntryReal Mᴴ := by
  apply ext_iff.mpr
  ext i j
  simp only [conjTranspose_apply, star_def, RingHomCompTriple.comp_apply, RingHom.id_apply]
  exact (h j i).symm


end RealMatrix


end MatrixPredicate


section MatrixPredicateHierarchy

-- def isReal (k : 𝕂) : Prop := ((re k) : 𝕂) = k
def isReal (k : 𝕂) : Prop := conj k = k

theorem RCLike.nonneg_real (z : 𝕂) : 0 ≤ z → isReal z := by
  intro zge0
  let g := nonneg_iff.mp zge0
  apply RCLike.ext_iff.mpr
  simp only [conj_re, conj_im, true_and, g.right]
  exact neg_zero

--todo:simplify
theorem nonneg_is_real (M : Matrix m n 𝕂) (h : IsEntryNonneg M) :
  IsEntryReal M := by
  apply ext_iff.mpr
  ext i j
  have mge0 : 0 ≤ M i j := h i j
  have : 0 ≤ re (M i j) ∧ im (M i j) = 0 := by
    apply nonneg_iff.mp
    exact mge0
  apply RCLike.ext_iff.mpr
  simp only [conj_re, conj_im, true_and, this.right]
  exact zero_eq_neg.mpr rfl

theorem positive_is_nonneg (M : Matrix m n 𝕂) (h : IsEntryPos M) : IsEntryNonneg M := by
  refine (IsEntryNonneg.ext_iff M).mpr ?_
  intro i j
  exact le_of_lt (h i j)

theorem uint_is_nonneg (M : Matrix m n 𝕂) (h : IsEntryUint M) : IsEntryNonneg M := by
  refine (IsEntryNonneg.ext_iff M).mpr ?_
  intro i j
  exact (h i j).right

theorem bool_is_uint (M : Matrix m n 𝕂) (h : IsEntryBool M) : IsEntryUint M := by
  refine (IsEntryUint.ext_iff M).mpr ?_
  intro i j
  rcases h i j <;> simp [*]

-- todo:simplify
theorem positive_is_real (M : Matrix m n 𝕂) (h : IsEntryPos M) : IsEntryReal M :=
  nonneg_is_real M (positive_is_nonneg M h)

theorem uint_is_real (M : Matrix m n 𝕂) (h : IsEntryUint M) : IsEntryReal M :=
  nonneg_is_real M (uint_is_nonneg M h)

theorem bool_is_real (M : Matrix m n 𝕂) (h : IsEntryBool M) : IsEntryReal M :=
  uint_is_real M (bool_is_uint M h)

theorem bool_is_nneg (M : Matrix m n 𝕂) (h : IsEntryBool M) : IsEntryNonneg M :=
  uint_is_nonneg M (bool_is_uint M h)


-- diagmx_symm
-- #check Matrix.IsDiag.isSymm

variable (M : Matrix n n 𝕂) (N : Matrix n n 𝕂)

open Matrix.UnitaryGroup

-- unitarymx_normal
theorem unitary_is_normal (h : IsUnitary M) : IsNormal M := by
  apply (IsNormal.ext_iff M).mpr
  let p := (IsUnitary.ext_iff' M).mp h
  rw [p.left, p.right]

-- diagmx_conj
theorem diag_conjTranspose_diag (h : IsDiag M) : IsDiag Mᴴ := by
  exact IsDiag.conjTranspose h

-- diagmx_mulC
theorem diag_mul_diag_comm (h₁ : IsDiag M) (h₂ : IsDiag N) :
  M * N = N * M := by
  let diag₁ := diag M
  let diag₂ := diag N
  have meqd : diagonal diag₁ = M := IsDiag.diagonal_diag h₁
  have neqd : diagonal diag₂ = N := IsDiag.diagonal_diag h₂
  rw [← meqd, ← neqd]
  simp only [diagonal_mul_diagonal]
  ext i j
  simp only [diagonal, of_apply]
  by_cases h : i = j <;> simp only [h, ↓reduceIte]
  rw [mul_comm]


-- diagmx_normal
theorem diag_is_normal (h : IsDiag M) : IsNormal M := by
  apply (IsNormal.ext_iff M).mpr
  have h' : IsDiag Mᴴ := by exact diag_conjTranspose_diag M h
  exact diag_mul_diag_comm M Mᴴ h h'


-- hermmx_normal
theorem hermitian_is_normal (h : IsHermitian M) : IsNormal M := by
  apply (IsNormal.ext_iff M).mpr
  rw [IsHermitian.eq]
  assumption

-- psdmx_herm
theorem posSemidef_is_hermitian (h : PosSemidef M) : IsHermitian M := by
  exact PosSemidef.isHermitian h

-- pdmx_psdmx
theorem posDef_is_hermitian (h : PosDef M) : IsHermitian M := by
  exact PosDef.isHermitian h

variable (hM : IsHermitian M)

-- obsmx_psd
theorem observable_is_posSemidef (p : IsObservable M hM) : PosSemidef M := by
  refine (PosSemidef.ext_iff M).mpr ?_
  constructor
  · exact hM
  · simp only [IsObservable] at p
    intro x
    sorry

-- projmx_obs
theorem projector_is_observable (h : IsProjector M hM) : IsObservable M hM := by
  refine (IsObservable.ext_iff M hM).mpr ?_
  simp only [IsProjector] at h
  exact bool_is_uint (M.spectral_diag hM) h

-- proj1mx_proj
theorem projectorone_is_projector (h : IsProjectorOne M hM) : IsProjector M hM := by
  simp only [IsProjectorOne] at h
  exact h.left


-- trace_spectral_diag
theorem trace_spectral_diag (nM : IsNormal M) : trace M = trace (spectral_diag M hM) := by
  simp only [spectral_diag]
  sorry

@[simp]
abbrev diag_mx [Zero R] (M : Matrix n n R) : Matrix n n R := diagonal (diag M)

-- diag_mx_real
theorem real_diag_real (rM : M.IsEntryReal) : (diag_mx M).IsEntryReal := by
  simp only [IsEntryReal, diag_mx, diagonal, diag_apply, of_apply] at *
  intro i j
  by_cases h : i = j <;> simp [h]
  exact rM j j

-- diag_mx_nneg
theorem nonneg_diag_nonneg (nnM : M.IsEntryNonneg) : (diag_mx M).IsEntryNonneg := by
  simp only [IsEntryNonneg, ge_iff_le, diag_mx, diagonal, diag_apply, of_apply] at *
  intro i j
  by_cases h : i = j <;> simp [h]
  exact nnM j j


-- denmx_obs
theorem density_is_observable (dM : M.IsDensity) : IsObservable M hM := by
  simp only [IsDensity, IsObservable] at *
  sorry


-- den1mx_den
theorem densityone_is_density (doM : M.IsDensityTraceOne) : M.IsDensity := by
  simp only [IsDensityTraceOne, IsDensity] at *
  constructor
  · exact doM.left
  · exact le_of_eq doM.right

-- denmx_psd
theorem density_is_posSemidef (dM : M.IsDensity) :
  M.PosSemidef := by
  exact dM.left

-- normalmx_rank
theorem rank_spectral_diag (nM : M.IsNormal) :
  rank M = rank (spectral_diag M hM) := by
  convert IsHermitian.rank_eq_rank_diagonal hM
  simp only [spectral_diag, rank_diagonal, Function.comp_apply, ne_eq, map_eq_zero, Fintype.card_subtype_compl]

-- rank11 todo:simply
theorem rank_one_one (A : Matrix (Fin 1) (Fin 1) 𝕂) : rank A = Bool.toNat (A 0 0 != 0) := by
  have d : A = diagonal (diag A) := by
    simp only [diagonal, diag]
    ext i j
    have ieq0 : i = 0 := Fin.fin_one_eq_zero i
    have jeq0 : j = 0 := Fin.fin_one_eq_zero j
    simp only [ieq0, Fin.isValue, jeq0, of_apply, ↓reduceIte]
  rw [d]
  convert rank_diagonal (diag A); simp only [Fin.isValue, diagonal_apply_eq, diag_apply, ne_eq,
    Fintype.card_subtype_compl, Fintype.card_ofSubsingleton]
  by_cases h : A 0 0 = 0
  · simp only [Fin.isValue, h, bne_self_eq_false, Bool.toNat_false]
    have : Fintype.card {x // A x x = 0} = 1 := by
      convert Fintype.card_unique
      refine uniqueOfSubsingleton ?convert_2.a
      exact @Subtype.mk (Fin 1) (fun x => A x x = 0) 0 h
    rw [this]
  · have : Fintype.card {x // A x x = 0} = 0 := by
      convert Fintype.card_eq_zero
      refine { false := ?convert_3.false }
      intro hh
      let hh' := hh.val
      have ij0 : ∀ i j, A i j = 0 → i = 0 ∧ j = 0 := by
        intro i j _
        have ieq0 : i = 0 := Fin.fin_one_eq_zero i
        have jeq0 : j = 0 := Fin.fin_one_eq_zero j
        constructor <;> assumption
      have sdfds : A hh' hh' = 0 := by
        let dsf := hh.property
        assumption
      have : A 0 0 = 0 := by
        let sdfas := ij0 hh' hh' sdfds
        rw [sdfas.left] at sdfds
        assumption
      exact h this
    rw [this]
    simpa only [Fin.isValue, tsub_zero, Bool.toNat_eq_one, bne_iff_ne, ne_eq]


-- rank_diagmx
theorem rank_diag_mx : rank (diag_mx M) = Fintype.card {i // (diag M i) ≠ 0} := by
  exact rank_diagonal M.diag

theorem sum_nat_eq0 {I : Type*} [DecidableEq I] (s : Finset I) (F : I → ℕ) :
  ∑ i ∈ s, F i = 0 → ∀ x ∈ s, F x = 0 := by
  intro sum0 x xs
  let s' := s \ {x}
  have sumof2 : ∑ i ∈ s, F i = F x + ∑ i ∈ s', F i := by
    exact Finset.sum_eq_add_sum_diff_singleton xs F
  rw [sum0] at sumof2
  exact Nat.eq_zero_of_add_eq_zero_right (id (Eq.symm sumof2))

-- sum_nat_eq1
theorem sum_nat_eq1 {I : Type*} [DecidableEq I] (s : Finset I) (F : I → ℕ) :
  ∑ i ∈ s, F i = 1 → ∃ i ∈ s, ∀ j ∈ s, F j = Bool.toNat (i == j) := by
  intro seq1
  have exnz : ∃ i ∈ s, F i ≠ 0 := by
    by_contra! allz
    have sum0 : ∑ i ∈ s, F i = 0 := by
      exact Finset.sum_eq_zero allz
    rw [seq1] at sum0
    contradiction
  rcases exnz with ⟨x, xs, fxnez⟩
  let s' := s \ {x}
  have xs' : s = s' ∪ {x} := by
    refine Eq.symm (Finset.sdiff_union_of_subset ?h)
    exact Finset.singleton_subset_iff.mpr xs
  have sumof2 : ∑ i ∈ s, F i = F x + ∑ i ∈ s', F i := by
    exact Finset.sum_eq_add_sum_diff_singleton xs F
  have sum2ge0 : ∑ i ∈ s', F i ≥ 0 := by
    exact Nat.zero_le (∑ i ∈ s', F i)
  have fxeq1_and_sum2eq0 : F x = 1 ∧ ∑ i ∈ s', F i = 0 := by
    rw [seq1] at sumof2
    have : F x = 0 ∧ (∑ i ∈ s', F i = 1) ∨ F x = 1 ∧ (∑ i ∈ s', F i = 0) := (@Nat.add_eq_one_iff (F x) (∑ i ∈ s', F i)).mp sumof2.symm
    rcases this with h1 | h2
    have fxeq0 : F x = 0 := h1.left
    contradiction
    assumption
  use x
  constructor
  · assumption
  intro y ys
  by_cases h : y = x
  · simp only [h, beq_self_eq_true, Bool.toNat_true]
    exact fxeq1_and_sum2eq0.left
  · symm
    calc
      (x == y).toNat = false.toNat := by
        simp only [Bool.toNat_false, Bool.toNat_eq_zero, beq_eq_false_iff_ne, ne_eq]
        exact fun a ↦ h (id (Eq.symm a))
      _ = 0 := by exact rfl
    symm
    have ys' : y ∈ s' := by
      refine Finset.mem_sdiff.mpr ?_
      constructor
      · assumption
      exact Finset.not_mem_singleton.mpr h
    apply sum_nat_eq0 s' F fxeq1_and_sum2eq0.right
    assumption



-- proj1mx_diagP
-- todo


-- proj1mx_den1
theorem projectorone_is_densityone (poM : IsProjectorOne M hM) :
  IsDensityTraceOne M := by
  simp only [IsProjectorOne, IsDensityTraceOne, IsProjector, PosSemidef] at *
  constructor
  · constructor
    · assumption
    · sorry
  · sorry

end MatrixPredicateHierarchy

section ExtraTheory

variable (M : Matrix n n 𝕂)
variable (hM : M.IsHermitian)

-- mx_dot_diag
theorem vecMul_diagonal_dotProduct [CommMonoid 𝕂] (dM : IsDiag M) (v : n → 𝕂) :
  star v ⬝ᵥ M *ᵥ v = ∑ i : n, M i i * ‖(v i)‖^2 := by
  let diagM := diag M
  have MeqD : M = diagonal diagM := Eq.symm (IsDiag.diagonal_diag dM)
  simp only [MeqD, dotProduct, mulVec, diagonal, of_apply, Pi.star_apply, RCLike.star_def, ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]
  congr
  ext i
  calc
    (starRingEnd 𝕂) (v i) * (diagM i * v i) = (diagM i * (v i)) * ((starRingEnd 𝕂) (v i)) := by
      exact DivisionCommMonoid.mul_comm ((starRingEnd 𝕂) (v i)) (diagM i * (v i))
    _ = diagM i * (v i * (starRingEnd 𝕂) (v i)) := by
      exact mul_assoc (diagM i) (v i) ((starRingEnd 𝕂) (v i))
  congr
  exact RCLike.mul_conj (v i)

-- theorem vecMul_diagonal_dotProduct_trace [CommMonoid 𝕂] (dM : IsDiag M) (v : n → 𝕂) :
--   trace ![![v ᵥ* M ⬝ᵥ v]] = ∑ i : n, M i i * (v i)^2 := by
--   rw [vecMul_diagonal_mulVec]
--   simp only [trace, Nat.succ_eq_add_one, Nat.reduceAdd, Finset.univ_unique, Fin.default_eq_zero,
--     Fin.isValue, diag_apply, cons_val', cons_val_fin_one, empty_val', Finset.sum_const,
--     Finset.card_singleton, one_smul]
--   assumption

-- mx_dot_diag_mx???
-- todo

theorem has_non_zero_elem [Zero α] (M : Matrix m n α) :
  M ≠ 0 → ∃ i j, M i j ≠ 0 := by
  intro Mne0
  by_contra! h'
  have : M = 0 := ext h'
  contradiction

-- #check vecMul_zero
-- mx_dot_eq0
theorem vecMul_dotProduct_always_zero_iff :
  (∀ v : n → 𝕂, star v ⬝ᵥ M *ᵥ v = 0) ↔ M = 0 := by
  sorry

open IsHermitian
-- hermmx_dot
theorem vecMul_dotProduct_always_real_iff :
  (∀ v : n → 𝕂, star v ⬝ᵥ M *ᵥ v = (RCLike.re (star v ⬝ᵥ M *ᵥ v) : 𝕂)) ↔ M.IsHermitian := by
  sorry

-- psdmx_dot
theorem vecMul_dotProduct_always_nonneg_iff :
  (∀ v : n → 𝕂, star v ⬝ᵥ M *ᵥ v ≥ 0) ↔ M.PosSemidef := by
  sorry

-- #check Matrix
-- psdmx_bimap_closed_gen
theorem posSemidef_bimap_closed (A : Matrix m n 𝕂) :
  M.PosSemidef → PosSemidef (A * M * Aᴴ) := by
  rw [← vecMul_dotProduct_always_nonneg_iff, ← vecMul_dotProduct_always_nonneg_iff]
  intro h v
  calc
    star v ⬝ᵥ (A * M * Aᴴ) *ᵥ v = star v ⬝ᵥ (A * M) *ᵥ (Aᴴ *ᵥ v) := by
      rw [← mulVec_mulVec]
    _ = star v ⬝ᵥ A *ᵥ M *ᵥ (Aᴴ *ᵥ v) := by
      rw [← mulVec_mulVec]
    _ = (star v ᵥ* A) ⬝ᵥ M *ᵥ (Aᴴ *ᵥ v) := by
      exact dotProduct_mulVec (star v) A (M *ᵥ Aᴴ *ᵥ v)
    _ = star (Aᴴ *ᵥ v) ⬝ᵥ M *ᵥ (Aᴴ *ᵥ v) := by
      nth_rw 1 [← conjTranspose_conjTranspose A]
      rw [← star_mulVec]
    _ ≥ 0 := by
      exact h (Aᴴ *ᵥ v)


-- #check IsHermitian
-- #check mul_nonneg
-- diagmx_nnegmx_psd
theorem diagmx_nonneg_posSemidef [PosMulMono 𝕂] :
  M.IsEntryNonneg → M.diag_mx.PosSemidef := by
  intro nnM
  rw [diag_mx]
  let dM := diagonal M.diag
  change dM.PosSemidef
  have nndM : dM.IsEntryNonneg := nonneg_diag_nonneg M nnM
  apply (vecMul_dotProduct_always_nonneg_iff dM).mp
  intro v
  rw [vecMul_diagonal_dotProduct]
  change 0 ≤ ∑ i : n, dM i i * ‖v i‖ ^ 2
  have : ∀ i : n, 0 ≤ dM i i * ‖v i‖ ^ 2 := by
    intro i
    apply mul_nonneg
    let tt:=(IsEntryNonneg.ext_iff dM).mp nndM i i
    exact ge_iff_le.mp tt
    rw [pow_two]
    apply mul_nonneg <;> refine RCLike.ofReal_nonneg.mpr ?hb.ha.a; exact norm_nonneg (v i)
  exact Fintype.sum_nonneg this
  exact isDiag_diagonal M.diag

-- obsmx_psd_eq
theorem observable_posSemidef_iff :
  M.IsObservable hM ↔ M.PosSemidef ∧ (1 - M).PosSemidef := by
  sorry

-- obsmx_dot
theorem observable_dot_iff :
  M.IsObservable hM ↔ ∀ v : n → 𝕂, 0 ≤ star v ⬝ᵥ M *ᵥ v ∧ star v ⬝ᵥ M *ᵥ v ≤ v ⬝ᵥ star v := by
  rw [observable_posSemidef_iff, ← vecMul_dotProduct_always_nonneg_iff, ← vecMul_dotProduct_always_nonneg_iff]
  constructor <;> intro h
  · intro v
    constructor
    · exact h.left v
    · have : v ⬝ᵥ star v - star v ⬝ᵥ M *ᵥ v ≥ 0 := by
        calc
          v ⬝ᵥ star v - star v ⬝ᵥ M *ᵥ v = star v ⬝ᵥ (1 - M) *ᵥ v := by
            have : star v ⬝ᵥ v = star v ⬝ᵥ 1 *ᵥ v := by
              simp only [one_mulVec]
            rw [dotProduct_comm, this, ← dotProduct_sub, ← sub_mulVec]
          _ ≥ 0 := h.right v
      exact sub_nonneg.mp this
  · constructor <;> intro v
    · exact (h v).left
    · have : star v ⬝ᵥ M *ᵥ v ≤ v ⬝ᵥ star v := (h v).right
      rw [sub_mulVec, one_mulVec, dotProduct_sub]
      nth_rw 1 [dotProduct_comm]
      exact sub_nonneg_of_le this




-- hermmx0
-- #check isHermitian_zero

-- psdmx0
-- #check PosSemidef.zero

-- psdmx_eq0
theorem posSemidef_zero_iff :
  M.PosSemidef ∧ (-M).PosSemidef → M = 0 := by
  rintro ⟨psdM, psdM'⟩
  rw [← vecMul_dotProduct_always_nonneg_iff M] at psdM
  rw [← vecMul_dotProduct_always_nonneg_iff (-M)] at psdM'
  apply (vecMul_dotProduct_always_zero_iff M).mp
  intro v
  have : star v ⬝ᵥ M *ᵥ v ≥ 0 := psdM v
  have : - (star v ⬝ᵥ M *ᵥ v) ≥ 0 := by
    calc
      - (star v ⬝ᵥ M *ᵥ v) = star v ⬝ᵥ -M *ᵥ v := by
        simp_all only [ge_iff_le]
        rw [neg_mulVec, dotProduct_neg]
      _ ≥ 0 := psdM' v
  simp_all only [ge_iff_le, Left.nonneg_neg_iff]
  exact le_antisymm this (psdM v)


-- psdmx_tr
theorem posSemidef_transpose_iff :
  M.PosSemidef ↔ PosSemidef Mᵀ := by
  constructor <;> intro h
  exact PosSemidef.transpose h
  have g : (Mᵀ)ᵀ.PosSemidef := PosSemidef.transpose h
  simp only [transpose_transpose] at g
  exact g

-- obsmx_tr
theorem observable_transpose_iff :
  M.IsObservable hM ↔ Mᵀ.IsObservable ((isHermitian_transpose_iff M).mpr hM) := by
  rw [observable_posSemidef_iff, observable_posSemidef_iff,
  posSemidef_transpose_iff, posSemidef_transpose_iff (1-M),
  transpose_sub, transpose_one]

-- denmx_tr
theorem density_transpose_iff :
  M.IsDensity ↔ IsDensity Mᵀ := by
  rw [IsDensity, IsDensity, posSemidef_transpose_iff, trace_transpose]

-- psdmx_adj
-- #check PosSemidef.conjTranspose
theorem posSemidef_conjTranspose_iff :
  M.PosSemidef ↔ PosSemidef Mᴴ := by
  constructor <;> intro h
  · exact PosSemidef.conjTranspose h
  · have : Mᴴᴴ.PosSemidef := PosSemidef.conjTranspose h
    simp only [conjTranspose_conjTranspose] at this
    assumption

-- obsmx_adj
theorem observable_conjTranspose_iff :
  M.IsObservable hM ↔ Mᴴ.IsObservable ((isHermitian_conjTranspose_iff M).mpr hM) := by
  rw [observable_posSemidef_iff, observable_posSemidef_iff,
  posSemidef_conjTranspose_iff, posSemidef_conjTranspose_iff]
  have : (1 - M).PosSemidef ↔ (1 - Mᴴ).PosSemidef := by
    calc
      (1 - M).PosSemidef ↔ (1 - M)ᴴ.PosSemidef := by
        exact posSemidef_conjTranspose_iff (1 - M)
      _ ↔ (1 - Mᴴ).PosSemidef := by
        have : (1 - M)ᴴ = (1 - Mᴴ) := by
          rw [conjTranspose_sub, conjTranspose_one]
        rw [this]
  rw [this]

-- #check star_le_star_iff
-- #check star_one
-- denmx_adj
theorem density_conjTranspose_iff :
  M.IsDensity ↔ Mᴴ.IsDensity := by
  -- simp only [IsDensity]
  rw [IsDensity, IsDensity, posSemidef_conjTranspose_iff, trace_conjTranspose]
  have : M.trace ≤ 1 ↔ star M.trace ≤ 1 := by
    rw [← star_le_star_iff]
    nth_rw 2 [← star_one]
  rw [this]


-- psdmx_conj
theorem posSemidef_conjugate_iff :
  M.PosSemidef ↔ PosSemidef M^* := by
  rw [conjugate_conjTranspose_transpose, posSemidef_conjTranspose_iff, posSemidef_transpose_iff]

theorem isHermitian_conjugate_iff :
  M.IsHermitian ↔ M^*.IsHermitian := by
  simp only [IsHermitian, conjTranspose_conjugate_tranpose, conjugate_conjugate]
  constructor <;> intro h
  · nth_rw 1 [← h]
    rw [transpose_transpose]
  · rw [conjugate_transpose_comm, h, conjugate_conjugate]

-- obsmx_conj
theorem observable_conjugate_iff :
  M.IsObservable hM ↔ M^*.IsObservable ((isHermitian_conjugate_iff M).mp hM) := by
  simp only [conjugate_conjTranspose_transpose]
  rw [observable_transpose_iff, observable_conjTranspose_iff]
  simp only [conjTranspose_transpose_conjugate, transpose_transpose, conjugate_transpose_comm]

-- denmx_conj
theorem density_conjugate_iff :
  M.IsDensity ↔ M^*.IsDensity := by
  rw [conjugate_conjTranspose_transpose, density_conjTranspose_iff, density_transpose_iff]

-- mxtraceE
-- #check trace.eq_1

end ExtraTheory


section ExtraMxPredClosed
-- #check Subgroup

def MxOperatorClosed (op : Matrix m n 𝕂 → Matrix m n 𝕂 → Matrix m n 𝕂)
  (p : Matrix m n 𝕂 → Prop) : Prop :=
  ∀ A B : Matrix m n 𝕂, p A ∧ p B → p (op A B)

variable (p : Matrix n n 𝕂 → Prop)
variable (q : Matrix n n 𝕂 → Prop)

def MxMulClosed : Prop :=
  ∀ A B, p A ∧ p B → p (A * B)

def MxBimapClosed : Prop :=
  ∀ A B, p A ∧ p B → p (A * B * Aᴴ)

def MxBipredClosed : Prop :=
  ∀ A B, p A ∧ q A ∧ p B ∧ q B → q (A * B * Aᴴ)

def MxUnitaryClosed : Prop :=
  MxBipredClosed (IsUnitary) p


-- hermmx_zmod_closed
-- todo

-- psdmx_add
theorem psdmxaddclosed :
  MxOperatorClosed (· + ·) (PosSemidef (n:=n) (R:=𝕂)) := by
  simp only [MxOperatorClosed]
  rintro A B ⟨psdA, psdB⟩
  apply (vecMul_dotProduct_always_nonneg_iff (A + B)).mp
  intro v
  rw [add_mulVec, dotProduct_add]
  exact Left.add_nonneg ((vecMul_dotProduct_always_nonneg_iff A).mpr psdA v) ((vecMul_dotProduct_always_nonneg_iff B).mpr psdB v)


-- psdmx_addr_closed
-- todo

-- unitmx_mulmx_closed
-- todo

-- unitarymx_mulmx_closed


-- todo


end ExtraMxPredClosed





end Matrix
