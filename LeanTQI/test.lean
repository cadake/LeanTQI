import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open scoped ENNReal

variable {m n 𝕂 : Type*}
variable [RCLike 𝕂] [Fintype m] [Fintype n]

def LpNorm (p : ℝ≥0∞) (M : Matrix m n 𝕂) : ℝ :=
  if p = ∞ then ⨆ i, ⨆ j, ‖M i j‖
  else (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal)

variable (p : ℝ≥0∞)

theorem lpnorm_tendsto_maxnorm [Fact (1 ≤ p)] (h : p = ∞) (M : Matrix m n 𝕂) :
    (∑ i, ∑ j, ‖M i j‖ ^ p.toReal) ^ (1 / p.toReal) =  ⨆ i, ⨆ j, ‖M i j‖ := sorry

theorem lpnorm_continuous_p (A : Matrix m n 𝕂) :
    ContinuousOn ((LpNorm (m := m) (n := n) (𝕂 := 𝕂) (M := A))) {p | 1 ≤ p} := by
  refine ContinuousOn.if ?hp ?hf ?hg
  · simp only [Set.setOf_eq_eq_singleton, Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
    intro p pge1 pinf
    simp only [frontier, closure_singleton, interior_singleton, Set.diff_empty,
      Set.mem_singleton_iff] at pinf
    sorry
  · sorry
  · sorry

end
