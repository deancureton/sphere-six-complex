module

public import SphereSixComplex.Prerequisites.Topology.SimplicialSingularComparison
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Simplicial--singular comparison for a standard simplex

The realization of a standard simplex is contractible.  Both its simplicial chains and its
singular chains therefore have zero positive-degree homology, while degree-zero homology is the
coefficient group.  The canonical adjunction unit respects the degree-zero augmentations, so its
chain map is a quasi-isomorphism in every degree.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- In a nonnegatively graded chain complex, degree-zero chains are canonically the degree-zero
cycles, since the outgoing differential vanishes. -/
public noncomputable def chainComplexXZeroIsoCyclesZero
    (K : ChainComplex AddCommGrpCat ℕ) : K.X 0 ≅ K.cycles 0 where
  hom := K.liftCycles (𝟙 _) 0 (by simp) (by simp)
  inv := K.iCycles 0
  hom_inv_id := by simp
  inv_hom_id := by
    rw [← cancel_mono (K.iCycles 0)]
    simp


/-- Every standard simplex is connected as a simplicial set. -/
public theorem standardSimplex_isConnected (n : ℕ) :
    (SSet.stdSimplex.obj (SimplexCategory.mk n)).IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        let i := SSet.stdSimplex.obj₀Equiv x
        let j := SSet.stdSimplex.obj₀Equiv y
        rcases le_total i j with hij | hji
        · let s := SSet.stdSimplex.edge n i j hij
          have hs : SSet.π₀.mk x = SSet.π₀.mk y := by
            have hsrc : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 1 s = x := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            have htgt : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 0 s = y := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            simpa only [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
          exact hs
        · let s := SSet.stdSimplex.edge n j i hji
          have hs : SSet.π₀.mk y = SSet.π₀.mk x := by
            have hsrc : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 1 s = y := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            have htgt : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 0 s = x := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            simpa only [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
          exact hs.symm
  · exact ⟨SSet.stdSimplex.const n 0 _⟩

/-- The geometric realization of every standard simplex is contractible. -/
public theorem standardSimplexRealization_contractibleSpace (n : ℕ) :
    ContractibleSpace
      (SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk n)) : Type) := by
  letI : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨stdSimplex.vertex (0 : Fin (n + 1)),
        (stdSimplex.vertex (0 : Fin (n + 1))).2⟩
  exact (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).contractibleSpace





end SphereSixComplex
