module

public import SphereSixComplex.Paper.Topology.HomologyComputation
public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# A concrete degree-one chain model from Section 7

Lemma 7.19 presents the first homology of the punctured glued space using the generators
`(c, g₁, g₂)` and the first two columns below.  The final gluing attaches the class
`(0, -1, -1)`, which is the third column.  Thus the degree-two to degree-one boundary in this
finite cellular model is the displayed `3 × 3` matrix.

This file constructs that finite chain complex and proves its exactness in degrees one and two by
an explicit integral inverse.  It then gives the direct singular-homology consequence of a chain
map whose homology map is an isomorphism in either degree.

Constructing that comparison from the paper's cover remains topological rather than algebraic:
Mathlib currently has no singular-chain excision theorem, singular Mayer--Vietoris chain
comparison, cellular-homology theorem, relative-cell/singular-chain comparison, or Lefschetz
duality theorem for manifolds with boundary.  Consequently the degreewise comparison proof is a
theorem parameter here, rather than an asserted property of the glued space.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Matrix

namespace SphereSixComplex

/-- The two punctured-space relations and the final attachment class, as boundary columns. -/
public def sectionSevenFirstBoundaryMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-37, 1, 12;
      3, 0, -1;
      0, 4, -1]

/-- An integral inverse to `sectionSevenFirstBoundaryMatrix`. -/
public def sectionSevenFirstBoundaryInverse : Matrix (Fin 3) (Fin 3) ℤ :=
  !![-4, -49, 1;
     -3, -37, 1;
     -12, -148, 3]


public theorem sectionSevenFirstBoundary_left_inverse :
    sectionSevenFirstBoundaryInverse * sectionSevenFirstBoundaryMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sectionSevenFirstBoundaryInverse, sectionSevenFirstBoundaryMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]

public theorem sectionSevenFirstBoundary_right_inverse :
    sectionSevenFirstBoundaryMatrix * sectionSevenFirstBoundaryInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sectionSevenFirstBoundaryInverse, sectionSevenFirstBoundaryMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ]



/-- The Section 7 degree-one boundary is an isomorphism of underlying abelian groups. -/
public theorem sectionSevenFirstBoundary_bijective :
    Function.Bijective sectionSevenFirstBoundaryMatrix.mulVec := by
  constructor
  · intro x y hxy
    have h := congrArg sectionSevenFirstBoundaryInverse.mulVec hxy
    simpa [Matrix.mulVec_mulVec, sectionSevenFirstBoundary_left_inverse] using h
  · intro y
    refine ⟨sectionSevenFirstBoundaryInverse.mulVec y, ?_⟩
    simp [Matrix.mulVec_mulVec, sectionSevenFirstBoundary_right_inverse]

/-- The additive homomorphism represented by the Section 7 degree-one boundary matrix. -/
public def sectionSevenFirstBoundaryHom : (Fin 3 → ℤ) →+ (Fin 3 → ℤ) :=
  (Matrix.mulVecLin sectionSevenFirstBoundaryMatrix).toAddHom









end SphereSixComplex
