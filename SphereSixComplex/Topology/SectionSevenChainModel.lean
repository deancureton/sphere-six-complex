module

public import SphereSixComplex.Topology.HomologyComputation
public import SphereSixComplex.Topology.MayerVietoris
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

@[simp]
public theorem sectionSevenFirstBoundaryMatrix_det :
    sectionSevenFirstBoundaryMatrix.det = -1 := by
  rw [Matrix.det_fin_three]
  change (-1 : ℤ) = -1
  rfl

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

/-- The first two columns are exactly the punctured-space presentation already extracted from
Lemma 7.19. -/
public theorem sectionSevenFirstBoundary_on_relations (y : Fin 2 → ℤ) :
    sectionSevenFirstBoundaryMatrix.mulVec ![y 0, y 1, 0] =
      firstHomologyRelationMatrix.mulVec y := by
  funext i
  fin_cases i <;>
    simp [sectionSevenFirstBoundaryMatrix, firstHomologyRelationMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The last basis vector has boundary equal to the paper's final attachment class. -/
@[simp]
public theorem sectionSevenFirstBoundary_on_attachment :
    sectionSevenFirstBoundaryMatrix.mulVec ![0, 0, 1] = ![12, -1, -1] := by
  funext i
  fin_cases i <;>
    norm_num [sectionSevenFirstBoundaryMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

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

/-- The finite chain complex `0 → ℤ³ → ℤ³ → ℤ → 0` carrying the explicit
degree-one Section 7 calculation. -/
public def sectionSevenDegreeOneCellularComplex : ChainComplex AddCommGrpCat ℕ :=
  ChainComplex.mk (AddCommGrpCat.of ℤ) (AddCommGrpCat.of (Fin 3 → ℤ))
    (AddCommGrpCat.of (Fin 3 → ℤ)) 0
    (AddCommGrpCat.ofHom sectionSevenFirstBoundaryHom) (by simp)
    (fun _ ↦ ⟨AddCommGrpCat.of (Fin 0 → ℤ), 0, by simp⟩)

/-- The explicit Section 7 cellular model is exact at degree one. -/
public theorem sectionSevenDegreeOneCellularComplex_exactAt_one :
    sectionSevenDegreeOneCellularComplex.ExactAt 1 := by
  let S := sectionSevenDegreeOneCellularComplex.sc' 2 1 0
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact sectionSevenFirstBoundaryHom (0 : (Fin 3 → ℤ) →+ ℤ)
    intro y
    constructor
    · intro _
      refine ⟨sectionSevenFirstBoundaryInverse.mulVec y, ?_⟩
      change sectionSevenFirstBoundaryMatrix.mulVec
        (sectionSevenFirstBoundaryInverse.mulVec y) = y
      rw [Matrix.mulVec_mulVec, sectionSevenFirstBoundary_right_inverse, Matrix.one_mulVec]
    · rintro ⟨z, rfl⟩
      simp
  rw [sectionSevenDegreeOneCellularComplex.exactAt_iff]
  apply ShortComplex.exact_of_iso
    (sectionSevenDegreeOneCellularComplex.isoSc' 2 1 0
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 2 1 (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 1 0 (by omega)))).symm
  exact hS

/-- The first homology object of the explicit finite model is zero. -/
public theorem sectionSevenDegreeOneCellularComplex_homology_one_isZero :
    IsZero (sectionSevenDegreeOneCellularComplex.homology 1) :=
  sectionSevenDegreeOneCellularComplex_exactAt_one.isZero_homology

/-- The explicit Section 7 cellular model is exact at degree two as well. -/
public theorem sectionSevenDegreeOneCellularComplex_exactAt_two :
    sectionSevenDegreeOneCellularComplex.ExactAt 2 := by
  let S := sectionSevenDegreeOneCellularComplex.sc' 3 2 1
  have hS : S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact]
    change Function.Exact
      (0 : (Fin 0 → ℤ) →+ (Fin 3 → ℤ)) sectionSevenFirstBoundaryHom
    intro y
    constructor
    · intro hy
      have hy0 : y = 0 := by
        apply sectionSevenFirstBoundary_bijective.injective
        change sectionSevenFirstBoundaryMatrix.mulVec y = 0 at hy
        simpa using hy
      refine ⟨0, ?_⟩
      simp [hy0]
    · rintro ⟨z, rfl⟩
      simp
  rw [sectionSevenDegreeOneCellularComplex.exactAt_iff]
  apply ShortComplex.exact_of_iso
    (sectionSevenDegreeOneCellularComplex.isoSc' 3 2 1
      ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 3 2 (by omega)))
      ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 2 1 (by omega)))).symm
  exact hS

/-- The second homology object of the explicit finite model is zero. -/
public theorem sectionSevenDegreeOneCellularComplex_homology_two_isZero :
    IsZero (sectionSevenDegreeOneCellularComplex.homology 2) :=
  sectionSevenDegreeOneCellularComplex_exactAt_two.isZero_homology

/-- A cellular-to-singular chain map inducing an isomorphism in degree one proves vanishing of
actual integral singular homology in that degree. -/
public theorem integralSingularHomology_one_subsingleton_of_sectionSevenCellularComparison
    {X : Type} [TopologicalSpace X]
    (f : sectionSevenDegreeOneCellularComplex ⟶ IntegralSingularChainComplex X)
    [IsIso (sectionSevenDegreeOneCellularComplex.homologyMap f 1)] :
    Subsingleton (IntegralSingularHomology 1 X) := by
  have hSingular : IsZero ((IntegralSingularChainComplex X).homology 1) :=
    IsZero.of_iso sectionSevenDegreeOneCellularComplex_homology_one_isZero
      (asIso (sectionSevenDegreeOneCellularComplex.homologyMap f 1)).symm
  exact AddCommGrpCat.subsingleton_of_isZero hSingular

/-- A cellular-to-singular chain map inducing an isomorphism in degree two proves vanishing of
actual integral singular homology in that degree. -/
public theorem integralSingularHomology_two_subsingleton_of_sectionSevenCellularComparison
    {X : Type} [TopologicalSpace X]
    (f : sectionSevenDegreeOneCellularComplex ⟶ IntegralSingularChainComplex X)
    [IsIso (sectionSevenDegreeOneCellularComplex.homologyMap f 2)] :
    Subsingleton (IntegralSingularHomology 2 X) := by
  have hSingular : IsZero ((IntegralSingularChainComplex X).homology 2) :=
    IsZero.of_iso sectionSevenDegreeOneCellularComplex_homology_two_isZero
      (asIso (sectionSevenDegreeOneCellularComplex.homologyMap f 2)).symm
  exact AddCommGrpCat.subsingleton_of_isZero hSingular

/-- The same chain comparison realizes the degree-one part of the Section 7 computed homology
groups. -/
public noncomputable def integralSingularHomologyOneEquivSectionSevenComputed
    {X : Type} [TopologicalSpace X]
    (f : sectionSevenDegreeOneCellularComplex ⟶ IntegralSingularChainComplex X)
    [IsIso (sectionSevenDegreeOneCellularComplex.homologyMap f 1)] :
    IntegralSingularHomology 1 X ≃+ SectionSevenComputedHomology 1 := by
  let _ : Subsingleton (IntegralSingularHomology 1 X) :=
    integralSingularHomology_one_subsingleton_of_sectionSevenCellularComparison f
  let _ : Unique (IntegralSingularHomology 1 X) := uniqueOfSubsingleton 0
  let _ : Subsingleton (SectionSevenComputedHomology 1) :=
    sectionSevenComputedHomology_middle_subsingleton 1 (by omega) (by omega)
  let _ : Unique (SectionSevenComputedHomology 1) := uniqueOfSubsingleton 0
  exact AddEquiv.ofUnique

end SphereSixComplex
