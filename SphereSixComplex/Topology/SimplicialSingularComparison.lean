module

public import SphereSixComplex.Topology.HomotopySphereHomology
public import SphereSixComplex.Topology.SimplicialSixSphereHomology
public import SphereSixComplex.Topology.SingularHomologyModTwo
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj

/-!
# The canonical simplicial-to-singular comparison

The unit of the geometric-realization/singular-set adjunction sends every simplex of a simplicial
set to the corresponding singular simplex of its realization.  Applying simplicial chains gives
the canonical comparison map.  This file packages that concrete map and proves that its
quasi-isomorphism, together with a homeomorphism `|∂Δ[7]| ≃ S⁶`, transports the already-computed
degree-two and degree-three homology vanishing to the standard topological sphere.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The canonical chain map from simplicial chains to singular chains on geometric realization. -/
public noncomputable def simplicialToRealizationSingularChainMap
    (K : SSet.{0}) (R : AddCommGrpCat) :
    K.chainComplex R ⟶
      (TopCat.toSSet.obj (SSet.toTop.obj K)).chainComplex R :=
  SSet.chainComplexMap (sSetTopAdj.unit.app K) R

/-- The precise general comparison theorem needed here. -/
public def SimplicialToSingularComparisonQuasiIsomorphism
    (K : SSet.{0}) (R : AddCommGrpCat) : Prop :=
  QuasiIso (simplicialToRealizationSingularChainMap K R)

/-- A quasi-isomorphic comparison transports vanishing from simplicial homology to singular
homology of the realization. -/
public theorem realizationSingularHomology_isZero_of_simplicial
    (K : SSet.{0}) (R : AddCommGrpCat) (k : ℕ)
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism K R)
    (hsimplicial : IsZero ((K.chainComplex R).homology k)) :
    IsZero (((TopCat.toSSet.obj (SSet.toTop.obj K)).chainComplex R).homology k) := by
  let _ : QuasiIso (simplicialToRealizationSingularChainMap K R) := hcomparison
  exact hsimplicial.of_iso
    (isoOfQuasiIsoAt (simplicialToRealizationSingularChainMap K R) k).symm

/-- The geometric identification of the realization of the boundary of the seven-simplex with
the project's standard six-sphere. -/
public def BoundarySevenRealizationHomeomorphSixSphere : Prop :=
  Nonempty ((SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ SixSphere)

/-- The two exact comparison inputs, isolated from the finite cone calculation. -/
public def BoundarySevenComparisonInputs (R : AddCommGrpCat) : Prop :=
  SimplicialToSingularComparisonQuasiIsomorphism (∂Δ[7] : SSet.{0}) R ∧
    BoundarySevenRealizationHomeomorphSixSphere

/-- The boundary comparison inputs imply degree-three singular homology vanishing for `S⁶`. -/
public theorem sixSphere_singularHomology_three_isZero_of_boundaryComparison
    (R : AddCommGrpCat) (h : BoundarySevenComparisonInputs R) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj R).obj
      (TopCat.of SixSphere)) := by
  obtain ⟨hcomparison, ⟨e⟩⟩ := h
  have hrealization :
      IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj R).obj
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))) :=
    realizationSingularHomology_isZero_of_simplicial
      (∂Δ[7] : SSet.{0}) R 3 hcomparison
        (boundarySeven_simplicialHomology_three_isZero R)
  exact hrealization.of_iso
    (((singularHomologyFunctor AddCommGrpCat 3).obj R).mapIso
      (TopCat.isoOfHomeo e.symm))

/-- Likewise, the comparison inputs imply degree-two singular homology vanishing for `S⁶`. -/
public theorem sixSphere_singularHomology_two_isZero_of_boundaryComparison
    (R : AddCommGrpCat) (h : BoundarySevenComparisonInputs R) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj R).obj
      (TopCat.of SixSphere)) := by
  obtain ⟨hcomparison, ⟨e⟩⟩ := h
  have hrealization :
      IsZero (((singularHomologyFunctor AddCommGrpCat 2).obj R).obj
        (SSet.toTop.obj (∂Δ[7] : SSet.{0}))) :=
    realizationSingularHomology_isZero_of_simplicial
      (∂Δ[7] : SSet.{0}) R 2 hcomparison
        (boundarySeven_simplicialHomology_two_isZero R)
  exact hrealization.of_iso
    (((singularHomologyFunctor AddCommGrpCat 2).obj R).mapIso
      (TopCat.isoOfHomeo e.symm))

/-- The comparison theorem over `𝔽₂` supplies exactly the standard-sphere Kervaire input. -/
public theorem sixSphere_modTwoHomology_three_isZero_of_boundaryComparison
    (h : BoundarySevenComparisonInputs (AddCommGrpCat.of (ZMod 2))) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of SixSphere)) :=
  sixSphere_singularHomology_three_isZero_of_boundaryComparison
    (AddCommGrpCat.of (ZMod 2)) h

/-- It is enough to prove the simplicial-to-singular comparison with integral coefficients:
degree-two and degree-three integral vanishing pass to mod-two degree-three homology through the
proved coefficient Bockstein sequence. -/
public theorem sixSphere_modTwoHomology_three_isZero_of_integralBoundaryComparison
    (h : BoundarySevenComparisonInputs (AddCommGrpCat.of ℤ)) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of SixSphere)) := by
  apply modTwoSingularHomologyThree_isZero (TopCat.of SixSphere)
  · exact sixSphere_singularHomology_three_isZero_of_boundaryComparison
      (AddCommGrpCat.of ℤ) h
  · exact sixSphere_singularHomology_two_isZero_of_boundaryComparison
      (AddCommGrpCat.of ℤ) h

/-- Consequently, the same two comparison inputs give the middle-dimensional mod-two vanishing
for every marked smooth homotopy six-sphere. -/
public theorem markedHomotopySixSphere_modTwoHomology_three_isZero_of_boundaryComparison
    (h : BoundarySevenComparisonInputs (AddCommGrpCat.of (ZMod 2)))
    (S : OrientedMarkedSmoothHomotopySixSphere) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier)) :=
  markedHomotopySixSphere_modTwoHomology_three_isZero_of_standard
    (sixSphere_modTwoHomology_three_isZero_of_boundaryComparison h) S

/-- The integral comparison inputs therefore also suffice for every marked homotopy sphere. -/
public theorem
    markedHomotopySixSphere_modTwoHomology_three_isZero_of_integralBoundaryComparison
    (h : BoundarySevenComparisonInputs (AddCommGrpCat.of ℤ))
    (S : OrientedMarkedSmoothHomotopySixSphere) :
    IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier)) :=
  markedHomotopySixSphere_modTwoHomology_three_isZero_of_standard
    (sixSphere_modTwoHomology_three_isZero_of_integralBoundaryComparison h) S

end SphereSixComplex
