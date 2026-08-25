module

public import SphereSixComplex.Topology.StandardSimplexSimplicialSingularComparison
public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodDeformation

/-!
# The local simplicial--singular comparison on a boundary face

The canonical adjunction unit on the standard six-simplex, followed by the singular-set map of
the inclusion into its affine face neighbourhood, induces a quasi-isomorphism on integral
chains.  The proof factors this exact canonical map into the standard-simplex comparison and the
singular-chain map of the explicit face-neighbourhood homotopy equivalence.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Simplicial

namespace SphereSixComplex

/-- The canonical simplicial map from the standard six-simplex to singular simplices in its
`i`-th affine face neighbourhood. -/
public noncomputable def boundarySevenFaceNeighborhoodLocalComparisonSSetMap
    (i : Fin 8) :
    (Δ[6] : SSet.{0}) ⟶
      TopCat.toSSet.obj (TopCat.of (boundarySevenComparisonFaceNeighborhood i)) :=
  sSetTopAdj.unit.app (Δ[6] : SSet.{0}) ≫
    TopCat.toSSet.map (boundarySevenFaceToComparisonFaceNeighborhood i)

/-- The exact canonical integral chain map on one standard face and its affine neighbourhood. -/
public noncomputable def boundarySevenFaceNeighborhoodLocalIntegralComparison
    (i : Fin 8) :
    (Δ[6] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ) ⟶
      IntegralSingularChainComplexObj
        (TopCat.of (boundarySevenComparisonFaceNeighborhood i)) :=
  SSet.chainComplexMap (boundarySevenFaceNeighborhoodLocalComparisonSSetMap i)
    (AddCommGrpCat.of ℤ)

/-- Functoriality identifies the canonical local comparison with the standard-simplex
simplicial--singular comparison followed by the singular chain map of face inclusion. -/
public theorem boundarySevenFaceNeighborhoodLocalIntegralComparison_eq
    (i : Fin 8) :
    boundarySevenFaceNeighborhoodLocalIntegralComparison i =
      simplicialToRealizationSingularChainMap
          (Δ[6] : SSet.{0}) (AddCommGrpCat.of ℤ) ≫
        boundarySevenFaceNeighborhoodIntegralSingularChainMap i := by
  change
    ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
        (sSetTopAdj.unit.app (Δ[6] : SSet.{0}) ≫
          TopCat.toSSet.map (boundarySevenFaceToComparisonFaceNeighborhood i)) =
      ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (sSetTopAdj.unit.app (Δ[6] : SSet.{0})) ≫
        ((SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).map
          (TopCat.toSSet.map (boundarySevenFaceToComparisonFaceNeighborhood i))
  exact Functor.map_comp _ _ _

/-- The canonical local integral comparison is a quasi-isomorphism. -/
public theorem boundarySevenFaceNeighborhoodLocalIntegralComparison_quasiIso
    (i : Fin 8) :
    QuasiIso (boundarySevenFaceNeighborhoodLocalIntegralComparison i) := by
  rw [boundarySevenFaceNeighborhoodLocalIntegralComparison_eq]
  let hstandard : QuasiIso
      (simplicialToRealizationSingularChainMap
        (Δ[6] : SSet.{0}) (AddCommGrpCat.of ℤ)) :=
    standardSimplex_simplicialToRealizationSingularChainMap_quasiIso 6
  let hneighborhood : QuasiIso
      (boundarySevenFaceNeighborhoodIntegralSingularChainMap i) :=
    boundarySevenFaceNeighborhoodIntegralSingularChainMap_quasiIso i
  rw [quasiIso_iff]
  intro k
  exact quasiIsoAt_comp
    (simplicialToRealizationSingularChainMap
      (Δ[6] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (boundarySevenFaceNeighborhoodIntegralSingularChainMap i) k
    (hφ := hstandard.quasiIsoAt k)
    (hφ' := hneighborhood.quasiIsoAt k)

end SphereSixComplex
