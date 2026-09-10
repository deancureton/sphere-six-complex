module
public import SphereSixComplex.Paper.Topology.PaperEllipticBoundaryTraceTransport
public import SphereSixComplex.Paper.Topology.PaperGeometricCentralCore

@[expose] public section
noncomputable section
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex SphereSixComplex.Topology SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

public theorem regularCoordinate_isQuotientCoveringMap :
    letI := A.regularBaseDeckAction
    IsQuotientCoveringMap A.regularCoordinate Delta := by
  let _ := A.regularBaseDeckAction
  let hp := regularBaseQuotientMap_isQuotientCoveringMap
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact hp.homeomorph_comp A.puncturedBaseHomeomorphTwicePuncturedComplex

public theorem regularFamilyOuterDeck_eq_of_coordinate_class_eq
    (e : RegularTotalSpace A.periods)
    (a b : FundamentalGroup A.CentralFamily (regularFamilyQuotientMap A.periods e))
    (h : FundamentalGroup.map
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ _ a =
      FundamentalGroup.map
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ _ b) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ a =
      hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ b := by
  let _ := regularFamilyDeckAction A.periods
  let _ := A.regularBaseDeckAction
  let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  let hq := A.regularCoordinate_isQuotientCoveringMap
  let D : QuotientCoverMapData
      (G := Delta) (H := Delta) (regularFamilyQuotientMap A.periods)
      ⟨A.regularCoordinate, A.regularCoordinate_isLocalHomeomorph.continuous⟩ := {
    baseMap := ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩
    lift := ⟨regularTotalSpaceBase A.periods, regularTotalSpaceBase_continuous A.periods⟩
    deckMap := MonoidHom.id Delta
    commutes := fun z ↦ by
      exact A.centralFamilyCoordinate_centralQuotientProjection z
    equivariant := fun g z ↦ regularTotalSpaceBase_familyDeckMap A.periods g z }
  have ha := quotientCover_fundamentalGroupToMulOpposite_naturality hp hq D e a
  have hb := quotientCover_fundamentalGroupToMulOpposite_naturality hp hq D e b
  change hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ a =
    hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ b
  have hab : FundamentalGroup.mapOfEq D.baseMap (D.commutes e) a =
      FundamentalGroup.mapOfEq D.baseMap (D.commutes e) b := by
    simp only [FundamentalGroup.mapOfEq_apply]
    have h' := h
    simp only [FundamentalGroup.map_apply] at h'
    exact congrArg (fun x ↦ Path.Homotopic.Quotient.cast x
      (D.commutes e).symm (D.commutes e).symm) h'
  exact
    ha.trans ((congrArg (hq.fundamentalGroupToMulOpposite ⟨D.lift e, rfl⟩) hab).trans hb.symm)

public theorem regularFamilyOuterDeck_eq_of_coordinate_class_eq_at
    {x : A.CentralFamily} (e : (regularFamilyQuotientMap A.periods) ⁻¹' {x})
    (a b : FundamentalGroup A.CentralFamily x)
    (h : FundamentalGroup.map
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ x a =
      FundamentalGroup.map
      ⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ x b) :
    letI := regularFamilyDeckAction A.periods
    let hp := regularFamilyQuotientMap_isQuotientCoveringMap A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
    hp.fundamentalGroupToMulOpposite e a = hp.fundamentalGroupToMulOpposite e b := by
  obtain ⟨e, he⟩ := e
  change regularFamilyQuotientMap A.periods e = x at he
  cases he
  exact A.regularFamilyOuterDeck_eq_of_coordinate_class_eq e a b h

end SphereSixComplex.Geometry.PaperAnalyticData
