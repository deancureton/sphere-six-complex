module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspAngularCentralLoopHomology
public import SphereSixComplex.Paper.Topology.PaperSectionSevenCuspSelectedMeridianSpecializationProof

@[expose] public section

noncomputable section

open AlgebraicTopology Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Topology
open Hurewicz
open SphereSixComplex.StandardCircleHomologyLiftDegree
open CuspPuncturedCollarBridge
open CuspPuncturedCollarBridge.CuspFiberSpecializationNormalization

variable (A : PaperAnalyticData)

public noncomputable def cuspAngularPuncturedLoop :
    Path A.cuspLocalBoundaryBase A.cuspLocalBoundaryBase := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  exact (A.cuspAngularLiftPath.map
    (additiveCuspBoundaryProjection W).continuous).cast
      (by
        exact (additiveCuspBoundaryProjection_basePreimage W
          A.cuspLocalBoundaryBase).symm)
      (by
        exact ((additiveCuspBoundaryProjection_paperCuspBoundaryDeck_smul W
          paperCuspBoundaryMeridian A.cuspBoundaryCoverBase).trans
            (additiveCuspBoundaryProjection_basePreimage W
              A.cuspLocalBoundaryBase)).symm)

public theorem cuspBoundaryMeridianHomologyClass_eq_actualCuspAngularPuncturedLoop :
    cuspBoundaryMeridianHomologyClass A.starCuspWitness A.cuspLocalBoundaryBase =
      loopHomologyClass A.cuspAngularPuncturedLoop := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ := paperCuspFillingDeckAction W
  let U := paperCuspUnwrappedFillingCover W A.cuspLocalBoundaryBase
  let T := U.toToricFillingCoverModel
  let _ : SimplyConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    U.boundarySimplyConnected
  let _ : PathConnectedSpace (puncturedLocalCuspQuotient W) :=
    U.boundaryQuotient.surjective.pathConnectedSpace U.boundaryProjection.continuous
  let p := A.cuspAngularPuncturedLoop
  have hb : T.boundaryProjection T.base = A.cuspLocalBoundaryBase :=
    additiveCuspBoundaryProjection_basePreimage W A.cuspLocalBoundaryBase
  let pT : Path (T.boundaryProjection T.base) (T.boundaryProjection T.base) :=
    p.cast hb hb
  have hmark : T.boundaryFundamentalGroupEquiv
      (Path.Homotopic.Quotient.mk pT) =
      MulOpposite.op paperCuspBoundaryMeridian := by
    let ex : U.boundaryProjection ⁻¹' ({T.boundaryProjection T.base} :
        Set (puncturedLocalCuspQuotient W)) := ⟨U.base, by rfl⟩
    change U.boundaryQuotient.fundamentalGroupToMulOpposite
        ex (Path.Homotopic.Quotient.mk pT) = _
    rw [IsQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff]
    let Gamma : Path.Homotopic.Quotient U.base
        (paperCuspBoundaryMeridian • U.base) :=
      Path.Homotopic.Quotient.mk A.cuspAngularLiftPath
    have hmono := U.boundaryQuotient.isCoveringMap.monodromy_eq_of_map_eq
      (ex := ex)
      (ey := ⟨paperCuspBoundaryMeridian • U.base,
        U.boundaryQuotient.map_smul paperCuspBoundaryMeridian (e := U.base)⟩)
      Gamma (by
        change (Path.Homotopic.Quotient.mk A.cuspAngularLiftPath).map
            U.boundaryProjection =
          (Path.Homotopic.Quotient.mk pT).cast _ _
        unfold pT p cuspAngularPuncturedLoop
        simp only [Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_map]
        apply eq_of_heq
        symm
        exact (Path.Homotopic.Quotient.cast_heq _ _).trans
          ((Path.Homotopic.Quotient.cast_heq _ _).trans
            (Path.Homotopic.Quotient.cast_heq _ _)))
    simp only [MulOpposite.unop_op]
    change paperCuspBoundaryMeridian • U.base = _
    exact congrArg Subtype.val hmono.symm
  let e := T.boundaryFundamentalGroupEquiv
  let hOne := deckHOneEquivOfFundamentalGroupEquivOpposite
    (T.boundaryProjection T.base) e
  have hdeck : deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
      (T.boundaryProjection T.base) e
        (Additive.ofMul (Abelianization.of paperCuspBoundaryMeridian)) =
      Additive.ofMul (Abelianization.of U.fundamentalGroupData.meridian) := by
    apply (deckAbelianPi1EquivOfFundamentalGroupEquivOpposite
      (T.boundaryProjection T.base) e).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change Abelianization.of paperCuspBoundaryMeridian =
      abelianizationMulOppositeEquiv paperCuspBoundaryDeck
        (Abelianization.of (e U.fundamentalGroupData.meridian))
    have he : e U.fundamentalGroupData.meridian =
        MulOpposite.op paperCuspBoundaryMeridian :=
      U.fundamentalGroupData.meridian_deck
    rw [he, abelianizationMulOppositeEquiv_of_op]
  change (abelianizationComparison _ (T.boundaryProjection T.base)).equiv
      (Additive.ofMul (Abelianization.of U.fundamentalGroupData.meridian)) = _
  rw [← hdeck]
  exact deckHOneEquivOfFundamentalGroupEquivOpposite_markedLoop
    (T.boundaryProjection T.base) e
    (fun _ : Unit ↦ paperCuspBoundaryMeridian) (fun _ : Unit ↦ pT)
    (fun _ ↦ hmark) () |>.trans
      (loopHomologyClass_cast p hb)

public theorem cuspMappingTorusMeridianHomologyClass_eq_actualCuspAngularPuncturedLoop_image :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    cuspMappingTorusMeridianHomologyClass G A.cuspLocalBoundaryBase =
      integralSingularHomologyMap 1 G.totalHomotopyEquiv.toFun
        (loopHomologyClass A.cuspAngularPuncturedLoop) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  unfold cuspMappingTorusMeridianHomologyClass
  rw [A.cuspBoundaryMeridianHomologyClass_eq_actualCuspAngularPuncturedLoop]
  rfl

end SphereSixComplex.Geometry.PaperAnalyticData

end
