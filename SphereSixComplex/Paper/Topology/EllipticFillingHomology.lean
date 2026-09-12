module

public import SphereSixComplex.Paper.Topology.CuspEllipticInteriorRelators
public import SphereSixComplex.Paper.Topology.PaperEllipticActualStraightPeriod
public import SphereSixComplex.Prerequisites.Topology.FreeLoopHomology

/-! # Elliptic filling relations in first homology

The fiber and base factors may be transported independently in first homology. No synchronized
basepoint trace or nonabelian elliptic relator comparison is needed.
-/

@[expose] public section
noncomputable section
open SphereSixComplex SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.Periods SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily

namespace SphereSixComplex
namespace Geometry.GlobalTorusFamily

theorem regularFamilyPeriodLoop_homology_eq
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (p q : RegularBase (U := U) × ComplexTwoSpace)
    (a : IntegerPeriods) {Y : Type} [TopologicalSpace Y]
    (f : C(RegularTotalSpace F, Y)) :
    loopHomologyClass ((regularFamilyPeriodLoop F p a).map f.continuous) =
      loopHomologyClass ((regularFamilyPeriodLoop F q a).map f.continuous) := by
  let _ := regularTotalSpace_pathConnected F
  obtain ⟨W⟩ := PathConnectedSpace.joined
    (regularFamilyCoverProjection F p) (regularFamilyCoverProjection F q)
  have hh := regularFamilyPeriodLoop_transport_map_of_path F hproper W a f
  have hc := congrArg (hurewiczFunction _) hh
  exact hc.trans (loopHomologyClass_whisker _ _)

end Geometry.GlobalTorusFamily
end SphereSixComplex

namespace SphereSixComplex
namespace Geometry.AnalyticData
open LatticeData
variable (A : AnalyticData)

theorem orderThreeStraightFiber_homology_eq_cuspPeriod :
    let _ := A.ellipticThreeBoundaryAction
    loopHomologyClass A.orderThreeCentralActualBasedStraightFiberPath =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint epsilon).map
        (regularFamilyQuotientMap A.periods).continuous) := by
  let _ := A.ellipticThreeBoundaryAction
  exact (loopHomologyClass_eq_of_toContinuousMap_eq _ _
    A.orderThreeMappedActualStraightPeriod_eq_actualBasedStraightFiber).symm.trans
    (regularFamilyPeriodLoop_homology_eq A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.ellipticThreeStraightCoverPoint A.cuspRegularCoverPoint epsilon
      (regularFamilyQuotientMap A.periods))

theorem orderFourStraightFiber_homology_eq_cuspPeriod :
    let _ := A.ellipticFourBoundaryAction
    loopHomologyClass A.orderFourCentralActualBasedStraightFiberPath =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint (-epsilon')).map
        (regularFamilyQuotientMap A.periods).continuous) := by
  let _ := A.ellipticFourBoundaryAction
  exact (loopHomologyClass_eq_of_toContinuousMap_eq _ _
    A.orderFourMappedActualStraightPeriod_eq_actualBasedStraightFiber).symm.trans
    (regularFamilyPeriodLoop_homology_eq A.periods
      (sourceActionProperlyDiscontinuous_of_eq
        A.modular.modularParameter.toTriangleUniformization_sourceAction)
      A.ellipticFourStraightCoverPoint A.cuspRegularCoverPoint (-epsilon')
      (regularFamilyQuotientMap A.periods))

end Geometry.AnalyticData
end SphereSixComplex

namespace SphereSixComplex.Geometry.AnalyticData
open LatticeData
variable (A : AnalyticData)

theorem orderThreeFillingRelation_homology_split :
    let _ := A.ellipticThreeBoundaryAction
    loopHomologyClass ((A.orderThreeFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderThreeCollarRegularRepresentative_base_projects.symm
        A.orderThreeCollarRegularRepresentative_base_projects.symm) =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint epsilon).map
        (regularFamilyQuotientMap A.periods).continuous) +
      loopHomologyClass A.orderThreeCentralAffineZeroSectionTriplePath := by
  let _ := A.ellipticThreeBoundaryAction
  have hsplit := congrArg (hurewiczFunction _) (Path.Homotopic.Quotient.eq.mpr
    A.orderThreeProjectedRegularLoop_pathHomotopic_localFiberThenBase)
  change loopHomologyClass _ = loopHomologyClass A.orderThreeLocalFiberThenBaseCentralPath at hsplit
  dsimp only
  refine hsplit.trans ?_
  rw [ A.orderThreeLocalFiberThenBaseCentralPath_eq_trans, loopHomologyClass_trans]
  have hf := congrArg (hurewiczFunction _) (Path.Homotopic.Quotient.eq.mpr
    A.orderThreeLocalOffsetFiberCentralPath_homotopic_actualBasedStraight)
  change loopHomologyClass _ =
    loopHomologyClass A.orderThreeCentralActualBasedStraightFiberPath at hf
  obtain ⟨H, hH⟩ := A.orderThreeLocalOffsetBaseCentralPath_homotopy_globalZeroSectionTriple
  exact congrArg₂ (· + ·) (hf.trans (A.orderThreeStraightFiber_homology_eq_cuspPeriod))
    (loopHomologyClass_eq_of_freeHomotopy _ _ H hH)

theorem orderFourFillingRelation_homology_split :
    let _ := A.ellipticFourBoundaryAction
    loopHomologyClass ((A.orderFourFillingRelationRegularLoop.map
      A.centralQuotientProjection_isLocalHomeomorph.continuous).cast
        A.orderFourCollarRegularRepresentative_base_projects.symm
        A.orderFourCollarRegularRepresentative_base_projects.symm) =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint (-epsilon')).map
        (regularFamilyQuotientMap A.periods).continuous) +
      loopHomologyClass A.orderFourCentralAffineZeroSectionQuadruplePath := by
  let _ := A.ellipticFourBoundaryAction
  have hsplit := congrArg (hurewiczFunction _) (Path.Homotopic.Quotient.eq.mpr
    A.orderFourProjectedRegularLoop_homotopic_fiberThenBase)
  change loopHomologyClass _ = loopHomologyClass A.orderFourCentralFiberThenBaseLoop at hsplit
  dsimp only
  refine hsplit.trans ?_
  rw [ A.orderFourCentralFiberThenBaseLoop_eq_factors, loopHomologyClass_trans]
  have hf := congrArg (hurewiczFunction _) (Path.Homotopic.Quotient.eq.mpr
    A.orderFourCentralFiberFactor_homotopic_actualBasedStraight)
  change loopHomologyClass _ =
    loopHomologyClass A.orderFourCentralActualBasedStraightFiberPath at hf
  obtain ⟨H, hH⟩ := A.orderFourCentralBaseFactor_homotopy_globalZeroSectionQuadruple
  exact congrArg₂ (· + ·) (hf.trans (A.orderFourStraightFiber_homology_eq_cuspPeriod))
    (loopHomologyClass_eq_of_freeHomotopy _ _ H hH)

end SphereSixComplex.Geometry.AnalyticData

namespace SphereSixComplex.Geometry.AnalyticData
variable (A : AnalyticData)

theorem orderThreeZeroSection_homology :
    loopHomologyClass A.orderThreeCentralAffineZeroSectionTriplePath =
      (3 : ℕ) • hurewiczFunction A.centralAffineBase A.centralAffineCorePiOneData.rhoOne := by
  have h := congrArg (hurewiczFunction A.centralAffineBase)
    A.orderThreeCentralAffineZeroSectionTriplePath_class
  change loopHomologyClass _ = hurewiczFunction _ (A.centralAffineCorePiOneData.rhoOne ^ 3) at h
  refine h.trans ?_
  exact congrArg Multiplicative.toAdd
    ((hurewiczPi1 A.centralAffineBase).map_pow A.centralAffineCorePiOneData.rhoOne 3)

theorem orderFourZeroSection_homology :
    loopHomologyClass A.orderFourCentralAffineZeroSectionQuadruplePath =
      (4 : ℕ) • hurewiczFunction A.centralAffineBase A.centralAffineCorePiOneData.rhoTwo := by
  have h := congrArg (hurewiczFunction A.centralAffineBase)
    A.orderFourCentralAffineZeroSectionQuadruplePath_class
  change loopHomologyClass _ = hurewiczFunction _ (A.centralAffineCorePiOneData.rhoTwo ^ 4) at h
  refine h.trans ?_
  exact congrArg Multiplicative.toAdd
    ((hurewiczPi1 A.centralAffineBase).map_pow A.centralAffineCorePiOneData.rhoTwo 4)

end SphereSixComplex.Geometry.AnalyticData

namespace SphereSixComplex.Geometry.AnalyticData
variable (A : AnalyticData)

theorem orderThreeCanonicalRelator_homology_split :
    let _ := A.ellipticThreeBoundaryAction
    hurewiczFunction A.ellipticThreeOverlapCentralBase A.ellipticThreeCanonicalRelatorInCentral =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
        LatticeData.epsilon).map
        (regularFamilyQuotientMap A.periods).continuous) +
      (3 : ℕ) • hurewiczFunction A.centralAffineBase A.centralAffineCorePiOneData.rhoOne := by
  let _ := A.ellipticThreeBoundaryAction
  have h := congrArg (hurewiczFunction A.ellipticThreeOverlapCentralBase)
    A.ellipticThreeCanonicalRelatorInCentral_eq_regularLoopProjection
  rw [hurewiczFunction_baseEq] at h
  refine h.trans ?_
  exact (A.orderThreeFillingRelation_homology_split).trans
    (congrArg₂ (· + ·) rfl A.orderThreeZeroSection_homology)

theorem orderFourCanonicalRelator_homology_split :
    let _ := A.ellipticFourBoundaryAction
    hurewiczFunction A.ellipticFourOverlapCentralBase A.ellipticFourCanonicalRelatorInCentral =
      loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint
        (-LatticeData.epsilon')).map
        (regularFamilyQuotientMap A.periods).continuous) +
      (4 : ℕ) • hurewiczFunction A.centralAffineBase A.centralAffineCorePiOneData.rhoTwo := by
  let _ := A.ellipticFourBoundaryAction
  have h := congrArg (hurewiczFunction A.ellipticFourOverlapCentralBase)
    A.ellipticFourCanonicalRelatorInCentral_eq_regularLoopProjection
  rw [hurewiczFunction_baseEq] at h
  refine h.trans ?_
  exact (A.orderFourFillingRelation_homology_split).trans
    (congrArg₂ (· + ·) rfl A.orderFourZeroSection_homology)

end SphereSixComplex.Geometry.AnalyticData


open SphereSixComplex SphereSixComplex.Hurewicz.Chains
namespace SphereSixComplex.Geometry.AnalyticData
variable (A : AnalyticData)

theorem cuspCentralToCoreEquiv_hurewicz
    (g : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne
      (A.cuspCentralToCoreEquiv g)) =
      integralSingularHomologyMap 1 A.actualCoreToEllipticInterior
        (integralSingularHomologyMap 1
          ⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
            A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩
          (hurewiczFunction _ g)) := by
  rw [actualCoreToEllipticInteriorPiOne, hurewiczFunction_map]
  unfold cuspCentralToCoreEquiv
  erw [hurewiczFunction_basePath, hurewiczFunction_homeomorphMulEquivOfEq]
  rfl

theorem ellipticThreeCentralToCoreEquiv_hurewicz
    (g : FundamentalGroup A.CentralFamily A.ellipticThreeOverlapCentralBase) :
    hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne
      (A.ellipticThreeCentralToCoreEquiv g)) =
      integralSingularHomologyMap 1 A.actualCoreToEllipticInterior
        (integralSingularHomologyMap 1
          ⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
            A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩
          (hurewiczFunction _ g)) := by
  rw [actualCoreToEllipticInteriorPiOne, hurewiczFunction_map]
  unfold ellipticThreeCentralToCoreEquiv
  erw [hurewiczFunction_basePath, hurewiczFunction_homeomorphMulEquivOfEq]
  rfl

theorem ellipticFourCentralToCoreEquiv_hurewicz
    (g : FundamentalGroup A.CentralFamily A.ellipticFourOverlapCentralBase) :
    hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne
      (A.ellipticFourCentralToCoreEquiv g)) =
      integralSingularHomologyMap 1 A.actualCoreToEllipticInterior
        (integralSingularHomologyMap 1
          ⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
            A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩
          (hurewiczFunction _ g)) := by
  rw [actualCoreToEllipticInteriorPiOne, hurewiczFunction_map]
  unfold ellipticFourCentralToCoreEquiv
  erw [hurewiczFunction_basePath, hurewiczFunction_homeomorphMulEquivOfEq]
  rfl

theorem geometricMarkedCentralToCoreEquiv_hurewicz
    (g : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne
      (A.geometricMarkedCentralToCoreEquiv g)) =
      integralSingularHomologyMap 1 A.actualCoreToEllipticInterior
        (integralSingularHomologyMap 1
          ⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
            A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩
          (hurewiczFunction _ g)) := by
  rw [← A.cuspCentralToCoreEquiv_hurewicz g]
  change Multiplicative.toAdd ((hurewiczPi1 _)
    (A.actualCoreToEllipticInteriorPiOne (A.geometricMarkedCentralToCoreEquiv g))) =
    Multiplicative.toAdd ((hurewiczPi1 _)
      (A.actualCoreToEllipticInteriorPiOne (A.cuspCentralToCoreEquiv g)))
  congr 1
  simp only [geometricMarkedCentralToCoreEquiv, cuspToCoreEquiv,
    cuspCentralMarkingCorrection, MulEquiv.trans_apply, MulAut.conj_inv_apply,
    map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact inv_mul_cancel_comm _ _

end SphereSixComplex.Geometry.AnalyticData
namespace SphereSixComplex.Geometry.AnalyticData
open LatticeData
variable (A : AnalyticData)

noncomputable def centralToInteriorHomologyOne : IntegralSingularHomology 1 A.CentralFamily →+
    IntegralSingularHomology 1 A.ellipticInterior :=
  (integralSingularHomologyMap 1 A.actualCoreToEllipticInterior).comp
    (integralSingularHomologyMap 1
      ⟨A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph,
        A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph.continuous⟩)

theorem orderThreeCanonicalRelator_homology_killed :
    A.centralToInteriorHomologyOne
      (hurewiczFunction _ A.ellipticThreeCanonicalRelatorInCentral) = 0 := by
  refine (A.ellipticThreeCentralToCoreEquiv_hurewicz
    A.ellipticThreeCanonicalRelatorInCentral).symm.trans ?_
  have h := congrArg (fun g ↦ hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne g))
    A.ellipticThreeCanonicalRelatorInCentral_toCore
  refine h.trans ?_
  exact (congrArg (hurewiczFunction _) A.actualThreeRelator_ellipticInterior_killed).trans
    (congrArg Multiplicative.toAdd (map_one (hurewiczPi1 _)))

theorem orderFourCanonicalRelator_homology_killed :
    A.centralToInteriorHomologyOne
      (hurewiczFunction _ A.ellipticFourCanonicalRelatorInCentral) = 0 := by
  refine (A.ellipticFourCentralToCoreEquiv_hurewicz
    A.ellipticFourCanonicalRelatorInCentral).symm.trans ?_
  have h := congrArg (fun g ↦ hurewiczFunction _ (A.actualCoreToEllipticInteriorPiOne g))
    A.ellipticFourCanonicalRelatorInCentral_toCore
  refine h.trans ?_
  exact (congrArg (hurewiczFunction _) A.actualFourRelator_ellipticInterior_killed).trans
    (congrArg Multiplicative.toAdd (map_one (hurewiczPi1 _)))

end SphereSixComplex.Geometry.AnalyticData

namespace SphereSixComplex.Geometry.GlobalTorusFamily

theorem regularFamilyPeriodLoop_homology_rhoLambda
    {U : TriangleUniformization} (F : PeriodFunctions U)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (p : RegularBase (U := U) × ComplexTwoSpace)
    (g : SphereSixComplex.TriangleGroup.Delta) (a : IntegerPeriods) :
    loopHomologyClass ((regularFamilyPeriodLoop F p
      (SphereSixComplex.TriangleGroup.rhoLambda g a)).map
      (regularFamilyQuotientMap F).continuous) =
    loopHomologyClass ((regularFamilyPeriodLoop F p a).map
      (regularFamilyQuotientMap F).continuous) := by
  have h := regularFamilyPeriodLoop_homology_eq F hproper p
    (regularDeckMap F g p) (SphereSixComplex.TriangleGroup.rhoLambda g a)
    (regularFamilyQuotientMap F)
  have hd := congrArg loopHomologyClass (regularFamilyPeriodLoop_deck F g p a)
  rw [loopHomologyClass_cast] at hd
  exact h.trans hd

end SphereSixComplex.Geometry.GlobalTorusFamily

namespace SphereSixComplex.Geometry.AnalyticData

theorem cuspPeriod_homology_eq_correctedTranslation
    (A : AnalyticData) (a : SphereSixComplex.LatticeData.Lattice) :
    loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint a).map
      (regularFamilyQuotientMap A.periods).continuous) =
      hurewiczFunction A.cuspCentralBase
        (Additive.toMul (A.correctedActualCuspCentralTranslation a)) := by
  change _ = hurewiczFunction A.cuspCentralBase
    (Additive.toMul (A.cuspCentralTranslation
      (SphereSixComplex.TriangleGroup.rhoLambda
        ((SphereSixComplex.TriangleGroup.g₁ * SphereSixComplex.TriangleGroup.g₂) ^
          A.geometricCentralCuspConjugatorExponent) a)))
  rw [A.cuspCentralTranslation_eq_periodLoop]
  change _ = loopHomologyClass (A.cuspCentralPeriodLoop _)
  have hp (b : SphereSixComplex.LatticeData.Lattice) :
      loopHomologyClass (A.cuspCentralPeriodLoop b) =
        loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint b).map
          (regularFamilyQuotientMap A.periods).continuous) := by
    apply loopHomologyClass_eq_of_toContinuousMap_eq
    rfl
  rw [hp]
  exact (regularFamilyPeriodLoop_homology_rhoLambda A.periods
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.cuspRegularCoverPoint _ a).symm

end SphereSixComplex.Geometry.AnalyticData
namespace SphereSixComplex.Geometry.AnalyticData
open LatticeData SphereSixComplex.Topology
variable (A : AnalyticData)

theorem cuspPeriod_homology_eq_affineTranslation (a : Lattice) :
    loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint a).map
      (regularFamilyQuotientMap A.periods).continuous) =
      hurewiczFunction A.centralAffineBase
        (Additive.toMul (A.centralAffineCorePiOneData.translation a)) := by
  exact A.cuspPeriod_homology_eq_correctedTranslation a

noncomputable def centralToInteriorAbelian :
    FundamentalGroup A.CentralFamily A.centralAffineBase →*
      Multiplicative (IntegralSingularHomology 1 A.ellipticInterior) :=
  A.centralToInteriorHomologyOne.toMultiplicative.comp (hurewiczPi1 A.centralAffineBase)

theorem centralToInteriorAbelian_orderThree :
    A.centralToInteriorAbelian A.centralAffineCorePiOneData.rhoOne ^ 3 =
      A.centralToInteriorAbelian
        (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon))) := by
  let J := A.centralToInteriorHomologyOne
  have hs := congrArg J A.orderThreeCanonicalRelator_homology_split
  have hk := A.orderThreeCanonicalRelator_homology_killed
  change J (hurewiczFunction _ A.ellipticThreeCanonicalRelatorInCentral) = 0 at hk
  rw [hk, map_add, map_nsmul, A.cuspPeriod_homology_eq_affineTranslation] at hs
  apply Multiplicative.toAdd.injective
  change (3 : ℕ) • J (hurewiczFunction _ A.centralAffineCorePiOneData.rhoOne) = _
  have hn : (A.centralToInteriorAbelian
      (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon)))).toAdd =
      -J (hurewiczFunction _
        (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon))) := by
    simp only [map_neg, toMul_neg, map_inv]
    rfl
  rw [hn]
  exact eq_neg_of_add_eq_zero_right hs.symm

theorem centralToInteriorAbelian_orderFour :
    A.centralToInteriorAbelian A.centralAffineCorePiOneData.rhoTwo ^ 4 =
      A.centralToInteriorAbelian
        (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon')) := by
  let J := A.centralToInteriorHomologyOne
  have hs := congrArg J A.orderFourCanonicalRelator_homology_split
  have hk := A.orderFourCanonicalRelator_homology_killed
  change J (hurewiczFunction _ A.ellipticFourCanonicalRelatorInCentral) = 0 at hk
  rw [hk, map_add, map_nsmul, A.cuspPeriod_homology_eq_affineTranslation] at hs
  apply Multiplicative.toAdd.injective
  change (4 : ℕ) • J (hurewiczFunction _ A.centralAffineCorePiOneData.rhoTwo) = _
  have hn : J (hurewiczFunction _
      (Additive.toMul (A.centralAffineCorePiOneData.translation (-epsilon')))) =
      -(A.centralToInteriorAbelian
        (Additive.toMul (A.centralAffineCorePiOneData.translation epsilon'))).toAdd := by
    change (A.centralToInteriorAbelian (Additive.toMul
      (A.centralAffineCorePiOneData.translation (-epsilon')))).toAdd = _
    simp only [map_neg, toMul_neg, map_inv]
    rfl
  rw [hn] at hs
  exact (eq_of_neg_add_eq_zero hs.symm).symm

end SphereSixComplex.Geometry.AnalyticData
namespace SphereSixComplex.Geometry.AnalyticData
open LatticeData SphereSixComplex.Topology
variable (A : AnalyticData)

theorem ellipticInterior_peripheral_twelfth_homology :
    let C := A.coreDataOf A.cuspCentralNaturality
    hurewiczPi1 _ (A.actualCoreToEllipticInteriorPiOne ((C.rhoOne * C.rhoTwo)⁻¹)) ^ 12 =
      hurewiczPi1 _ (A.actualCoreToEllipticInteriorPiOne
        (Additive.toMul (C.translation (Pi.single (0 : Fin 4) 1)))) := by
  have he (g : FundamentalGroup A.CentralFamily A.centralAffineBase) :
      hurewiczPi1 _ (A.actualCoreToEllipticInteriorPiOne
        (A.cuspCentralNaturality.centralToCore g)) = A.centralToInteriorAbelian g := by
    apply Multiplicative.toAdd.injective
    exact A.geometricMarkedCentralToCoreEquiv_hurewicz g
  have h := affineCore_peripheral_twelfth_abelian A.centralAffineCorePiOneData
    A.centralToInteriorAbelian A.centralToInteriorAbelian_orderThree
    A.centralToInteriorAbelian_orderFour
  rw [← he, ← he] at h
  simp only [map_mul, map_inv] at h
  dsimp only [coreDataOf, AffineTorusCorePiOneData.mapSurjective]
  simp only [map_mul, map_inv]
  exact h

theorem ellipticInterior_cuspMeridian_twelfth_homology :
    hurewiczPi1 _ (A.actualCoreToEllipticInteriorPiOne
      (A.cuspOverlapToCore A.cuspAffineBridgeMeridian)⁻¹) ^ 12 =
      hurewiczPi1 _ (A.actualCoreToEllipticInteriorPiOne
        (A.cuspOverlapToCore (Additive.toMul
          (A.cuspAffineBridgeTranslation (Pi.single (0 : Fin 4) 1))))) := by
  rw [A.cuspBridge_translation_core A.cuspCentralNaturality,
    A.cuspBridge_meridian_core A.cuspCentralNaturality]
  have hz : Additive.toMul
      ((A.coreDataOf A.cuspCentralNaturality).translation 0) = 1 :=
    congrArg Additive.toMul (map_zero
      (A.coreDataOf A.cuspCentralNaturality).translation)
  rw [hz]
  simp only [inv_one, mul_one]
  exact A.ellipticInterior_peripheral_twelfth_homology
end SphereSixComplex.Geometry.AnalyticData
end
