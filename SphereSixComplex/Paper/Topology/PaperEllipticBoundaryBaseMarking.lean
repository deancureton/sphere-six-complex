module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof
import all SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof
import all SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeZeroSectionHomotopyProof

/-!
# First-power markings of the actual elliptic boundary meridians

Translation loops project trivially to the base. The synchronized powered base homotopies
therefore identify the physical meridians themselves, by unique roots in the base free group.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Topology
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Periods.SourceAutomaticBranch
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : AnalyticData)

public theorem orderFourCollarRegularRepresentative_coordinate
    (lift : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    (A.centralFamilyCoordinate
      (A.centralQuotientProjection (A.orderFourCollarRegularRepresentativeMap lift))).1 =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianTwoFixedPoint
        (((lift.1 : ℝ) : ℂ) * ((CyclicAngularFundamentalDomain.angleMap 4 lift.2.1 : Circle) : ℂ)) := by
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  let _ := A.totalSpaceCharts
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let q := orderFourPuncturedCollarGaugeEquiv A.periods A.starSeparation.orderFour.radius
    (A.orderFourCollarInverseRepresentative lift)
  change A.modular.sourceCoordinate.coordinate
    (regularTotalSpaceBase A.periods
      (orderFourCollarToRegular A.periods hproper A.starSeparation.orderFour.sourceData q)).1 = _
  rw [orderFourCollarToRegular_base A.periods hproper
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderFour.sourceData q]
  have hqbase : familyTotalSpaceBase A.periods q =
      familyTotalSpaceBase A.periods (A.orderFourCollarInverseRepresentative lift).1 := by
    change familyTotalSpaceBase A.periods
      (orderFourPrincipalGaugeEquiv A.periods (A.orderFourCollarInverseRepresentative lift).1) = _
    rw [orderFourPrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
      familyTotalSpaceBase_familyTranslationMap]
  rw [hqbase, ← A.orderFourCayleyRegularCoordinate_chartFunction,
    A.orderFourCollarInverseRepresentative_cayley]


public theorem orderFourDeckStraightCentralLoop_projects_representative
    (g : OrderFourAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    A.ellipticFourBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection (A.orderFourCollarRegularRepresentativeMap
        (A.ellipticFourBoundaryDeckStraightLift g t)) := by
  let _ := A.ellipticFourBoundaryAction
  simpa [orderFourCollarRegularRepresentativeMap,
    ellipticFourBoundaryDeckStraightLift] using
    A.ellipticFourBoundaryDeckStraightCentralLoop_apply_explicit g t

public theorem orderFourTranslationStraightLift_angle
    (a : SphereSixComplex.LatticeData.Lattice) (t : unitInterval) :
    letI := A.ellipticFourBoundaryAction
    (A.ellipticFourBoundaryDeckStraightLift
      (Additive.toMul (A.ellipticFourBoundaryDeckData.translation a)) t).2.1 =
      A.ellipticFourBoundaryBase.2.1 := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticFourBoundaryAction
  change (Path.segment A.ellipticFourBoundaryBase.2
    (Additive.toMul (affineTorusMappingTorusDeckTranslation
      (orderFourDescendedAffineTorusAutomorphism A.periods) a) •
        A.ellipticFourBoundaryBase.2) t).1 = _
  rw [affineTorusMappingTorusDeckTranslation_smul]
  change (t : ℝ) * (A.ellipticFourBoundaryBase.2.1 -
    A.ellipticFourBoundaryBase.2.1) + A.ellipticFourBoundaryBase.2.1 = _
  ring

public theorem orderFourTranslationStraightCentralLoop_basePath
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.ellipticFourBoundaryAction
    (A.ellipticFourBoundaryDeckStraightCentralLoop
      (Additive.toMul (A.ellipticFourBoundaryDeckData.translation a))).map
        A.centralFamilyCoordinate_continuous =
      Path.refl (A.centralFamilyCoordinate A.ellipticFourCentralBase) := by
  let _ := A.ellipticFourBoundaryAction
  let g := Additive.toMul (A.ellipticFourBoundaryDeckData.translation a)
  let L := A.ellipticFourBoundaryDeckStraightCentralLoop g
  apply Path.ext
  funext t
  change A.centralFamilyCoordinate (L t) = _
  calc
    A.centralFamilyCoordinate (L t) = A.centralFamilyCoordinate (L 0) := by
      apply Subtype.ext
      dsimp only [L, g]
      rw [A.orderFourDeckStraightCentralLoop_projects_representative,
        A.orderFourDeckStraightCentralLoop_projects_representative,
        A.orderFourCollarRegularRepresentative_coordinate,
        A.orderFourCollarRegularRepresentative_coordinate,
        A.orderFourTranslationStraightLift_angle,
        A.orderFourTranslationStraightLift_angle]
      rfl
    _ = _ := congrArg A.centralFamilyCoordinate L.source

public noncomputable def orderFourBoundaryBaseHom :
    FundamentalGroup (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      (A.ellipticFourBoundaryProjection A.ellipticFourBoundaryBase) →*
      FundamentalGroup TwicePuncturedComplex
        (A.centralFamilyCoordinate A.ellipticFourCentralBase) :=
  (FundamentalGroup.mapOfEq
    (⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ :
      C(A.CentralFamily, TwicePuncturedComplex)) rfl).comp
    (FundamentalGroup.mapOfEq A.ellipticFourOverlapToCentral rfl)

public theorem orderFourBoundaryBaseHom_ofDeck
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.ellipticFourBoundaryAction
    letI := A.ellipticFourBoundaryCover_simplyConnected
    A.orderFourBoundaryBaseHom
      (SphereSixComplex.ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase g) =
      Path.Homotopic.Quotient.mk
        ((A.ellipticFourBoundaryDeckStraightCentralLoop g).map
          A.centralFamilyCoordinate_continuous) := by
  let _ := A.ellipticFourBoundaryAction
  let _ := A.ellipticFourBoundaryCover_simplyConnected
  rw [← A.ellipticFourBoundaryDeckStraightLoop_class_eq_ofDeck]
  simp only [orderFourBoundaryBaseHom, MonoidHom.comp_apply]
  erw [A.ellipticFourBoundaryDeckStraightCentralLoop_class g,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem orderFourBoundaryBaseHom_translation
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.ellipticFourBoundaryAction
    letI := A.ellipticFourBoundaryCover_simplyConnected
    A.orderFourBoundaryBaseHom
      (SphereSixComplex.ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase
          (Additive.toMul (A.ellipticFourBoundaryDeckData.translation a))) = 1 := by
  let _ := A.ellipticFourBoundaryAction
  let _ := A.ellipticFourBoundaryCover_simplyConnected
  rw [A.orderFourBoundaryBaseHom_ofDeck, A.orderFourTranslationStraightCentralLoop_basePath]
  rfl

public theorem orderFourBoundaryBaseHom_fillingRelation
    : letI := A.ellipticFourBoundaryAction
    letI := A.ellipticFourBoundaryCover_simplyConnected
    A.orderFourBoundaryBaseHom
      (SphereSixComplex.ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
        A.ellipticFourBoundaryBase
          A.ellipticFourBoundaryDeckData.fillingRelation) =
      (A.orderFourBoundaryBaseHom
        (SphereSixComplex.ofDeck A.ellipticFourBoundaryProjection_isQuotientCoveringMap
          A.ellipticFourBoundaryBase
            A.ellipticFourBoundaryDeckData.meridian)) ^ 4 := by
  let _ := A.ellipticFourBoundaryAction
  let _ := A.ellipticFourBoundaryCover_simplyConnected
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation, SphereSixComplex.ofDeck_mul,
    SphereSixComplex.ofDeck_pow, SphereSixComplex.ofDeck_inv, map_mul, map_inv, map_pow,
    A.orderFourBoundaryBaseHom_translation, inv_one, one_mul]


public theorem orderThreeCollarRegularRepresentative_coordinate
    (lift : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    (A.centralFamilyCoordinate
      (A.centralQuotientProjection (A.orderThreeCollarRegularRepresentativeMap lift))).1 =
      ellipticChartFunction A.modular.sourceCoordinate.coordinate fuchsianOneFixedPoint
        (((lift.1 : ℝ) : ℂ) * ((CyclicAngularFundamentalDomain.angleMap 3 lift.2.1 : Circle) : ℂ)) := by
  rw [A.centralFamilyCoordinate_centralQuotientProjection]
  let _ := A.totalSpaceCharts
  let hproper : SourceActionProperlyDiscontinuous
      (U := A.modular.modularParameter.toTriangleUniformization) :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let q := orderThreePuncturedCollarGaugeEquiv A.periods A.starSeparation.orderThree.radius
    (A.orderThreeCollarInverseRepresentative lift)
  change A.modular.sourceCoordinate.coordinate
    (regularTotalSpaceBase A.periods
      (orderThreeCollarToRegular A.periods hproper A.starSeparation.orderThree.sourceData q)).1 = _
  rw [orderThreeCollarToRegular_base A.periods hproper
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.sourceData q]
  have hqbase : familyTotalSpaceBase A.periods q =
      familyTotalSpaceBase A.periods (A.orderThreeCollarInverseRepresentative lift).1 := by
    change familyTotalSpaceBase A.periods
      (orderThreePrincipalGaugeEquiv A.periods (A.orderThreeCollarInverseRepresentative lift).1) = _
    rw [orderThreePrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
      familyTotalSpaceBase_familyTranslationMap]
  rw [hqbase, ← A.orderThreeCayleyRegularCoordinate_chartFunction,
    A.orderThreeCollarInverseRepresentative_cayley]


public theorem orderThreeDeckStraightCentralLoop_projects_representative
    (g : OrderThreeAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    A.ellipticThreeBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection (A.orderThreeCollarRegularRepresentativeMap
        (A.ellipticThreeBoundaryDeckStraightLift g t)) := by
  let _ := A.ellipticThreeBoundaryAction
  simpa [orderThreeCollarRegularRepresentativeMap,
    ellipticThreeBoundaryDeckStraightLift] using
    A.ellipticThreeBoundaryDeckStraightCentralLoop_apply_explicit g t

public theorem orderThreeTranslationStraightLift_angle
    (a : SphereSixComplex.LatticeData.Lattice) (t : unitInterval) :
    letI := A.ellipticThreeBoundaryAction
    (A.ellipticThreeBoundaryDeckStraightLift
      (Additive.toMul (A.ellipticThreeBoundaryDeckData.translation a)) t).2.1 =
      A.ellipticThreeBoundaryBase.2.1 := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticThreeBoundaryAction
  change (Path.segment A.ellipticThreeBoundaryBase.2
    (Additive.toMul (affineTorusMappingTorusDeckTranslation
      (orderThreeDescendedAffineTorusAutomorphism A.periods) a) •
        A.ellipticThreeBoundaryBase.2) t).1 = _
  rw [affineTorusMappingTorusDeckTranslation_smul]
  change (t : ℝ) * (A.ellipticThreeBoundaryBase.2.1 -
    A.ellipticThreeBoundaryBase.2.1) + A.ellipticThreeBoundaryBase.2.1 = _
  ring

public theorem orderThreeTranslationStraightCentralLoop_basePath
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.ellipticThreeBoundaryAction
    (A.ellipticThreeBoundaryDeckStraightCentralLoop
      (Additive.toMul (A.ellipticThreeBoundaryDeckData.translation a))).map
        A.centralFamilyCoordinate_continuous =
      Path.refl (A.centralFamilyCoordinate A.ellipticThreeCentralBase) := by
  let _ := A.ellipticThreeBoundaryAction
  let g := Additive.toMul (A.ellipticThreeBoundaryDeckData.translation a)
  let L := A.ellipticThreeBoundaryDeckStraightCentralLoop g
  apply Path.ext
  funext t
  change A.centralFamilyCoordinate (L t) = _
  calc
    A.centralFamilyCoordinate (L t) = A.centralFamilyCoordinate (L 0) := by
      apply Subtype.ext
      dsimp only [L, g]
      rw [A.orderThreeDeckStraightCentralLoop_projects_representative,
        A.orderThreeDeckStraightCentralLoop_projects_representative,
        A.orderThreeCollarRegularRepresentative_coordinate,
        A.orderThreeCollarRegularRepresentative_coordinate,
        A.orderThreeTranslationStraightLift_angle,
        A.orderThreeTranslationStraightLift_angle]
      rfl
    _ = _ := congrArg A.centralFamilyCoordinate L.source

public noncomputable def orderThreeBoundaryBaseHom :
    FundamentalGroup (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      (A.ellipticThreeBoundaryProjection A.ellipticThreeBoundaryBase) →*
      FundamentalGroup TwicePuncturedComplex
        (A.centralFamilyCoordinate A.ellipticThreeCentralBase) :=
  (FundamentalGroup.mapOfEq
    (⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ :
      C(A.CentralFamily, TwicePuncturedComplex)) rfl).comp
    (FundamentalGroup.mapOfEq A.ellipticThreeOverlapToCentral rfl)

public theorem orderThreeBoundaryBaseHom_ofDeck
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.ellipticThreeBoundaryAction
    letI := A.ellipticThreeBoundaryCover_simplyConnected
    A.orderThreeBoundaryBaseHom
      (SphereSixComplex.ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
        A.ellipticThreeBoundaryBase g) =
      Path.Homotopic.Quotient.mk
        ((A.ellipticThreeBoundaryDeckStraightCentralLoop g).map
          A.centralFamilyCoordinate_continuous) := by
  let _ := A.ellipticThreeBoundaryAction
  let _ := A.ellipticThreeBoundaryCover_simplyConnected
  rw [← A.ellipticThreeBoundaryDeckStraightLoop_class_eq_ofDeck]
  simp only [orderThreeBoundaryBaseHom, MonoidHom.comp_apply]
  erw [A.ellipticThreeBoundaryDeckStraightCentralLoop_class g,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem orderThreeBoundaryBaseHom_translation
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.ellipticThreeBoundaryAction
    letI := A.ellipticThreeBoundaryCover_simplyConnected
    A.orderThreeBoundaryBaseHom
      (SphereSixComplex.ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
        A.ellipticThreeBoundaryBase
          (Additive.toMul (A.ellipticThreeBoundaryDeckData.translation a))) = 1 := by
  let _ := A.ellipticThreeBoundaryAction
  let _ := A.ellipticThreeBoundaryCover_simplyConnected
  rw [A.orderThreeBoundaryBaseHom_ofDeck, A.orderThreeTranslationStraightCentralLoop_basePath]
  rfl

public theorem orderThreeBoundaryBaseHom_fillingRelation
    : letI := A.ellipticThreeBoundaryAction
    letI := A.ellipticThreeBoundaryCover_simplyConnected
    A.orderThreeBoundaryBaseHom
      (SphereSixComplex.ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
        A.ellipticThreeBoundaryBase
          A.ellipticThreeBoundaryDeckData.fillingRelation) =
      (A.orderThreeBoundaryBaseHom
        (SphereSixComplex.ofDeck A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
          A.ellipticThreeBoundaryBase
            A.ellipticThreeBoundaryDeckData.meridian)) ^ 3 := by
  let _ := A.ellipticThreeBoundaryAction
  let _ := A.ellipticThreeBoundaryCover_simplyConnected
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation, SphereSixComplex.ofDeck_mul,
    SphereSixComplex.ofDeck_pow, SphereSixComplex.ofDeck_inv, map_mul, map_inv, map_pow,
    A.orderThreeBoundaryBaseHom_translation, inv_one, one_mul]


end SphereSixComplex.Geometry.AnalyticData
