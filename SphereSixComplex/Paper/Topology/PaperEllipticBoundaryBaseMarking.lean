module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticWholeRelatorClassificationProof
public import SphereSixComplex.Paper.Periods.ExactFuchsianRamification
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourBaseCoordinateLocalDegreeProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticStraightLoopGeometricConnectorReduction
public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof
public import SphereSixComplex.Paper.Topology.PaperActualCuspCentralLoopRelation
import all SphereSixComplex.Paper.Topology.PaperActualEllipticOrderFourZeroSectionComparisonProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeBaseCoordinateLocalDegreeProof
public import SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeZeroSectionHomotopyProof
import all SphereSixComplex.Paper.Topology.PaperActualEllipticOrderThreeZeroSectionHomotopyProof

/-!
# First-power markings of the actual elliptic boundary meridians

Translation loops project trivially to the base. The synchronized powered base homotopies
therefore identify the physical meridians themselves, by unique roots in the base free group.
-/

@[expose] public section

noncomputable section

open Complex Filter Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

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
open SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

variable (A : PaperAnalyticData)

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

public theorem orderFourCollarRegularRepresentative_coordinate_fiber_independent
    (r : OpenRadialInterval A.starSeparation.orderFour.radius) (θ : ℝ)
    (v w : ComplexTwoSpace) :
    A.centralFamilyCoordinate
        (A.centralQuotientProjection (A.orderFourCollarRegularRepresentativeMap (r, θ, v))) =
      A.centralFamilyCoordinate
        (A.centralQuotientProjection (A.orderFourCollarRegularRepresentativeMap (r, θ, w))) := by
  apply Subtype.ext
  rw [A.orderFourCollarRegularRepresentative_coordinate,
    A.orderFourCollarRegularRepresentative_coordinate]

public theorem orderFourDeckStraightCentralLoop_projects_representative
    (g : OrderFourAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection (A.orderFourCollarRegularRepresentativeMap
        (A.orderFourActualEllipticBoundaryDeckStraightLift g t)) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  simpa [orderFourCollarRegularRepresentativeMap,
    orderFourActualEllipticBoundaryDeckStraightLift] using
    A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit g t

public theorem orderFourTranslationStraightLift_angle
    (a : SphereSixComplex.LatticeData.Lattice) (t : unitInterval) :
    letI := A.orderFourActualEllipticBoundaryAction
    (A.orderFourActualEllipticBoundaryDeckStraightLift
      (Additive.toMul (A.orderFourActualEllipticBoundaryDeckData.translation a)) t).2.1 =
      A.orderFourActualEllipticBoundaryBase.2.1 := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  change (Path.segment A.orderFourActualEllipticBoundaryBase.2
    (Additive.toMul (affineTorusMappingTorusDeckTranslation
      (orderFourDescendedAffineTorusAutomorphism A.periods) a) •
        A.orderFourActualEllipticBoundaryBase.2) t).1 = _
  rw [affineTorusMappingTorusDeckTranslation_smul]
  change (t : ℝ) * (A.orderFourActualEllipticBoundaryBase.2.1 -
    A.orderFourActualEllipticBoundaryBase.2.1) + A.orderFourActualEllipticBoundaryBase.2.1 = _
  ring

public theorem orderFourTranslationStraightCentralLoop_basePath
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.orderFourActualEllipticBoundaryAction
    (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
      (Additive.toMul (A.orderFourActualEllipticBoundaryDeckData.translation a))).map
        A.centralFamilyCoordinate_continuous =
      Path.refl (A.centralFamilyCoordinate A.orderFourActualEllipticCentralBase) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let g := Additive.toMul (A.orderFourActualEllipticBoundaryDeckData.translation a)
  let L := A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g
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
      (A.orderFourActualEllipticBoundaryProjection A.orderFourActualEllipticBoundaryBase) →*
      FundamentalGroup TwicePuncturedComplex
        (A.centralFamilyCoordinate A.orderFourActualEllipticCentralBase) :=
  (FundamentalGroup.mapOfEq
    (⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ :
      C(A.CentralFamily, TwicePuncturedComplex)) rfl).comp
    (FundamentalGroup.mapOfEq A.orderFourActualOverlapToCentral rfl)

public theorem orderFourBoundaryBaseHom_ofDeck
    (g : OrderFourAffineMappingTorusDeck A.periods) :
    letI := A.orderFourActualEllipticBoundaryAction
    letI := A.orderFourActualEllipticBoundaryCover_simplyConnected
    A.orderFourBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase g) =
      Path.Homotopic.Quotient.mk
        ((A.orderFourActualEllipticBoundaryDeckStraightCentralLoop g).map
          A.centralFamilyCoordinate_continuous) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := A.orderFourActualEllipticBoundaryCover_simplyConnected
  rw [← A.orderFourActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
  simp only [orderFourBoundaryBaseHom, MonoidHom.comp_apply]
  erw [A.orderFourActualEllipticBoundaryDeckStraightCentralLoop_class g,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem orderFourBoundaryBaseHom_translation
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.orderFourActualEllipticBoundaryAction
    letI := A.orderFourActualEllipticBoundaryCover_simplyConnected
    A.orderFourBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase
          (Additive.toMul (A.orderFourActualEllipticBoundaryDeckData.translation a))) = 1 := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := A.orderFourActualEllipticBoundaryCover_simplyConnected
  rw [A.orderFourBoundaryBaseHom_ofDeck, A.orderFourTranslationStraightCentralLoop_basePath]
  rfl

public theorem orderFourBoundaryBaseHom_fillingRelation
    : letI := A.orderFourActualEllipticBoundaryAction
    letI := A.orderFourActualEllipticBoundaryCover_simplyConnected
    A.orderFourBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase
          A.orderFourActualEllipticBoundaryDeckData.fillingRelation) =
      (A.orderFourBoundaryBaseHom
        (SphereSixComplex.ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase
            A.orderFourActualEllipticBoundaryDeckData.meridian)) ^ 4 := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := A.orderFourActualEllipticBoundaryCover_simplyConnected
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation, SphereSixComplex.ofDeck_mul,
    SphereSixComplex.ofDeck_pow, SphereSixComplex.ofDeck_inv, map_mul, map_inv, map_pow,
    A.orderFourBoundaryBaseHom_translation, inv_one, one_mul]

public theorem orderFourBoundaryMeridian_base_first_power :
    letI := A.orderFourActualEllipticBoundaryAction
    letI := A.orderFourActualEllipticBoundaryCover_simplyConnected
    ∃ w : Path (A.centralFamilyCoordinate A.orderFourActualEllipticCentralBase)
        twicePuncturedComplexBasepoint,
      A.orderFourBoundaryBaseHom
        (SphereSixComplex.ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderFourActualEllipticBoundaryBase A.orderFourActualEllipticBoundaryDeckData.meridian) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm
          TwicePuncturedComplex.oneMeridianClass⁻¹ := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := A.orderFourActualEllipticBoundaryCover_simplyConnected
  let L := (A.orderFourActualEllipticBoundaryDeckStraightCentralLoop
    A.orderFourActualEllipticBoundaryDeckData.fillingRelation).map
      A.centralFamilyCoordinate_continuous
  let gamma := twicePuncturedCounterclockwiseOneQuadruple
  have hmap : A.orderFourFillingRelationBaseCoordinateMap = L.toContinuousMap := by
    unfold orderFourFillingRelationBaseCoordinateMap
    rw [A.orderFourFillingRelationRegularLoop_projects]
    rfl
  obtain ⟨Hraw, hrawTrace⟩ :=
    A.orderFourActualCayleyBaseCoordinate_quadrupleHomotopy_with_trace
  let H : ContinuousMap.Homotopy L.toContinuousMap gamma.toContinuousMap :=
    Hraw.cast (A.orderFourFillingRelationBaseCoordinateMap_eq_cayley.symm.trans hmap) rfl
  have htrace : (H.evalAt 0).cast L.source.symm gamma.source.symm =
      (H.evalAt 1).cast L.target.symm gamma.target.symm := by
    apply Path.ext
    funext s
    exact hrawTrace s
  let w := (H.evalAt 0).cast L.source.symm gamma.source.symm
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm
  have hfree := SphereSixComplex.loopClass_eq_whiskered_of_freeHomotopy L gamma H htrace
  have hp : Path.Homotopic.Quotient.mk L = E (Path.Homotopic.Quotient.mk gamma) := by
    rw [hfree]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
    change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm) _
    unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
    simp only [CategoryTheory.Iso.conj_apply]
    change (Path.Homotopic.Quotient.mk w).trans
      ((Path.Homotopic.Quotient.mk gamma).trans (Path.Homotopic.Quotient.mk w).symm) =
      (Path.Homotopic.Quotient.mk w.symm).symm.trans
        ((Path.Homotopic.Quotient.mk gamma).trans (Path.Homotopic.Quotient.mk w.symm))
    simp only [← Path.Homotopic.Quotient.mk_symm]
    rw [Path.symm_symm]
  have hpow : (A.orderFourBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderFourActualEllipticBoundaryBase A.orderFourActualEllipticBoundaryDeckData.meridian)) ^ 4 =
      (E TwicePuncturedComplex.oneMeridianClass⁻¹) ^ 4 := by
    rw [← A.orderFourBoundaryBaseHom_fillingRelation, A.orderFourBoundaryBaseHom_ofDeck]
    change Path.Homotopic.Quotient.mk L = _
    rw [hp, twicePuncturedCounterclockwiseOneQuadruple_class, map_pow]
  refine ⟨w, ?_⟩
  let F := (TwicePuncturedComplex.markedMeridianMulEquiv
    TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm
  apply E.symm.injective
  apply F.injective
  apply pow_left_injective (by decide : (4 : ℕ) ≠ 0)
  simpa only [← map_pow] using congrArg (fun x ↦ F (E.symm x)) hpow

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

public theorem orderThreeCollarRegularRepresentative_coordinate_fiber_independent
    (r : OpenRadialInterval A.starSeparation.orderThree.radius) (θ : ℝ)
    (v w : ComplexTwoSpace) :
    A.centralFamilyCoordinate
        (A.centralQuotientProjection (A.orderThreeCollarRegularRepresentativeMap (r, θ, v))) =
      A.centralFamilyCoordinate
        (A.centralQuotientProjection (A.orderThreeCollarRegularRepresentativeMap (r, θ, w))) := by
  apply Subtype.ext
  rw [A.orderThreeCollarRegularRepresentative_coordinate,
    A.orderThreeCollarRegularRepresentative_coordinate]

public theorem orderThreeDeckStraightCentralLoop_projects_representative
    (g : OrderThreeAffineMappingTorusDeck A.periods) (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g t =
      A.centralQuotientProjection (A.orderThreeCollarRegularRepresentativeMap
        (A.orderThreeActualEllipticBoundaryDeckStraightLift g t)) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  simpa [orderThreeCollarRegularRepresentativeMap,
    orderThreeActualEllipticBoundaryDeckStraightLift] using
    A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_apply_explicit g t

public theorem orderThreeTranslationStraightLift_angle
    (a : SphereSixComplex.LatticeData.Lattice) (t : unitInterval) :
    letI := A.orderThreeActualEllipticBoundaryAction
    (A.orderThreeActualEllipticBoundaryDeckStraightLift
      (Additive.toMul (A.orderThreeActualEllipticBoundaryDeckData.translation a)) t).2.1 =
      A.orderThreeActualEllipticBoundaryBase.2.1 := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  change (Path.segment A.orderThreeActualEllipticBoundaryBase.2
    (Additive.toMul (affineTorusMappingTorusDeckTranslation
      (orderThreeDescendedAffineTorusAutomorphism A.periods) a) •
        A.orderThreeActualEllipticBoundaryBase.2) t).1 = _
  rw [affineTorusMappingTorusDeckTranslation_smul]
  change (t : ℝ) * (A.orderThreeActualEllipticBoundaryBase.2.1 -
    A.orderThreeActualEllipticBoundaryBase.2.1) + A.orderThreeActualEllipticBoundaryBase.2.1 = _
  ring

public theorem orderThreeTranslationStraightCentralLoop_basePath
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.orderThreeActualEllipticBoundaryAction
    (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
      (Additive.toMul (A.orderThreeActualEllipticBoundaryDeckData.translation a))).map
        A.centralFamilyCoordinate_continuous =
      Path.refl (A.centralFamilyCoordinate A.orderThreeActualEllipticCentralBase) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let g := Additive.toMul (A.orderThreeActualEllipticBoundaryDeckData.translation a)
  let L := A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g
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
      (A.orderThreeActualEllipticBoundaryProjection A.orderThreeActualEllipticBoundaryBase) →*
      FundamentalGroup TwicePuncturedComplex
        (A.centralFamilyCoordinate A.orderThreeActualEllipticCentralBase) :=
  (FundamentalGroup.mapOfEq
    (⟨A.centralFamilyCoordinate, A.centralFamilyCoordinate_continuous⟩ :
      C(A.CentralFamily, TwicePuncturedComplex)) rfl).comp
    (FundamentalGroup.mapOfEq A.orderThreeActualOverlapToCentral rfl)

public theorem orderThreeBoundaryBaseHom_ofDeck
    (g : OrderThreeAffineMappingTorusDeck A.periods) :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI := A.orderThreeActualEllipticBoundaryCover_simplyConnected
    A.orderThreeBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase g) =
      Path.Homotopic.Quotient.mk
        ((A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop g).map
          A.centralFamilyCoordinate_continuous) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := A.orderThreeActualEllipticBoundaryCover_simplyConnected
  rw [← A.orderThreeActualEllipticBoundaryDeckStraightLoop_class_eq_ofDeck]
  simp only [orderThreeBoundaryBaseHom, MonoidHom.comp_apply]
  erw [A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop_class g,
    FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map]
  rfl

public theorem orderThreeBoundaryBaseHom_translation
    (a : SphereSixComplex.LatticeData.Lattice) :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI := A.orderThreeActualEllipticBoundaryCover_simplyConnected
    A.orderThreeBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase
          (Additive.toMul (A.orderThreeActualEllipticBoundaryDeckData.translation a))) = 1 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := A.orderThreeActualEllipticBoundaryCover_simplyConnected
  rw [A.orderThreeBoundaryBaseHom_ofDeck, A.orderThreeTranslationStraightCentralLoop_basePath]
  rfl

public theorem orderThreeBoundaryBaseHom_fillingRelation
    : letI := A.orderThreeActualEllipticBoundaryAction
    letI := A.orderThreeActualEllipticBoundaryCover_simplyConnected
    A.orderThreeBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase
          A.orderThreeActualEllipticBoundaryDeckData.fillingRelation) =
      (A.orderThreeBoundaryBaseHom
        (SphereSixComplex.ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase
            A.orderThreeActualEllipticBoundaryDeckData.meridian)) ^ 3 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := A.orderThreeActualEllipticBoundaryCover_simplyConnected
  rw [UnwrappedCyclicAffineBoundaryDeckData.fillingRelation, SphereSixComplex.ofDeck_mul,
    SphereSixComplex.ofDeck_pow, SphereSixComplex.ofDeck_inv, map_mul, map_inv, map_pow,
    A.orderThreeBoundaryBaseHom_translation, inv_one, one_mul]

public theorem orderThreeBoundaryMeridian_base_first_power :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI := A.orderThreeActualEllipticBoundaryCover_simplyConnected
    ∃ w : Path (A.centralFamilyCoordinate A.orderThreeActualEllipticCentralBase)
        twicePuncturedComplexBasepoint,
      A.orderThreeBoundaryBaseHom
        (SphereSixComplex.ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
          A.orderThreeActualEllipticBoundaryBase A.orderThreeActualEllipticBoundaryDeckData.meridian) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm
          TwicePuncturedComplex.zeroMeridianClass⁻¹ := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := A.orderThreeActualEllipticBoundaryCover_simplyConnected
  let L := (A.orderThreeActualEllipticBoundaryDeckStraightCentralLoop
    A.orderThreeActualEllipticBoundaryDeckData.fillingRelation).map
      A.centralFamilyCoordinate_continuous
  let gamma := twicePuncturedCounterclockwiseZeroTriple
  have hmap : A.orderThreeFillingRelationBaseCoordinateMap = L.toContinuousMap := by
    unfold orderThreeFillingRelationBaseCoordinateMap
    rw [A.orderThreeFillingRelationRegularLoop_projects]
    rfl
  obtain ⟨Hraw, hrawTrace⟩ :=
    A.orderThreeActualCayleyBaseCoordinate_tripleHomotopy_with_trace
  let H : ContinuousMap.Homotopy L.toContinuousMap gamma.toContinuousMap :=
    Hraw.cast (A.orderThreeFillingRelationBaseCoordinateMap_eq_cayley.symm.trans hmap) rfl
  have htrace : (H.evalAt 0).cast L.source.symm gamma.source.symm =
      (H.evalAt 1).cast L.target.symm gamma.target.symm := by
    apply Path.ext
    funext s
    exact hrawTrace s
  let w := (H.evalAt 0).cast L.source.symm gamma.source.symm
  let E := FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm
  have hfree := SphereSixComplex.loopClass_eq_whiskered_of_freeHomotopy L gamma H htrace
  have hp : Path.Homotopic.Quotient.mk L = E (Path.Homotopic.Quotient.mk gamma) := by
    rw [hfree]
    simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
    change _ = (FundamentalGroup.fundamentalGroupMulEquivOfPath w.symm) _
    unfold FundamentalGroup.fundamentalGroupMulEquivOfPath
    simp only [CategoryTheory.Iso.conj_apply]
    change (Path.Homotopic.Quotient.mk w).trans
      ((Path.Homotopic.Quotient.mk gamma).trans (Path.Homotopic.Quotient.mk w).symm) =
      (Path.Homotopic.Quotient.mk w.symm).symm.trans
        ((Path.Homotopic.Quotient.mk gamma).trans (Path.Homotopic.Quotient.mk w.symm))
    simp only [← Path.Homotopic.Quotient.mk_symm]
    rw [Path.symm_symm]
  have hpow : (A.orderThreeBoundaryBaseHom
      (SphereSixComplex.ofDeck A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        A.orderThreeActualEllipticBoundaryBase A.orderThreeActualEllipticBoundaryDeckData.meridian)) ^ 3 =
      (E TwicePuncturedComplex.zeroMeridianClass⁻¹) ^ 3 := by
    rw [← A.orderThreeBoundaryBaseHom_fillingRelation, A.orderThreeBoundaryBaseHom_ofDeck]
    change Path.Homotopic.Quotient.mk L = _
    rw [hp, twicePuncturedCounterclockwiseZeroTriple_class, map_pow]
  refine ⟨w, ?_⟩
  let F := (TwicePuncturedComplex.markedMeridianMulEquiv
    TwicePuncturedComplex.establishedMarkedMeridianHom_injective).symm
  apply E.symm.injective
  apply F.injective
  apply pow_left_injective (by decide : (3 : ℕ) ≠ 0)
  simpa only [← map_pow] using congrArg (fun x ↦ F (E.symm x)) hpow

end SphereSixComplex.Geometry.PaperAnalyticData
