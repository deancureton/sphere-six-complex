module

public import SphereSixComplex.Topology.PaperActualCuspCentralLoopRelation

/-!
# Geometric peripheral classes in the actual central family

This module defines the central translation and cusp-meridian classes directly from the chosen
cusp filling and defines the two finite meridians by transporting the concrete zero-section
loops to the same actual cusp basepoint.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.LatticeData SphereSixComplex.Topology
open CuspPuncturedCollarBridge

variable (A : PaperAnalyticData)

/-- The map on fundamental groups induced by the literal cusp collar chart. -/
public noncomputable def actualCuspOverlapToCentralPiOne :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
          Set A.VanKampenSpace)
        A.actualCuspOverlapBase →*
      FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
  FundamentalGroup.map A.actualCuspOverlapToCentral A.actualCuspOverlapBase

/-- The actual cusp translations, mapped through the literal collar chart into the central
family. -/
public noncomputable def actualCuspCentralTranslation :
    Lattice →+ Additive
      (FundamentalGroup A.CentralFamily A.actualCuspCentralBase) :=
  A.actualCuspOverlapToCentralPiOne.toAdditive.comp
    (fundamentalGroupAddHomOfBaseEq
      A.actualCuspChosenAffineFillingCover_boundaryBase_eq
      A.actualCuspChosenAffineFillingCover.translation)

/-- The actual angular cusp meridian in the central family. -/
public noncomputable def actualCuspCentralMeridian :
    FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
  A.actualCuspOverlapToCentralPiOne
    (fundamentalGroupElementOfBaseEq
      A.actualCuspChosenAffineFillingCover_boundaryBase_eq
      A.actualCuspChosenAffineFillingCover.meridian)

public theorem actualCuspAffineBridgeMeridian_eq_angularProjectedLoop :
    fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        A.actualCuspChosenAffineFillingCover.meridian =
      fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk A.actualCuspAngularProjectedLoop) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.actualCuspBoundaryProjection
      paperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  rw [A.actualCuspChosenAffineFillingCover_meridian_eq_ofDeck]
  apply congrArg
    (fundamentalGroupElementOfBaseEq
      A.actualCuspChosenAffineFillingCover_boundaryBase_eq)
  exact A.actualCuspAngularProjectedLoop_class_eq_ofDeck.symm

/-- The filling's chosen cusp meridian is represented by the literal angular path after applying
the actual central collar chart. -/
public theorem actualCuspCentralMeridian_eq_angularLoop :
    A.actualCuspCentralMeridian =
      Path.Homotopic.Quotient.mk A.actualCuspAngularCentralLoop := by
  rw [actualCuspCentralMeridian,
    A.actualCuspAffineBridgeMeridian_eq_angularProjectedLoop]
  unfold actualCuspOverlapToCentralPiOne
  rw [← TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hsource :
      A.actualCuspOverlapToCentral
          A.actualCuspChosenAffineFillingCover.boundaryBase =
        A.actualCuspCentralBase := by
    rw [A.actualCuspChosenAffineFillingCover_boundaryBase_eq]
    rfl
  calc
    _ = FundamentalGroup.mapOfEq A.actualCuspOverlapToCentral hsource
          (Path.Homotopic.Quotient.mk A.actualCuspAngularProjectedLoop) :=
      mapOfEq_fundamentalGroupElementOfBaseEq
        A.actualCuspChosenAffineFillingCover_boundaryBase_eq
        A.actualCuspOverlapToCentral hsource rfl _
    _ = Path.Homotopic.Quotient.mk A.actualCuspAngularCentralLoop := by
      rw [FundamentalGroup.mapOfEq_apply]
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      rfl

/-- Transport from the marked zero-section basepoint to the selected actual cusp point. -/
public noncomputable def markedCentralToActualCuspEquiv :
    FundamentalGroup A.CentralFamily
        (A.centralZeroSection A.markedPuncturedBasepoint) ≃*
      FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.actualCuspMarkedCentralWhisker

/-- The first finite core meridian is the counterclockwise zero-section meridian, transported to
the actual cusp basepoint. -/
public noncomputable def geometricCentralRhoOne :
    FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
  A.markedCentralToActualCuspEquiv A.markedZeroCentralMeridianClass⁻¹

/-- The second finite core meridian is the counterclockwise zero-section meridian, transported to
the actual cusp basepoint. -/
public noncomputable def geometricCentralRhoTwo :
    FundamentalGroup A.CentralFamily A.actualCuspCentralBase :=
  A.markedCentralToActualCuspEquiv A.markedOneCentralMeridianClass⁻¹

/-- The actual cusp meridian is exactly the product of the two concrete finite core meridians. -/
public theorem actualCuspCentralMeridian_eq_geometricRhoProduct :
    A.actualCuspCentralMeridian =
      A.geometricCentralRhoOne * A.geometricCentralRhoTwo := by
  rw [A.actualCuspCentralMeridian_eq_angularLoop]
  have h := congrArg A.markedCentralToActualCuspEquiv
    A.actualCuspMarkedCentralLoop_class_eq_finiteProduct
  rw [map_mul] at h
  change A.markedCentralToActualCuspEquiv
      (Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralLoop) =
    A.geometricCentralRhoOne * A.geometricCentralRhoTwo at h
  have hwhisker :
      A.markedCentralToActualCuspEquiv.symm
          (Path.Homotopic.Quotient.mk A.actualCuspAngularCentralLoop) =
        Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralLoop := by
    rfl
  calc
    Path.Homotopic.Quotient.mk A.actualCuspAngularCentralLoop =
        A.markedCentralToActualCuspEquiv
          (Path.Homotopic.Quotient.mk A.actualCuspMarkedCentralLoop) := by
      rw [← hwhisker,
        A.markedCentralToActualCuspEquiv.apply_symm_apply]
    _ = A.geometricCentralRhoOne * A.geometricCentralRhoTwo := h

end SphereSixComplex.Geometry.PaperAnalyticData

end
