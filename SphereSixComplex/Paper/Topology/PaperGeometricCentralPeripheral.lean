module

public import SphereSixComplex.Paper.Topology.PaperActualCuspCentralLoopRelation

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
public noncomputable def cuspOverlapToCentralPiOne :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩ A.actualVanKampenFourPieceCover.cusp :
          Set A.VanKampenSpace)
        A.cuspOverlapBase →*
      FundamentalGroup A.CentralFamily A.cuspCentralBase :=
  FundamentalGroup.map A.cuspOverlapToCentral A.cuspOverlapBase

/-- The actual cusp translations, mapped through the literal collar chart into the central
family. -/
public noncomputable def cuspCentralTranslation :
    Lattice →+ Additive
      (FundamentalGroup A.CentralFamily A.cuspCentralBase) :=
  A.cuspOverlapToCentralPiOne.toAdditive.comp
    (fundamentalGroupAddHomOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      A.cuspChosenAffineFillingCover.translation)

/-- The actual angular cusp meridian in the central family. -/
public noncomputable def cuspCentralMeridian :
    FundamentalGroup A.CentralFamily A.cuspCentralBase :=
  A.cuspOverlapToCentralPiOne
    (fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq
      A.cuspChosenAffineFillingCover.meridian)

public theorem cuspAffineBridgeMeridian_eq_angularProjectedLoop :
    fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        A.cuspChosenAffineFillingCover.meridian =
      fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        (Path.Homotopic.Quotient.mk A.cuspAngularProjectedLoop) := by
  let W := A.starCuspWitness
  let _ := paperCuspBoundaryDeckAction W
  let _ : SimplyConnectedSpace
      (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspBoundaryCover_simplyConnected W
  let hp : IsQuotientCoveringMap A.cuspBoundaryProjection
      PaperCuspBoundaryDeck :=
    (additiveCuspBoundaryProjection_isQuotientCoveringMap W).homeomorph_comp
      A.cuspCollarToStarOverlapHomeomorph
  rw [A.cuspChosenAffineFillingCover_meridian_eq_ofDeck]
  apply congrArg
    (fundamentalGroupElementOfBaseEq
      A.cuspChosenAffineFillingCover_boundaryBase_eq)
  exact A.cuspAngularProjectedLoop_class_eq_ofDeck.symm

/-- The filling's chosen cusp meridian is represented by the literal angular path after applying
the actual central collar chart. -/
public theorem cuspCentralMeridian_eq_angularLoop :
    A.cuspCentralMeridian =
      Path.Homotopic.Quotient.mk A.cuspAngularCentralLoop := by
  rw [cuspCentralMeridian,
    A.cuspAffineBridgeMeridian_eq_angularProjectedLoop]
  unfold cuspOverlapToCentralPiOne
  rw [← TauCeti.FundamentalGroup.mapOfEq_rfl]
  have hsource :
      A.cuspOverlapToCentral
          A.cuspChosenAffineFillingCover.boundaryBase =
        A.cuspCentralBase := by
    rw [A.cuspChosenAffineFillingCover_boundaryBase_eq]
    rfl
  calc
    _ = FundamentalGroup.mapOfEq A.cuspOverlapToCentral hsource
          (Path.Homotopic.Quotient.mk A.cuspAngularProjectedLoop) :=
      mapOfEq_fundamentalGroupElementOfBaseEq
        A.cuspChosenAffineFillingCover_boundaryBase_eq
        A.cuspOverlapToCentral hsource rfl _
    _ = Path.Homotopic.Quotient.mk A.cuspAngularCentralLoop := by
      rw [FundamentalGroup.mapOfEq_apply]
      apply congrArg Path.Homotopic.Quotient.mk
      apply Path.ext
      funext t
      rfl

/-- Transport from the marked zero-section basepoint to the selected actual cusp point. -/
public noncomputable def markedCentralToActualCuspEquiv :
    FundamentalGroup A.CentralFamily
        (A.centralZeroSection A.markedPuncturedBasepoint) ≃*
      FundamentalGroup A.CentralFamily A.cuspCentralBase :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath A.cuspMarkedCentralWhisker

/-- The first finite core meridian is the counterclockwise zero-section meridian, transported to
the actual cusp basepoint. -/
public noncomputable def geometricCentralRhoOne :
    FundamentalGroup A.CentralFamily A.cuspCentralBase :=
  A.markedCentralToActualCuspEquiv A.markedZeroCentralMeridianClass⁻¹

/-- The second finite core meridian is the counterclockwise zero-section meridian, transported to
the actual cusp basepoint. -/
public noncomputable def geometricCentralRhoTwo :
    FundamentalGroup A.CentralFamily A.cuspCentralBase :=
  A.markedCentralToActualCuspEquiv A.markedOneCentralMeridianClass⁻¹

/-- The actual cusp meridian is exactly the product of the two concrete finite core meridians. -/
public theorem cuspCentralMeridian_eq_geometricRhoProduct :
    A.cuspCentralMeridian =
      A.geometricCentralRhoOne * A.geometricCentralRhoTwo := by
  rw [A.cuspCentralMeridian_eq_angularLoop]
  have h := congrArg A.markedCentralToActualCuspEquiv
    A.cuspMarkedCentralLoop_class_eq_finiteProduct
  rw [map_mul] at h
  change A.markedCentralToActualCuspEquiv
      (Path.Homotopic.Quotient.mk A.cuspMarkedCentralLoop) =
    A.geometricCentralRhoOne * A.geometricCentralRhoTwo at h
  have hwhisker :
      A.markedCentralToActualCuspEquiv.symm
          (Path.Homotopic.Quotient.mk A.cuspAngularCentralLoop) =
        Path.Homotopic.Quotient.mk A.cuspMarkedCentralLoop := by
    rfl
  calc
    Path.Homotopic.Quotient.mk A.cuspAngularCentralLoop =
        A.markedCentralToActualCuspEquiv
          (Path.Homotopic.Quotient.mk A.cuspMarkedCentralLoop) := by
      rw [← hwhisker,
        A.markedCentralToActualCuspEquiv.apply_symm_apply]
    _ = A.geometricCentralRhoOne * A.geometricCentralRhoTwo := h

end SphereSixComplex.Geometry.PaperAnalyticData

end
