module

public import SphereSixComplex.Topology.EquivariantCoveringHomotopyLift
public import SphereSixComplex.Geometry.PaperCentralCompactCore

/-!
# The full-deck regular-base covering for affine radial lifts

This module installs the triangle-group action on the regular base and records that the affine
coordinate is an invariant covering projection.  The equivariant homotopy-lifting theorem then
applies directly to radial homotopies in the twice-punctured affine coordinate line.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.GlobalTorusFamily

variable (A : PaperAnalyticData)

/-- The affine coordinate on the regular base is the exact full-deck covering, transported
through the regular-base preimage homeomorphism. -/
public theorem regularCoordinate_isCoveringMap :
    IsCoveringMap A.regularCoordinate := by
  let e := A.regularBaseCoordinatePreimageHomeomorph
  let f := ({0, 1} : Set ℂ)ᶜ.restrictPreimage
    A.modular.sourceCoordinate.coordinate
  have hf : IsCoveringMap f :=
    A.modular.sourceCoordinate.regular_covering.isCoveringMap_restrictPreimage
  have hcomp : IsCoveringMap (f ∘ e) := hf.comp_homeomorph e
  convert hcomp using 1
  rfl

/-- The triangle-group action on the regular upper-half-plane base. -/
public noncomputable abbrev regularBaseDeckAction : MulAction Delta
    (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
  SphereSixComplex.TriangleGroup.FuchsianProperFreeness.regularSourceMulAction
    A.modular.modularParameter.toTriangleUniformization

public theorem regularBaseDeckAction_continuous :
    letI := A.regularBaseDeckAction
    ContinuousConstSMul Delta
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) := by
  let _ := A.regularBaseDeckAction
  constructor
  intro g
  change Continuous (regularSourceEquiv g)
  apply Continuous.subtype_mk
  exact (fuchsianSourceAction_contMDiff g 0).continuous.comp continuous_subtype_val

/-- The affine coordinate is invariant under every regular-base deck transformation. -/
public theorem regularCoordinate_deck_invariant (g : Delta)
    (z : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    A.regularCoordinate (actionMap A.regularBaseDeckAction g z) =
      A.regularCoordinate z := by
  apply Subtype.ext
  change A.modular.sourceCoordinate.coordinate
    (fuchsianSourceAction g • z.1) =
      A.modular.sourceCoordinate.coordinate z.1
  exact A.modular.sourceCoordinate.coordinate_invariant g z.1

end SphereSixComplex.Geometry.PaperAnalyticData
