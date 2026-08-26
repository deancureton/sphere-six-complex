module

public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularBaseDeckCover

/-!
# Equivariant homotopy transport in the regular torus family

The affine coordinate covering canonically lifts invariant radial homotopies to the regular
base.  Lifting those base homotopies further through the varying-torus family is a separate
bundle-homotopy statement; its exact data is isolated here without asserting a product
trivialization of the quotient family.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
open SphereSixComplex.Geometry.GlobalTorusFamily

universe u

variable (A : PaperAnalyticData)

/-- The canonical lift of an invariant coordinate homotopy is equivariant for the full
triangle-group deck action on the regular base. -/
public theorem regularCoordinate_liftHomotopy_equivariant
    {B : Type u} [TopologicalSpace B]
    (parameterAction : MulAction Delta B)
    (H : C(unitInterval × B, RegularCoordinateBase))
    (f : C(B, RegularBase
      (U := A.modular.modularParameter.toTriangleUniformization)))
    (H0 : ∀ b, H (0, b) = A.regularCoordinate (f b))
    (H_invariant : ∀ g t b,
      H (t, actionMap parameterAction g b) = H (t, b))
    (f_equivariant : ∀ g b, f (actionMap parameterAction g b) =
      actionMap A.regularBaseDeckAction g (f b)) :
    ∀ g t b,
      A.regularCoordinate_isCoveringMap.liftHomotopy H f H0
          (t, actionMap parameterAction g b) =
        actionMap A.regularBaseDeckAction g
          (A.regularCoordinate_isCoveringMap.liftHomotopy H f H0 (t, b)) := by
  exact A.regularCoordinate_isCoveringMap.liftHomotopy_equivariant
    A.regularBaseDeckAction parameterAction
    A.regularBaseDeckAction_continuous
    A.regularCoordinate_deck_invariant
    H f H0 H_invariant f_equivariant

/-- Exact output of lifting a regular-base homotopy through the varying-torus family.  The
projection, initial value, and full-deck equivariance are recorded explicitly. -/
public structure EquivariantRegularFamilyHomotopyLiftData
    {B : Type u} [TopologicalSpace B]
    (parameterAction : MulAction Delta B)
    (baseHomotopy : C(unitInterval × B,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)))
    (initialLift : C(B, RegularTotalSpace A.periods)) where
  lift : C(unitInterval × B, RegularTotalSpace A.periods)
  projects : ∀ t b,
    regularTotalSpaceBase A.periods (lift (t, b)) = baseHomotopy (t, b)
  zero : ∀ b, lift (0, b) = initialLift b
  equivariant : ∀ g t b,
    lift (t, actionMap parameterAction g b) =
      actionMap (regularFamilyDeckAction A.periods) g (lift (t, b))

/-- The precise fibre-bundle homotopy-lifting property still needed for the affine radial
argument.  It asks for a deck-equivariant lift only when the base homotopy and its initial
total-space lift already satisfy the corresponding equivariance and projection equations. -/
public structure RegularFamilyEquivariantHomotopyLiftingProperty where
  liftHomotopy : ∀ {B : Type u} [TopologicalSpace B]
    (parameterAction : MulAction Delta B)
    (baseHomotopy : C(unitInterval × B,
      RegularBase (U := A.modular.modularParameter.toTriangleUniformization)))
    (initialLift : C(B, RegularTotalSpace A.periods)),
    (∀ b, baseHomotopy (0, b) =
      regularTotalSpaceBase A.periods (initialLift b)) →
    (∀ g t b, baseHomotopy (t, actionMap parameterAction g b) =
      actionMap A.regularBaseDeckAction g (baseHomotopy (t, b))) →
    (∀ g b, initialLift (actionMap parameterAction g b) =
      actionMap (regularFamilyDeckAction A.periods) g (initialLift b)) →
    A.EquivariantRegularFamilyHomotopyLiftData parameterAction baseHomotopy initialLift

end SphereSixComplex.Geometry.PaperAnalyticData
