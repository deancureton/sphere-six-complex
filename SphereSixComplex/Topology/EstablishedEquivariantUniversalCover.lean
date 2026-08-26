module

public import SphereSixComplex.Topology.EstablishedEquivariantUniversalCoverProof
public import SphereSixComplex.Periods.FuchsianUniformizationBridge

/-!
# The Fuchsian pair-of-pants classification boundary

The definitions of the two-meridian deck group, the affine deck extension and the equivariant
affine universal cover are in `EstablishedEquivariantUniversalCoverDefs`, and are re-exported
here, so every module path using them is unchanged.

This module records the one remaining classification input for the paper's punctured global
family and derives the equivariant universal cover from it.

## What is assumed, and why in this form

The retained input is `establishedPuncturedGlobalFamilyAffineFundamentalGroup`: the punctured
global family is locally nice and its fundamental group is the affine deck group
`IntegerPeriods ⋊ FreeGroup (Fin 2)`, the two free meridians acting by the order-three and
order-four integral period monodromies.  The equivariant universal cover itself is then a
theorem, `establishedPuncturedGlobalFamilyEquivariantUniversalCover`, obtained from Tau Ceti's
based-path universal cover in `EstablishedEquivariantUniversalCoverProof`.

Two changes from the earlier form of this boundary are deliberate.

* The covering space is no longer assumed.  A simply connected quotient covering already forces
  the fundamental group of the base to be the acting group, so postulating the cover and
  postulating the group are equivalent; only the latter is a statement one can check.
* The source uniformization is no longer arbitrary.  A bare `TriangleUniformization` records a
  homomorphism `Delta →* Equiv.Perm UpperHalfPlane` acting holomorphically, hence by Moebius
  transformations, but it does not require that image to be discrete, and discreteness is exactly
  what makes the regular locus a covering of a twice-punctured disc with free meridian
  fundamental group.  The input is therefore taken on a `Periods.FuchsianModularParameter`, whose
  `toTriangleUniformization` has `sourceAction = fuchsianSourceAction` by definition.  This is the
  only case that occurs: `PaperAnalyticData.centralAffineUniversalCover` instantiates it at
  `A.modular.modularParameter`.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex

namespace Geometry.GlobalTorusFamily

open Periods TriangleGroup Geometry.ComplexTorus

/-- The standard punctured-Fuchsian classification, in its fundamental-group form.

For a Fuchsian modular parameter, the regular locus of the uniformizing half-plane covers a
twice-punctured disc, so the punctured global family is an affine torus bundle over a pair of
pants: its fundamental group is the lattice extended by the free group on the two meridians,
which map to the order-three and order-four orbifold generators.  No covering space, filling
relation or van Kampen conclusion is asserted. -/
public axiom establishedPuncturedGlobalFamilyAffineFundamentalGroup
    {P : Periods.FuchsianModularParameter}
    (F : PeriodFunctions P.toTriangleUniformization) :
    PuncturedGlobalFamilyAffineFundamentalGroup F

/-- The equivariant universal-cover classification for a punctured Fuchsian affine torus family.

This is now a theorem: the affine fundamental-group identification above is transported onto
Tau Ceti's based-path universal cover, which is simply connected and whose fundamental-group
action is a quotient covering map.  The conclusion supplies only the universal cover and its
affine deck action. -/
public noncomputable def establishedPuncturedGlobalFamilyEquivariantUniversalCover
    {P : Periods.FuchsianModularParameter}
    (F : PeriodFunctions P.toTriangleUniformization) :
    ChosenEquivariantAffineUniversalCover IntegerPeriods Delta (PuncturedGlobalFamily F)
      (twoMeridianOrbifoldMap g₁ g₂) integralOrbifoldPeriodMonodromy :=
  puncturedGlobalFamilyEquivariantUniversalCover_of_fundamentalGroup F
    (establishedPuncturedGlobalFamilyAffineFundamentalGroup F)

end Geometry.GlobalTorusFamily

end SphereSixComplex

end
