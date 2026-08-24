module

public import SphereSixComplex.Topology.HomogeneousCovering
import all SphereSixComplex.Topology.HomogeneousCovering
public import SphereSixComplex.Periods.FuchsianModularParameterExistence
import all SphereSixComplex.Periods.FuchsianModularParameterExistence
public import SphereSixComplex.TriangleGroup.FuchsianSmoothAction
import all SphereSixComplex.TriangleGroup.FuchsianSmoothAction
public import Mathlib.Geometry.Manifold.Notation
import all Mathlib.Geometry.Manifold.Notation

@[expose] public section

/-!
# Assembly of an exact source orbifold coordinate

This file packages the consequences which do not need any further Schwarz-triangle analysis.
Once a global invariant holomorphic coordinate has been constructed, openness and surjectivity
give the quotient-map field, while exact orbit fibres and the source deck action turn a local
homeomorphism on the ordinary locus into a covering map.
-/

open Set Topology
open scoped Manifold MatrixGroups

noncomputable section

namespace SphereSixComplex.Periods.ExactSourceAssembly

open SphereSixComplex.TriangleGroup

/-- The ordinary-value locus of a normalized `(3,4,∞)` coordinate. -/
def sourceRegularValueSet : Set ℂ := ({0, 1} : Set ℂ)ᶜ

/-- The analytic and fibre data left after deriving quotientness and the regular covering
formally.  The Schwarz-reflection construction is expected to produce precisely this package. -/
structure SourceCoordinateCore where
  coordinate : UpperHalfPlane → ℂ
  coordinate_holomorphic : MDiff coordinate
  coordinate_invariant : ∀ g z,
    coordinate (fuchsianSourceAction g • z) = coordinate z
  coordinate_surjective : Function.Surjective coordinate
  coordinate_isOpenMap : IsOpenMap coordinate
  coordinate_eq_iff_orbit : ∀ z w,
    coordinate z = coordinate w ↔
      ∃ g : Delta, fuchsianSourceAction g • z = w
  coordinate_at_one : coordinate fuchsianOneFixedPoint = 0
  coordinate_at_two : coordinate fuchsianTwoFixedPoint = 1
  regular_localHomeomorph :
    IsLocalHomeomorph (sourceRegularValueSet.restrictPreimage coordinate)
  branch_one : HasExactHolomorphicBranchAt coordinate fuchsianOneFixedPoint 0 3
  branch_two : HasExactHolomorphicBranchAt coordinate fuchsianTwoFixedPoint 1 4
  cusp : HasExactFuchsianCusp
    { coordinate := coordinate
      coordinate_holomorphic := coordinate_holomorphic
      coordinate_invariant := coordinate_invariant }

namespace SourceCoordinateCore

variable (K : SourceCoordinateCore)

/-- The source action restricted to the inverse image of the ordinary-value locus. -/
def regularDeckHomeomorph (g : Delta) :
    K.coordinate ⁻¹' sourceRegularValueSet ≃ₜ
      K.coordinate ⁻¹' sourceRegularValueSet where
  toFun z := ⟨fuchsianSourceAction g • z.1, by
    change K.coordinate (fuchsianSourceAction g • z.1) ∈ sourceRegularValueSet
    have hz := z.2
    change K.coordinate z.1 ∈ sourceRegularValueSet at hz
    simpa only [K.coordinate_invariant] using hz
    ⟩
  invFun z := ⟨fuchsianSourceAction g⁻¹ • z.1, by
    change K.coordinate (fuchsianSourceAction g⁻¹ • z.1) ∈ sourceRegularValueSet
    have hz := z.2
    change K.coordinate z.1 ∈ sourceRegularValueSet at hz
    simpa only [K.coordinate_invariant] using hz
    ⟩
  left_inv z := by
    apply Subtype.ext
    change fuchsianSourceAction g⁻¹ • (fuchsianSourceAction g • z.1) = z.1
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  right_inv z := by
    apply Subtype.ext
    change fuchsianSourceAction g • (fuchsianSourceAction g⁻¹ • z.1) = z.1
    rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (fuchsianSourceAction_contMDiff g 0).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (fuchsianSourceAction_contMDiff g⁻¹ 0).continuous.comp continuous_subtype_val

theorem regularDeckHomeomorph_fiber (g : Delta)
    (z : K.coordinate ⁻¹' sourceRegularValueSet) :
    sourceRegularValueSet.restrictPreimage K.coordinate
        (K.regularDeckHomeomorph g z) =
      sourceRegularValueSet.restrictPreimage K.coordinate z := by
  apply Subtype.ext
  exact K.coordinate_invariant g z.1

theorem regularDeckHomeomorph_transitive
    (z w : K.coordinate ⁻¹' sourceRegularValueSet)
    (hzw : sourceRegularValueSet.restrictPreimage K.coordinate z =
      sourceRegularValueSet.restrictPreimage K.coordinate w) :
    ∃ g : Delta, K.regularDeckHomeomorph g z = w := by
  have hcoord : K.coordinate z.1 = K.coordinate w.1 := congrArg Subtype.val hzw
  obtain ⟨g, hg⟩ := (K.coordinate_eq_iff_orbit z.1 w.1).mp hcoord
  refine ⟨g, ?_⟩
  apply Subtype.ext
  exact hg

theorem regularCoordinate_surjective :
    Function.Surjective
      (sourceRegularValueSet.restrictPreimage K.coordinate) := by
  intro y
  obtain ⟨z, hz⟩ := K.coordinate_surjective y.1
  refine ⟨⟨z, ?_⟩, ?_⟩
  · change K.coordinate z ∈ sourceRegularValueSet
    simpa only [hz] using y.2
  · apply Subtype.ext
    exact hz

/-- Exact orbit fibres upgrade local conformality on the ordinary locus to a genuine covering. -/
theorem regularCoordinate_isCoveringMap :
    IsCoveringMap (sourceRegularValueSet.restrictPreimage K.coordinate) := by
  letI : LocallyConnectedSpace sourceRegularValueSet :=
    (show IsOpen sourceRegularValueSet by
      exact isOpen_compl_iff.mpr (isClosed_singleton.union isClosed_singleton)
      ).locallyConnectedSpace
  exact Topology.isCoveringMap_of_deck_transitive
    (sourceRegularValueSet.restrictPreimage K.coordinate)
    K.regular_localHomeomorph
    (T2Space.isSeparatedMap _)
    K.regularCoordinate_surjective
    K.regularDeckHomeomorph
    K.regularDeckHomeomorph_fiber
    K.regularDeckHomeomorph_transitive

/-- Assemble the paper's exact source-coordinate contract from the reduced core. -/
def toExactFuchsianOrbifoldCoordinate : ExactFuchsianOrbifoldCoordinate where
  coordinate := K.coordinate
  coordinate_holomorphic := K.coordinate_holomorphic
  coordinate_invariant := K.coordinate_invariant
  coordinate_isQuotientMap :=
    K.coordinate_isOpenMap.isQuotientMap
      K.coordinate_holomorphic.continuous K.coordinate_surjective
  coordinate_eq_iff_orbit := K.coordinate_eq_iff_orbit
  coordinate_at_one := K.coordinate_at_one
  coordinate_at_two := K.coordinate_at_two
  regular_covering := by
    apply IsCoveringMapOn.of_isCoveringMap_restrictPreimage
    · exact isOpen_compl_iff.mpr (isClosed_singleton.union isClosed_singleton)
    · exact (isOpen_compl_iff.mpr (isClosed_singleton.union isClosed_singleton)).preimage
        K.coordinate_holomorphic.continuous
    · exact K.regularCoordinate_isCoveringMap
  branch_one := K.branch_one
  branch_two := K.branch_two
  cusp := K.cusp


end SourceCoordinateCore

end SphereSixComplex.Periods.ExactSourceAssembly
