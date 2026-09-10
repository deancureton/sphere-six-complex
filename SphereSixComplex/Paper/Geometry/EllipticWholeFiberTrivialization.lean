module

public import SphereSixComplex.Paper.Geometry.EllipticLocalTrivialization
public import SphereSixComplex.Prerequisites.Geometry.PartialDiffeomorphGluing

/-!
# Whole-fibre elliptic trivializations

This file isolates the precise gluing input that is not supplied by pointwise quotient charts.
Compatible local analytic representatives glue to a partial diffeomorphism on one open
neighbourhood.  Restricting its target away from the central fibre gives the collar used for an
elliptic filling.
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry.EllipticWholeFiberTrivialization

open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLocalTrivialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods

noncomputable section

universe u v w

section ActualEllipticFamilies

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- A family deck map as a permutation of the actual varying-lattice quotient. -/
@[expose] public noncomputable def familyDeckEquiv (g : Delta) :
    Equiv.Perm (TotalSpace (parameterMap F)) where
  toFun := familyDeckMap F g
  invFun := familyDeckMap F g⁻¹
  left_inv x := by
    rw [← familyDeckMap_mul, inv_mul_cancel, familyDeckMap_one]
  right_inv x := by
    rw [← familyDeckMap_mul, mul_inv_cancel, familyDeckMap_one]

@[simp]
public theorem familyDeckEquiv_apply (g : Delta) (x : TotalSpace (parameterMap F)) :
    familyDeckEquiv F g x = familyDeckMap F g x :=
  rfl

/-- The order-three subgroup acting on the actual torus family. -/
@[expose] public noncomputable def familyDeckRepresentation :
    Delta →* Equiv.Perm (TotalSpace (parameterMap F)) where
  toFun := familyDeckEquiv F
  map_one' := by
    apply Equiv.ext
    exact familyDeckMap_one F
  map_mul' := by
    intro g h
    apply Equiv.ext
    exact familyDeckMap_mul F g h

/-- The order-three subgroup acting on the actual torus family. -/
@[expose] public noncomputable def orderThreeFamilyRepresentation :
    FiniteCyclic 3 →* Equiv.Perm (TotalSpace (parameterMap F)) :=
  (familyDeckRepresentation F).comp
    (Monoid.Coprod.inl : FiniteCyclic 3 →* Delta)

/-- The order-four subgroup acting on the actual torus family. -/
@[expose] public noncomputable def orderFourFamilyRepresentation :
    FiniteCyclic 4 →* Equiv.Perm (TotalSpace (parameterMap F)) :=
  (familyDeckRepresentation F).comp
    (Monoid.Coprod.inr : FiniteCyclic 4 →* Delta)

/-- The product with the actual fixed order-three period torus. -/
public abbrev OrderThreeFixedProduct :=
  ComplexUnitDisc × AdditiveTorus (parameterMap F U.zOne).1

/-- The product with the actual fixed order-four period torus. -/
public abbrev OrderFourFixedProduct :=
  ComplexUnitDisc × AdditiveTorus (parameterMap F U.zTwo).1

/-- Quotient the vector coordinate by the fixed order-three period lattice. -/
@[expose] public def orderThreeFixedProductProjection
    (p : ComplexUnitDisc × ComplexTwoSpace) : OrderThreeFixedProduct F :=
  (p.1, Quotient.mk _ p.2)

/-- Quotient the vector coordinate by the fixed order-four period lattice. -/
@[expose] public def orderFourFixedProductProjection
    (p : ComplexUnitDisc × ComplexTwoSpace) : OrderFourFixedProduct F :=
  (p.1, Quotient.mk _ p.2)

section PointwiseCandidates

variable [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]

/-- The fixed-torus-valued map supplied at one point of the order-three fibre by the proven local
analytic lift and the Cayley biholomorphism. -/
@[expose] public noncomputable def orderThreePointwiseProductMap
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    TotalSpace (parameterMap F) → OrderThreeFixedProduct F := fun q ↦
  orderThreeFixedProductProjection F
    (orderThreeCoverDiffeomorph ω (orderThreeLocalLift F hprojection v q))

/-- The analogous fixed-torus-valued pointwise map at the order-four fibre. -/
@[expose] public noncomputable def orderFourPointwiseProductMap
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (v : ComplexTwoSpace) :
    TotalSpace (parameterMap F) → OrderFourFixedProduct F := fun q ↦
  orderFourFixedProductProjection F
    (orderFourCoverDiffeomorph ω (orderFourLocalLift F hprojection v q))

@[simp]
public theorem orderThreePointwiseProductMap_center
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (hzOne : U.zOne = fuchsianOneFixedPoint)
    (v : ComplexTwoSpace) :
    orderThreePointwiseProductMap F hprojection v
        (projection (parameterMap F) (U.zOne, v)) =
      (ComplexUnitDisc.center, Quotient.mk _ v) := by
  rw [orderThreePointwiseProductMap,
    orderThreeCayleyLocalChart_center F hprojection hzOne]
  rfl

@[simp]
public theorem orderFourPointwiseProductMap_center
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (hzTwo : U.zTwo = fuchsianTwoFixedPoint)
    (v : ComplexTwoSpace) :
    orderFourPointwiseProductMap F hprojection v
        (projection (parameterMap F) (U.zTwo, v)) =
      (ComplexUnitDisc.center, Quotient.mk _ v) := by
  rw [orderFourPointwiseProductMap,
    orderFourCayleyLocalChart_center F hprojection hzTwo]
  rfl

end PointwiseCandidates

section WholeFiberObligations

variable [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
variable [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderThreeFixedProduct F)]
variable [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderFourFixedProduct F)]

/-- The exact remaining order-three whole-fibre input.  Its analytic content is local chart
compatibility, while `pointwise_agreement` requires the glued map to be the map already constructed
from the quotient local inverse and the fixed-lattice projection. -/
public structure OrderThreeWholeFiberCompatibility
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) where
  /-- Indexing type for the compatible pointwise charts. -/
  Index : Type
  /-- The compatible charts and their glued source and target neighbourhoods. -/
  gluing : CompatiblePartialDiffeomorphs Index globalDeckTotalModel
    (TotalSpace (parameterMap F)) (OrderThreeFixedProduct F) ω
  /-- The glued source contains the entire order-three fibre. -/
  contains_source_fibre : ∀ v : ComplexTwoSpace,
    projection (parameterMap F) (U.zOne, v) ∈ gluing.source
  /-- The glued target contains the entire central fixed torus. -/
  contains_target_fibre : ∀ x : AdditiveTorus (parameterMap F U.zOne).1,
    (ComplexUnitDisc.center, x) ∈ gluing.target
  /-- Each local chart agrees near its centre with the constructed pointwise candidate. -/
  pointwise_agreement : ∀ v : ComplexTwoSpace,
    gluing.toFun =ᶠ[nhdsWithin
      (projection (parameterMap F) (U.zOne, v)) gluing.source]
      orderThreePointwiseProductMap F hprojection v
  /-- The glued map has the prescribed value at every point of the central fibre. -/
  pointwise_value : ∀ v : ComplexTwoSpace,
    gluing.toFun (projection (parameterMap F) (U.zOne, v)) =
      orderThreePointwiseProductMap F hprojection v
        (projection (parameterMap F) (U.zOne, v))
  /-- The source neighbourhood is invariant under the order-three family action. -/
  source_invariant : ∀ g : FiniteCyclic 3,
    MapsTo (orderThreeFamilyRepresentation F g) gluing.source gluing.source
  /-- The target neighbourhood is invariant under the fixed-fibre action. -/
  target_invariant : ∀ g : FiniteCyclic 3,
    MapsTo ((orderThreeActionData F).representation g) gluing.target gluing.target
  /-- The glued map intertwines the source and target cyclic actions. -/
  equivariant : ∀ g : FiniteCyclic 3, Set.EqOn
    (gluing.toFun ∘ orderThreeFamilyRepresentation F g)
    ((orderThreeActionData F).representation g ∘ gluing.toFun) gluing.source

/-- The exact analogous order-four compatibility input. -/
public structure OrderFourWholeFiberCompatibility
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) where
  /-- Indexing type for the compatible pointwise charts. -/
  Index : Type
  /-- The compatible charts and their glued source and target neighbourhoods. -/
  gluing : CompatiblePartialDiffeomorphs Index globalDeckTotalModel
    (TotalSpace (parameterMap F)) (OrderFourFixedProduct F) ω
  /-- The glued source contains the entire order-four fibre. -/
  contains_source_fibre : ∀ v : ComplexTwoSpace,
    projection (parameterMap F) (U.zTwo, v) ∈ gluing.source
  /-- The glued target contains the entire central fixed torus. -/
  contains_target_fibre : ∀ x : AdditiveTorus (parameterMap F U.zTwo).1,
    (ComplexUnitDisc.center, x) ∈ gluing.target
  /-- Each local chart agrees near its centre with the constructed pointwise candidate. -/
  pointwise_agreement : ∀ v : ComplexTwoSpace,
    gluing.toFun =ᶠ[nhdsWithin
      (projection (parameterMap F) (U.zTwo, v)) gluing.source]
      orderFourPointwiseProductMap F hprojection v
  /-- The glued map has the prescribed value at every point of the central fibre. -/
  pointwise_value : ∀ v : ComplexTwoSpace,
    gluing.toFun (projection (parameterMap F) (U.zTwo, v)) =
      orderFourPointwiseProductMap F hprojection v
        (projection (parameterMap F) (U.zTwo, v))
  /-- The source neighbourhood is invariant under the order-four family action. -/
  source_invariant : ∀ g : FiniteCyclic 4,
    MapsTo (orderFourFamilyRepresentation F g) gluing.source gluing.source
  /-- The target neighbourhood is invariant under the fixed-fibre action. -/
  target_invariant : ∀ g : FiniteCyclic 4,
    MapsTo ((orderFourActionData F).representation g) gluing.target gluing.target
  /-- The glued map intertwines the source and target cyclic actions. -/
  equivariant : ∀ g : FiniteCyclic 4, Set.EqOn
    (gluing.toFun ∘ orderFourFamilyRepresentation F g)
    ((orderFourActionData F).representation g ∘ gluing.toFun) gluing.source

namespace OrderThreeWholeFiberCompatibility

variable {F} {hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
    (projection (parameterMap F))}
    (D : OrderThreeWholeFiberCompatibility F hprojection)

/-- The order-three obligation instantiates the generic equivariant gluing theorem. -/
@[expose] public noncomputable def toEquivariantCompatibility :
    EquivariantWholeFiberCompatibility (FiniteCyclic 3) D.Index globalDeckTotalModel
      (TotalSpace (parameterMap F)) (OrderThreeFixedProduct F) ω where
  gluing := D.gluing
  sourceRepresentation := orderThreeFamilyRepresentation F
  targetRepresentation := (orderThreeActionData F).representation
  source_invariant := D.source_invariant
  target_invariant := D.target_invariant
  equivariant := D.equivariant

/-- The resulting analytic trivialization on one neighbourhood of the entire order-three fibre. -/
@[expose] public noncomputable def trivialization :
    PartialDiffeomorph globalDeckTotalModel globalDeckTotalModel
      (TotalSpace (parameterMap F)) (OrderThreeFixedProduct F) ω :=
  D.gluing.toPartialDiffeomorph

omit [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderFourFixedProduct F)] in
public theorem trivialization_equivariant (g : FiniteCyclic 3) : Set.EqOn
    (D.trivialization ∘ orderThreeFamilyRepresentation F g)
    ((orderThreeActionData F).representation g ∘ D.trivialization) D.gluing.source :=
  D.toEquivariantCompatibility.toPartialDiffeomorph_equivariant g

omit [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderFourFixedProduct F)] in
public theorem maps_central_fibre
    (hzOne : U.zOne = fuchsianOneFixedPoint) (v : ComplexTwoSpace) :
    D.trivialization (projection (parameterMap F) (U.zOne, v)) =
      (ComplexUnitDisc.center, Quotient.mk _ v) := by
  change D.gluing.toFun (projection (parameterMap F) (U.zOne, v)) = _
  rw [D.pointwise_value,
    orderThreePointwiseProductMap_center F hprojection hzOne]

/-- The punctured restriction is the collar identification consumed by the filling. -/
@[expose] public noncomputable def collar :
    OpenPartialHomeomorph (TotalSpace (parameterMap F)) (OrderThreeFixedProduct F) :=
  collarOpenPartialHomeomorph D.gluing

omit [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderFourFixedProduct F)] in
public theorem collar_target : D.collar.target ⊆
    puncturedDiscProduct (AdditiveTorus (parameterMap F U.zOne).1) :=
  collar_target_subset_puncturedDiscProduct D.gluing

end OrderThreeWholeFiberCompatibility

namespace OrderFourWholeFiberCompatibility

variable {F} {hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
    (projection (parameterMap F))}
    (D : OrderFourWholeFiberCompatibility F hprojection)

@[expose] public noncomputable def toEquivariantCompatibility :
    EquivariantWholeFiberCompatibility (FiniteCyclic 4) D.Index globalDeckTotalModel
      (TotalSpace (parameterMap F)) (OrderFourFixedProduct F) ω where
  gluing := D.gluing
  sourceRepresentation := orderFourFamilyRepresentation F
  targetRepresentation := (orderFourActionData F).representation
  source_invariant := D.source_invariant
  target_invariant := D.target_invariant
  equivariant := D.equivariant

@[expose] public noncomputable def trivialization :
    PartialDiffeomorph globalDeckTotalModel globalDeckTotalModel
      (TotalSpace (parameterMap F)) (OrderFourFixedProduct F) ω :=
  D.gluing.toPartialDiffeomorph

omit [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderThreeFixedProduct F)] in
public theorem trivialization_equivariant (g : FiniteCyclic 4) : Set.EqOn
    (D.trivialization ∘ orderFourFamilyRepresentation F g)
    ((orderFourActionData F).representation g ∘ D.trivialization) D.gluing.source :=
  D.toEquivariantCompatibility.toPartialDiffeomorph_equivariant g

omit [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderThreeFixedProduct F)] in
public theorem maps_central_fibre
    (hzTwo : U.zTwo = fuchsianTwoFixedPoint) (v : ComplexTwoSpace) :
    D.trivialization (projection (parameterMap F) (U.zTwo, v)) =
      (ComplexUnitDisc.center, Quotient.mk _ v) := by
  change D.gluing.toFun (projection (parameterMap F) (U.zTwo, v)) = _
  rw [D.pointwise_value,
    orderFourPointwiseProductMap_center F hprojection hzTwo]

@[expose] public noncomputable def collar :
    OpenPartialHomeomorph (TotalSpace (parameterMap F)) (OrderFourFixedProduct F) :=
  collarOpenPartialHomeomorph D.gluing

omit [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (OrderThreeFixedProduct F)] in
public theorem collar_target : D.collar.target ⊆
    puncturedDiscProduct (AdditiveTorus (parameterMap F U.zTwo).1) :=
  collar_target_subset_puncturedDiscProduct D.gluing

end OrderFourWholeFiberCompatibility

end WholeFiberObligations

end ActualEllipticFamilies

end

end SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
