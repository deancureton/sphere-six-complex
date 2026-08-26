module

public import SphereSixComplex.Geometry.EllipticLogarithmicGauge
public import SphereSixComplex.Geometry.EquivariantQuotientHomeomorph
import all SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
import all SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient

/-!
# Quotient descent for the elliptic logarithmic gauges

Compatible local logarithm branches give a single torus-valued gauge after branch changes are
identified by lattice periods.  This file isolates the exact remaining gluing data for that
gauge and proves that it descends from the affine cyclic collar quotient to the linear cyclic
collar quotient.  It does not posit a global logarithm on a punctured disc or identify either
local quotient with a paper-specific space.
-/

namespace SphereSixComplex.Geometry.EllipticLogarithmicGaugeDescent

open Set
open SphereSixComplex.Geometry SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticLogarithmicGauge
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- The order-three linear cyclic action obtained by restricting the global deck action. -/
@[expose, instance_reducible] public noncomputable def orderThreeLinearFamilyAction :
    MulAction (FiniteCyclic 3) (TotalSpace (parameterMap F)) where
  smul g q := orderThreeFamilyRepresentation F g q
  one_smul q := by
    change orderThreeFamilyRepresentation F 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    change orderThreeFamilyRepresentation F (g * h) q =
      orderThreeFamilyRepresentation F g (orderThreeFamilyRepresentation F h q)
    rw [map_mul]
    rfl

/-- The order-four linear cyclic action obtained by restricting the global deck action. -/
@[expose, instance_reducible] public noncomputable def orderFourLinearFamilyAction :
    MulAction (FiniteCyclic 4) (TotalSpace (parameterMap F)) where
  smul g q := orderFourFamilyRepresentation F g q
  one_smul q := by
    change orderFourFamilyRepresentation F 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    change orderFourFamilyRepresentation F (g * h) q =
      orderFourFamilyRepresentation F g (orderFourFamilyRepresentation F h q)
    rw [map_mul]
    rfl

public theorem orderThreeAffine_smulOf_generator
    (q : TotalSpace (parameterMap F)) :
    smulOf (orderThreeAffineFamilyAction F) (cyclicGenerator 3) q =
      orderThreeAffineFamilyGenerator F q := by
  rw [smulOf.eq_def]
  change orderThreeAffineFamilyRepresentation F (cyclicGenerator 3) q = _
  rw [orderThreeAffineFamilyRepresentation.eq_def, cyclicGenerator.eq_def,
    cyclicRepresentation_generator]

public theorem orderFourAffine_smulOf_generator
    (q : TotalSpace (parameterMap F)) :
    smulOf (orderFourAffineFamilyAction F) (cyclicGenerator 4) q =
      orderFourAffineFamilyGenerator F q := by
  rw [smulOf.eq_def]
  change orderFourAffineFamilyRepresentation F (cyclicGenerator 4) q = _
  rw [orderFourAffineFamilyRepresentation.eq_def, cyclicGenerator.eq_def,
    cyclicRepresentation_generator]

public theorem orderThreeLinear_smulOf_generator
    (q : TotalSpace (parameterMap F)) :
    smulOf (orderThreeLinearFamilyAction F) (cyclicGenerator 3) q =
      familyDeckMap F g₁ q := by
  rw [smulOf.eq_def]
  change orderThreeFamilyRepresentation F (cyclicGenerator 3) q = _
  rw [orderThreeFamilyRepresentation, SphereSixComplex.TriangleGroup.g₁.eq_def]
  rfl

public theorem orderFourLinear_smulOf_generator
    (q : TotalSpace (parameterMap F)) :
    smulOf (orderFourLinearFamilyAction F) (cyclicGenerator 4) q =
      familyDeckMap F g₂ q := by
  rw [smulOf.eq_def]
  change orderFourFamilyRepresentation F (cyclicGenerator 4) q = _
  rw [orderFourFamilyRepresentation, SphereSixComplex.TriangleGroup.g₂.eq_def]
  rfl

/-- Exact local data needed to glue the order-three logarithmic gauge on an invariant branch
carrier.  The two formulas say that the same torus-valued homeomorphism is represented by the
source branch before applying the generator and by the rotated branch afterwards. -/
public structure OrderThreeLogarithmicGaugeDescentData
    (r : ℝ) (B : RotatedLogBranches 3 orderThreeDiscRotation) where
  source : OpenSubMulAction (orderThreeAffineFamilyAction F)
  target : OpenSubMulAction (orderThreeLinearFamilyAction F)
  gaugeHomeomorph : source ≃ₜ target
  branch_covered : ∀ q : source,
    (q : TotalSpace (parameterMap F)) ∈ orderThreeLogarithmicGaugeCarrier F r B
  source_formula : ∀ q : source,
    (gaugeHomeomorph q : TotalSpace (parameterMap F)) =
      orderThreeLogarithmicGaugeMap F (fun w => B.source.log w) q
  rotated_formula : ∀ q : source,
    (gaugeHomeomorph
        (cyclicGenerator 3 • q) :
      TotalSpace (parameterMap F)) =
      orderThreeLogarithmicGaugeMap F (fun w => B.target.log w)
        ((cyclicGenerator 3 • q : source) : TotalSpace (parameterMap F))

/-- Exact analogous gluing data for the order-four logarithmic gauge. -/
public structure OrderFourLogarithmicGaugeDescentData
    (r : ℝ) (B : RotatedLogBranches 4 orderFourDiscRotation) where
  source : OpenSubMulAction (orderFourAffineFamilyAction F)
  target : OpenSubMulAction (orderFourLinearFamilyAction F)
  gaugeHomeomorph : source ≃ₜ target
  branch_covered : ∀ q : source,
    (q : TotalSpace (parameterMap F)) ∈ orderFourLogarithmicGaugeCarrier F r B
  source_formula : ∀ q : source,
    (gaugeHomeomorph q : TotalSpace (parameterMap F)) =
      orderFourLogarithmicGaugeMap F (fun w => B.source.log w) q
  rotated_formula : ∀ q : source,
    (gaugeHomeomorph
        (cyclicGenerator 4 • q) :
      TotalSpace (parameterMap F)) =
      orderFourLogarithmicGaugeMap F (fun w => B.target.log w)
        ((cyclicGenerator 4 • q : source) : TotalSpace (parameterMap F))

namespace OrderThreeLogarithmicGaugeDescentData

variable {F r B}
    (D : OrderThreeLogarithmicGaugeDescentData F r B)

public theorem equivariant_generator
    (hsource : U.sourceAction = fuchsianSourceAction)
    (q : D.source) :
    D.gaugeHomeomorph
        (cyclicGenerator 3 • q) =
      cyclicGenerator 3 •
        (D.gaugeHomeomorph q) := by
  apply Subtype.ext
  rw [D.rotated_formula]
  change
    orderThreeLogarithmicGaugeMap F (fun w => B.target.log w)
        (smulOf (orderThreeAffineFamilyAction F) (cyclicGenerator 3) q) =
      smulOf (orderThreeLinearFamilyAction F) (cyclicGenerator 3)
        (D.gaugeHomeomorph q)
  rw [D.source_formula]
  rw [orderThreeAffine_smulOf_generator,
    orderThreeLinear_smulOf_generator]
  exact orderThreeLogarithmicGauge_conjugates_generator_on F hsource B r
    (D.branch_covered q)

@[expose] public noncomputable def toEquivariantOpenHomeomorph
    (hsource : U.sourceAction = fuchsianSourceAction) :
    EquivariantOpenHomeomorph
      (orderThreeAffineFamilyAction F) (orderThreeLinearFamilyAction F)
      D.source D.target where
  toHomeomorph := D.gaugeHomeomorph
  equivariant := equivariant_of_cyclic_generator D.gaugeHomeomorph
    (cyclicGenerator 3)
    (fun g => ⟨(Multiplicative.toAdd g).val, cyclic_eq_generator_pow g⟩)
    (D.equivariant_generator hsource)

/-- The glued order-three logarithmic gauge descends to a homeomorphism of the two exact local
orbit quotients. -/
@[expose] public noncomputable def quotientHomeomorph
    (hsource : U.sourceAction = fuchsianSourceAction) :
    D.source.OrbitQuotient ≃ₜ D.target.OrbitQuotient :=
  orbitQuotientHomeomorph (D.toEquivariantOpenHomeomorph hsource)

end OrderThreeLogarithmicGaugeDescentData

namespace OrderFourLogarithmicGaugeDescentData

variable {F r B}
    (D : OrderFourLogarithmicGaugeDescentData F r B)

public theorem equivariant_generator
    (hsource : U.sourceAction = fuchsianSourceAction)
    (q : D.source) :
    D.gaugeHomeomorph
        (cyclicGenerator 4 • q) =
      cyclicGenerator 4 •
        (D.gaugeHomeomorph q) := by
  apply Subtype.ext
  rw [D.rotated_formula]
  change
    orderFourLogarithmicGaugeMap F (fun w => B.target.log w)
        (smulOf (orderFourAffineFamilyAction F) (cyclicGenerator 4) q) =
      smulOf (orderFourLinearFamilyAction F) (cyclicGenerator 4)
        (D.gaugeHomeomorph q)
  rw [D.source_formula]
  rw [orderFourAffine_smulOf_generator,
    orderFourLinear_smulOf_generator]
  exact orderFourLogarithmicGauge_conjugates_generator_on F hsource B r
    (D.branch_covered q)

@[expose] public noncomputable def toEquivariantOpenHomeomorph
    (hsource : U.sourceAction = fuchsianSourceAction) :
    EquivariantOpenHomeomorph
      (orderFourAffineFamilyAction F) (orderFourLinearFamilyAction F)
      D.source D.target where
  toHomeomorph := D.gaugeHomeomorph
  equivariant := equivariant_of_cyclic_generator D.gaugeHomeomorph
    (cyclicGenerator 4)
    (fun g => ⟨(Multiplicative.toAdd g).val, cyclic_eq_generator_pow g⟩)
    (D.equivariant_generator hsource)

/-- The glued order-four logarithmic gauge descends to a homeomorphism of the two exact local
orbit quotients. -/
@[expose] public noncomputable def quotientHomeomorph
    (hsource : U.sourceAction = fuchsianSourceAction) :
    D.source.OrbitQuotient ≃ₜ D.target.OrbitQuotient :=
  orbitQuotientHomeomorph (D.toEquivariantOpenHomeomorph hsource)

end OrderFourLogarithmicGaugeDescentData

end

end SphereSixComplex.Geometry.EllipticLogarithmicGaugeDescent
