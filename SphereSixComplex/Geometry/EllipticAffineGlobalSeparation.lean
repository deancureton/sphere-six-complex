module

public import SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
public import SphereSixComplex.TriangleGroup.EstablishedFuchsianEllipticStabilizers
public import SphereSixComplex.TriangleGroup.FuchsianProperFreeness
public import SphereSixComplex.TriangleGroup.FuchsianSmoothAction
import all SphereSixComplex.TriangleGroup.Representation
import all SphereSixComplex.Geometry.TorusFamily

/-!
# Separation for the affine global elliptic action

The affine free-product action covers the explicit Fuchsian source action.  Proper discontinuity
therefore lifts from the source.  The final collar separation is reduced to the exact source
stabilizer calculation at the two elliptic points.
-/

namespace SphereSixComplex.Geometry.EllipticAffineGlobalSeparation

open Complex
open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem familyTotalSpaceBase_orderThreeRepresentation
    (a : CyclicThree) (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (orderThreeAffineFamilyRepresentation F a q) =
      U.sourceAction (Monoid.Coprod.inl a) • familyTotalSpaceBase F q := by
  let k := (Multiplicative.toAdd a).val
  rw [cyclic_eq_generator_pow a, map_pow]
  have hgen : orderThreeAffineFamilyRepresentation F (cyclicGenerator 3) =
      orderThreeAffineFamilyGenerator F := by
    change (cyclicRepresentation 3 (orderThreeAffineFamilyGenerator F)
      (orderThreeAffineFamilyGenerator_pow F)) (Multiplicative.ofAdd 1) = _
    exact cyclicRepresentation_generator 3 _ _
  rw [hgen, familyTotalSpaceBase_orderThreeGenerator_pow]
  have hsourceGenerator : Monoid.Coprod.inl (cyclicGenerator 3) = g₁ := by
    change Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 3)) = g₁
    exact SphereSixComplex.TriangleGroup.g₁.eq_def.symm
  rw [show Monoid.Coprod.inl (cyclicGenerator 3 ^ k) = g₁ ^ k by
    rw [map_pow]
    rw [hsourceGenerator]]

public theorem familyTotalSpaceBase_orderFourRepresentation
    (a : CyclicFour) (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (orderFourAffineFamilyRepresentation F a q) =
      U.sourceAction (Monoid.Coprod.inr a) • familyTotalSpaceBase F q := by
  let k := (Multiplicative.toAdd a).val
  rw [cyclic_eq_generator_pow a, map_pow]
  have hgen : orderFourAffineFamilyRepresentation F (cyclicGenerator 4) =
      orderFourAffineFamilyGenerator F := by
    change (cyclicRepresentation 4 (orderFourAffineFamilyGenerator F)
      (orderFourAffineFamilyGenerator_pow F)) (Multiplicative.ofAdd 1) = _
    exact cyclicRepresentation_generator 4 _ _
  rw [hgen, familyTotalSpaceBase_orderFourGenerator_pow]
  have hsourceGenerator : Monoid.Coprod.inr (cyclicGenerator 4) = g₂ := by
    change Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 4)) = g₂
    exact SphereSixComplex.TriangleGroup.g₂.eq_def.symm
  rw [show Monoid.Coprod.inr (cyclicGenerator 4 ^ k) = g₂ ^ k by
    rw [map_pow]
    rw [hsourceGenerator]]

/-- The full affine family action covers the source triangle action. -/
public theorem familyTotalSpaceBase_affineGlobalRepresentation
    (g : Delta) (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (affineGlobalFamilyRepresentation F g q) =
      U.sourceAction g • familyTotalSpaceBase F q := by
  induction g using Monoid.Coprod.induction_on generalizing q with
  | inl a =>
      rw [affineGlobalFamilyRepresentation_inl]
      exact familyTotalSpaceBase_orderThreeRepresentation F a q
  | inr a =>
      rw [affineGlobalFamilyRepresentation_inr]
      exact familyTotalSpaceBase_orderFourRepresentation F a q
  | mul g h hg hh =>
      rw [map_mul, Equiv.Perm.mul_apply, hg, hh, map_mul, mul_smul]

/-- Proper discontinuity of the source action lifts to the affine action on the varying torus
family by projection of compact sets. -/
public theorem affineGlobalFamilyAction_properlyDiscontinuous
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    letI := affineGlobalFamilyAction F
    ProperlyDiscontinuousSMul Delta (TotalSpace (parameterMap F)) := by
  let _ := affineGlobalFamilyAction F
  constructor
  intro K L hK hL
  let base : TotalSpace (parameterMap F) → UpperHalfPlane := familyTotalSpaceBase F
  have hKbase : IsCompact (base '' K) := hK.image (familyTotalSpaceBase_continuous F)
  have hLbase : IsCompact (base '' L) := hL.image (familyTotalSpaceBase_continuous F)
  let KB : Set UpperHalfPlane := base '' K
  let LB : Set UpperHalfPlane := base '' L
  rw [SourceActionProperlyDiscontinuous.eq_def] at hproper
  apply (hproper hKbase hLbase).subset
  intro g hg
  change (((fun z : UpperHalfPlane ↦ U.sourceAction g • z) '' KB) ∩ LB).Nonempty
  rcases hg with ⟨q, ⟨p, hpK, hpq⟩, hqL⟩
  refine ⟨base q, ?_, ?_⟩
  · refine ⟨base p, ⟨p, hpK, rfl⟩, ?_⟩
    change U.sourceAction g • familyTotalSpaceBase F p = familyTotalSpaceBase F q
    rw [← familyTotalSpaceBase_affineGlobalRepresentation F g p]
    exact congrArg (familyTotalSpaceBase F) hpq
  · exact ⟨q, hqL, rfl⟩

/-- Exact source stabilizer statement still needed at the order-three elliptic point. -/
@[expose] public def OrderThreeSourceStabilizerExact : Prop :=
  ∀ g : Delta,
    fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint ↔
      ∃ a : CyclicThree, g = Monoid.Coprod.inl a

/-- Exact source stabilizer statement still needed at the order-four elliptic point. -/
@[expose] public def OrderFourSourceStabilizerExact : Prop :=
  ∀ g : Delta,
    fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint ↔
      ∃ a : CyclicFour, g = Monoid.Coprod.inr a

/-- The established elliptic stabilizer theorem supplies the exact order-three source input. -/
public theorem establishedOrderThreeSourceStabilizerExact :
    OrderThreeSourceStabilizerExact :=
  establishedFuchsianOneStabilizerExact

/-- The established elliptic stabilizer theorem supplies the exact order-four source input. -/
public theorem establishedOrderFourSourceStabilizerExact :
    OrderFourSourceStabilizerExact :=
  establishedFuchsianTwoStabilizerExact

public theorem mem_familyFiber_iff_base_eq
    (z : UpperHalfPlane) (q : TotalSpace (parameterMap F)) :
    q ∈ familyFiber F z ↔ familyTotalSpaceBase F q = z := by
  constructor
  · exact familyTotalSpaceBase_eq_of_mem_familyFiber F
  · intro hq
    obtain ⟨x, hx⟩ := exists_fixedFiberToFamily_of_base_eq F hq
    subst q
    induction x using Quotient.inductionOn with
    | _ v =>
      refine ⟨v, ?_⟩
      rw [projection.eq_def]
      exact (fixedFiberToFamily_mk F z v).symm

/-- Setwise preservation of a complete varying-family fibre is exactly fixation of its source
base point. -/
public theorem affineGlobal_preserves_familyFiber_iff_source_fixed
    (g : Delta) (z : UpperHalfPlane) :
    (∀ q ∈ familyFiber F z,
      affineGlobalFamilyRepresentation F g q ∈ familyFiber F z) ↔
      U.sourceAction g • z = z := by
  constructor
  · intro h
    let q := projection (parameterMap F) (z, 0)
    have hq : q ∈ familyFiber F z := ⟨0, rfl⟩
    have hout := (mem_familyFiber_iff_base_eq F z _).mp (h q hq)
    rw [familyTotalSpaceBase_affineGlobalRepresentation,
      familyTotalSpaceBase_projection] at hout
    exact hout
  · intro hfixed q hq
    rw [mem_familyFiber_iff_base_eq]
    rw [familyTotalSpaceBase_affineGlobalRepresentation,
      (mem_familyFiber_iff_base_eq F z q).mp hq, hfixed]

/-- Conditional exact setwise stabilizer of the order-three central family fibre. -/
public theorem orderThree_centralFamilyFiber_stabilizer
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hstab : OrderThreeSourceStabilizerExact) (g : Delta) :
    (∀ q ∈ familyFiber F fuchsianOneFixedPoint,
      affineGlobalFamilyRepresentation F g q ∈ familyFiber F fuchsianOneFixedPoint) ↔
      ∃ a : CyclicThree, g = Monoid.Coprod.inl a := by
  rw [affineGlobal_preserves_familyFiber_iff_source_fixed, hsource]
  exact hstab g

/-- Conditional exact setwise stabilizer of the order-four central family fibre. -/
public theorem orderFour_centralFamilyFiber_stabilizer
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hstab : OrderFourSourceStabilizerExact) (g : Delta) :
    (∀ q ∈ familyFiber F fuchsianTwoFixedPoint,
      affineGlobalFamilyRepresentation F g q ∈ familyFiber F fuchsianTwoFixedPoint) ↔
      ∃ a : CyclicFour, g = Monoid.Coprod.inr a := by
  rw [affineGlobal_preserves_familyFiber_iff_source_fixed, hsource]
  exact hstab g

/-- Every open neighborhood of a Cayley center contains a positive radial Cayley ball. -/
public theorem exists_cayleyRadius_subset
    (a : UpperHalfPlane) {S : Set UpperHalfPlane}
    (hS : IsOpen S) (ha : a ∈ S) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∀ z : UpperHalfPlane, ‖(cayleyHomeomorph a z).1‖ < r → z ∈ S := by
  have hcenter : cayleyHomeomorph a a = discCenter := by
    apply Subtype.ext
    simp [cayleyHomeomorph, cayleyDiscCoordinate, cayleyCoordinate, discCenter]
  have hopen : IsOpen (cayleyHomeomorph a '' S) :=
    (cayleyHomeomorph a).isOpenMap S hS
  have hmem : discCenter ∈ cayleyHomeomorph a '' S :=
    ⟨a, ha, hcenter⟩
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp hopen) discCenter hmem
  let r := min ε (1 / 2 : ℝ)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right ε (1 / 2 : ℝ)) (by norm_num)
  refine ⟨r, hr, hr1, ?_⟩
  intro z hz
  have hzball : cayleyHomeomorph a z ∈ Metric.ball discCenter ε := by
    change dist (cayleyHomeomorph a z).1 (discCenter : ℂ) < ε
    change dist (cayleyHomeomorph a z).1 0 < ε
    rw [dist_zero_right]
    exact hz.trans_le (min_le_left _ _)
  obtain ⟨w, hw, hwz⟩ := hball hzball
  have hwz' : w = z := (cayleyHomeomorph a).injective hwz
  rwa [← hwz']

/-- Proper discontinuity plus the exact order-three source stabilizer gives a positive affine
collar with no additional triangle-group identifications. -/
public theorem orderThreeSmallAffineCollarOrbitSeparation_of_sourceStabilizer
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hstab : OrderThreeSourceStabilizerExact) :
    OrderThreeSmallAffineCollarOrbitSeparation F := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  obtain ⟨S, hSopen, hcenter, _hSinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) fuchsianOneFixedPoint
  obtain ⟨r, hr, hr1, hrS⟩ :=
    exists_cayleyRadius_subset fuchsianOneFixedPoint hSopen hcenter
  refine ⟨r, hr, hr1, ?_⟩
  intro q hq x hx g hg
  have hqS : familyTotalSpaceBase F q ∈ S := by
    apply hrS
    exact hq.2
  have hxS : familyTotalSpaceBase F x ∈ S := by
    apply hrS
    exact hx.2
  have hbase := congrArg (familyTotalSpaceBase F) hg
  rw [familyTotalSpaceBase_affineGlobalRepresentation] at hbase
  have hinter : ((fun z : UpperHalfPlane ↦ g • z) '' S ∩ S).Nonempty := by
    refine ⟨familyTotalSpaceBase F q, ?_, hqS⟩
    refine ⟨familyTotalSpaceBase F x, hxS, ?_⟩
    change fuchsianSourceAction g • familyTotalSpaceBase F x = familyTotalSpaceBase F q
    simpa only [← hsource] using hbase
  exact (hstab g).mp ((htranslate g).mp hinter)

/-- Proper discontinuity plus the exact order-four source stabilizer gives the corresponding
positive affine collar. -/
public theorem orderFourSmallAffineCollarOrbitSeparation_of_sourceStabilizer
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U))
    (hstab : OrderFourSourceStabilizerExact) :
    OrderFourSmallAffineCollarOrbitSeparation F := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    fuchsianProperlyDiscontinuous_of_source hsource hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane :=
    ⟨fun g ↦ (fuchsianSourceAction_contMDiff g 0).continuous⟩
  obtain ⟨S, hSopen, hcenter, _hSinvariant, htranslate⟩ :=
    exists_open_stabilizer_slice (G := Delta) fuchsianTwoFixedPoint
  obtain ⟨r, hr, hr1, hrS⟩ :=
    exists_cayleyRadius_subset fuchsianTwoFixedPoint hSopen hcenter
  refine ⟨r, hr, hr1, ?_⟩
  intro q hq x hx g hg
  have hqS : familyTotalSpaceBase F q ∈ S := by
    apply hrS
    exact hq.2
  have hxS : familyTotalSpaceBase F x ∈ S := by
    apply hrS
    exact hx.2
  have hbase := congrArg (familyTotalSpaceBase F) hg
  rw [familyTotalSpaceBase_affineGlobalRepresentation] at hbase
  have hinter : ((fun z : UpperHalfPlane ↦ g • z) '' S ∩ S).Nonempty := by
    refine ⟨familyTotalSpaceBase F q, ?_, hqS⟩
    refine ⟨familyTotalSpaceBase F x, hxS, ?_⟩
    change fuchsianSourceAction g • familyTotalSpaceBase F x = familyTotalSpaceBase F q
    simpa only [← hsource] using hbase
  exact (hstab g).mp ((htranslate g).mp hinter)

/-- The classical order-three stabilizer calculation closes the affine collar separation. -/
public theorem orderThreeSmallAffineCollarOrbitSeparation
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    OrderThreeSmallAffineCollarOrbitSeparation F :=
  orderThreeSmallAffineCollarOrbitSeparation_of_sourceStabilizer F hsource hproper
    establishedOrderThreeSourceStabilizerExact

/-- The classical order-four stabilizer calculation closes the affine collar separation. -/
public theorem orderFourSmallAffineCollarOrbitSeparation
    (hsource : U.sourceAction = fuchsianSourceAction)
    (hproper : SourceActionProperlyDiscontinuous (U := U)) :
    OrderFourSmallAffineCollarOrbitSeparation F :=
  orderFourSmallAffineCollarOrbitSeparation_of_sourceStabilizer F hsource hproper
    establishedOrderFourSourceStabilizerExact

end

end SphereSixComplex.Geometry.EllipticAffineGlobalSeparation
