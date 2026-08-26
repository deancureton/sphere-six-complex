module

public import SphereSixComplex.Geometry.ComplexModelRechart
public import SphereSixComplex.Geometry.PaperCentralFamilyTopology
public import SphereSixComplex.Geometry.EllipticLinearCollarGlobalDescent
public import SphereSixComplex.Geometry.EllipticAnalyticCollarDescent
public import SphereSixComplex.Geometry.QuotientDeckFundamentalGroup
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Elliptic filling pieces for the paper data
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination
open SphereSixComplex.TriangleGroup.FuchsianProperFreeness
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticFamilySpecialization EllipticFixedPointCriterion
open EllipticLocalCoordinates EllipticCayleyHomeomorph
open EllipticWholeFiberCompactCover EllipticWholeFiberTrivialization
open EllipticVaryingFamilyQuotient EllipticPuncturedCollarGaugeHomeomorph
open EllipticAnalyticCollarDescent EllipticLinearCollarGlobalDescent
open EllipticAffineGlobalSeparation
open EquivariantQuotientHomeomorph

noncomputable section

universe u

variable {G X : Type u} [Group G] [TopologicalSpace X]

public theorem restrictedOrbitRel_eq_mulActionOrbitRel
    (A : MulAction G X) (S : InvariantOpenCarrier A) :
    restrictedOrbitRel A S =
      letI := restrictedMulAction A S
      MulAction.orbitRel G S.carrier := by
  rfl

public theorem restrictedIsCancelSMul
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hfree : letI := A; IsCancelSMul G X) :
    letI := restrictedMulAction A S
    IsCancelSMul G S.carrier := by
  let _ := A
  let _ : IsCancelSMul G X := hfree
  let _ := restrictedMulAction A S
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x hx
  apply IsCancelSMul.eq_one_of_smul (x := (x : X))
  exact congrArg Subtype.val hx

public theorem restrictedContinuousConstSMul
    (A : MulAction G X) (S : InvariantOpenCarrier A)
    (hcontinuous : letI := A; ContinuousConstSMul G X) :
    letI := restrictedMulAction A S
    ContinuousConstSMul G S.carrier := by
  let _ := A
  let _ : ContinuousConstSMul G X := hcontinuous
  let _ := restrictedMulAction A S
  exact ⟨fun g => Continuous.subtype_mk
    ((continuous_const_smul g).comp continuous_subtype_val) _⟩

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

@[expose] public noncomputable def orderThreeFillingOpen (r : ℝ) :
    TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
  ⟨{q | orderThreeFamilyRadius A.periods q < r},
    isOpen_lt (orderThreeFamilyRadius_continuous A.periods) continuous_const⟩

@[expose] public noncomputable def orderFourFillingOpen (r : ℝ) :
    TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
  ⟨{q | orderFourFamilyRadius A.periods q < r},
    isOpen_lt (orderFourFamilyRadius_continuous A.periods) continuous_const⟩

@[expose] public noncomputable def orderThreeFillingCarrier (r : ℝ) :
    InvariantOpenCarrier (orderThreeAffineFamilyAction A.periods) where
  carrier := A.orderThreeFillingOpen r
  isOpen_carrier := (A.orderThreeFillingOpen r).2
  invariant g q hq := by
    change orderThreeFamilyRadius A.periods
      (orderThreeAffineFamilyRepresentation A.periods g q) < r
    rw [orderThreeFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact hq

@[expose] public noncomputable def orderFourFillingCarrier (r : ℝ) :
    InvariantOpenCarrier (orderFourAffineFamilyAction A.periods) where
  carrier := A.orderFourFillingOpen r
  isOpen_carrier := (A.orderFourFillingOpen r).2
  invariant g q hq := by
    change orderFourFamilyRadius A.periods
      (orderFourAffineFamilyRepresentation A.periods g q) < r
    rw [orderFourFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact hq

@[expose, instance_reducible]
public noncomputable def orderThreeFillingAction (r : ℝ) :
    MulAction (FiniteCyclic 3) (A.orderThreeFillingOpen r) where
  smul g q := ⟨orderThreeAffineFamilyRepresentation A.periods g q, by
    change orderThreeFamilyRadius A.periods
      (orderThreeAffineFamilyRepresentation A.periods g q) < r
    rw [orderThreeFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact q.property⟩
  one_smul q := by
    apply Subtype.ext
    change orderThreeAffineFamilyRepresentation A.periods 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    apply Subtype.ext
    change orderThreeAffineFamilyRepresentation A.periods (g * h) q =
      orderThreeAffineFamilyRepresentation A.periods g
        (orderThreeAffineFamilyRepresentation A.periods h q)
    rw [map_mul]
    rfl

@[expose, instance_reducible]
public noncomputable def orderFourFillingAction (r : ℝ) :
    MulAction (FiniteCyclic 4) (A.orderFourFillingOpen r) where
  smul g q := ⟨orderFourAffineFamilyRepresentation A.periods g q, by
    change orderFourFamilyRadius A.periods
      (orderFourAffineFamilyRepresentation A.periods g q) < r
    rw [orderFourFamilyRadius_representation A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction]
    exact q.property⟩
  one_smul q := by
    apply Subtype.ext
    change orderFourAffineFamilyRepresentation A.periods 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    apply Subtype.ext
    change orderFourAffineFamilyRepresentation A.periods (g * h) q =
      orderFourAffineFamilyRepresentation A.periods g
        (orderFourAffineFamilyRepresentation A.periods h q)
    rw [map_mul]
    rfl

public abbrev OrderThreeVaryingFilling (r : ℝ) :=
  letI := A.orderThreeFillingAction r
  OrbitQuotient (M := A.orderThreeFillingOpen r) (G := FiniteCyclic 3)

public abbrev OrderFourVaryingFilling (r : ℝ) :=
  letI := A.orderFourFillingAction r
  OrbitQuotient (M := A.orderFourFillingOpen r) (G := FiniteCyclic 4)

/-- The order-three radial coordinate is constant on the finite filling action. -/
public theorem orderThreeFillingRadius_respects (r : ℝ)
    (x y : A.orderThreeFillingOpen r)
    (h : letI := A.orderThreeFillingAction r
      MulAction.orbitRel (FiniteCyclic 3) _ x y) :
    orderThreeFamilyRadius A.periods x.1 = orderThreeFamilyRadius A.periods y.1 := by
  let _ := A.orderThreeFillingAction r
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  calc
    orderThreeFamilyRadius A.periods x.1 =
        orderThreeFamilyRadius A.periods
          (orderThreeAffineFamilyRepresentation A.periods g y.1) := by
      exact congrArg (orderThreeFamilyRadius A.periods) (congrArg Subtype.val hg).symm
    _ = orderThreeFamilyRadius A.periods y.1 :=
      orderThreeFamilyRadius_representation A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction g y.1

/-- The order-four radial coordinate is constant on the finite filling action. -/
public theorem orderFourFillingRadius_respects (r : ℝ)
    (x y : A.orderFourFillingOpen r)
    (h : letI := A.orderFourFillingAction r
      MulAction.orbitRel (FiniteCyclic 4) _ x y) :
    orderFourFamilyRadius A.periods x.1 = orderFourFamilyRadius A.periods y.1 := by
  let _ := A.orderFourFillingAction r
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  calc
    orderFourFamilyRadius A.periods x.1 =
        orderFourFamilyRadius A.periods
          (orderFourAffineFamilyRepresentation A.periods g y.1) := by
      exact congrArg (orderFourFamilyRadius A.periods) (congrArg Subtype.val hg).symm
    _ = orderFourFamilyRadius A.periods y.1 :=
      orderFourFamilyRadius_representation A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction g y.1

/-- Radial coordinate on the order-three filling quotient. -/
@[expose] public noncomputable def orderThreeFillingRadius (r : ℝ) :
    A.OrderThreeVaryingFilling r → ℝ := by
  let _ := A.orderThreeFillingAction r
  exact Quotient.lift (fun q ↦ orderThreeFamilyRadius A.periods q.1)
    (A.orderThreeFillingRadius_respects r)

/-- Radial coordinate on the order-four filling quotient. -/
@[expose] public noncomputable def orderFourFillingRadius (r : ℝ) :
    A.OrderFourVaryingFilling r → ℝ := by
  let _ := A.orderFourFillingAction r
  exact Quotient.lift (fun q ↦ orderFourFamilyRadius A.periods q.1)
    (A.orderFourFillingRadius_respects r)

@[simp]
public theorem orderThreeFillingRadius_mk (r : ℝ) (q : A.orderThreeFillingOpen r) :
    A.orderThreeFillingRadius r (Quotient.mk _ q) =
      orderThreeFamilyRadius A.periods q.1 := by
  rw [orderThreeFillingRadius.eq_def]
  rfl

@[simp]
public theorem orderFourFillingRadius_mk (r : ℝ) (q : A.orderFourFillingOpen r) :
    A.orderFourFillingRadius r (Quotient.mk _ q) =
      orderFourFamilyRadius A.periods q.1 := by
  rw [orderFourFillingRadius.eq_def]
  rfl

/-- The descended order-three filling radius is continuous. -/
public theorem orderThreeFillingRadius_continuous (r : ℝ) :
    Continuous (A.orderThreeFillingRadius r) := by
  rw [orderThreeFillingRadius.eq_def]
  exact continuous_quot_lift (A.orderThreeFillingRadius_respects r)
    ((orderThreeFamilyRadius_continuous A.periods).comp continuous_subtype_val)

/-- The descended order-four filling radius is continuous. -/
public theorem orderFourFillingRadius_continuous (r : ℝ) :
    Continuous (A.orderFourFillingRadius r) := by
  rw [orderFourFillingRadius.eq_def]
  exact continuous_quot_lift (A.orderFourFillingRadius_respects r)
    ((orderFourFamilyRadius_continuous A.periods).comp continuous_subtype_val)

/-- The descended order-three filling radius is nonnegative. -/
public theorem orderThreeFillingRadius_nonneg (r : ℝ)
    (Q : A.OrderThreeVaryingFilling r) :
    0 ≤ A.orderThreeFillingRadius r Q := by
  induction Q using Quotient.inductionOn with
  | _ q =>
      rw [A.orderThreeFillingRadius_mk, orderThreeFamilyRadius.eq_def]
      exact norm_nonneg _

/-- Every point of the order-three filling has radius strictly below its defining radius. -/
public theorem orderThreeFillingRadius_lt (r : ℝ)
    (Q : A.OrderThreeVaryingFilling r) :
    A.orderThreeFillingRadius r Q < r := by
  induction Q using Quotient.inductionOn with
  | _ q =>
      rw [A.orderThreeFillingRadius_mk]
      exact q.property

/-- The descended order-four filling radius is nonnegative. -/
public theorem orderFourFillingRadius_nonneg (r : ℝ)
    (Q : A.OrderFourVaryingFilling r) :
    0 ≤ A.orderFourFillingRadius r Q := by
  induction Q using Quotient.inductionOn with
  | _ q =>
      rw [A.orderFourFillingRadius_mk, orderFourFamilyRadius.eq_def]
      exact norm_nonneg _

/-- Every point of the order-four filling has radius strictly below its defining radius. -/
public theorem orderFourFillingRadius_lt (r : ℝ)
    (Q : A.OrderFourVaryingFilling r) :
    A.orderFourFillingRadius r Q < r := by
  induction Q using Quotient.inductionOn with
  | _ q =>
      rw [A.orderFourFillingRadius_mk]
      exact q.property

/-- Every closed order-three radial sublevel strictly below the filling radius is compact. -/
public theorem orderThreeFillingRadius_le_isCompact
    {s r : ℝ} (hsr : s < r) (hr : r < 1) :
    IsCompact {Q : A.OrderThreeVaryingFilling r |
      A.orderThreeFillingRadius r Q ≤ s} := by
  let K : Set (A.orderThreeFillingOpen r) :=
    {q | orderThreeFamilyRadius A.periods q.1 ≤ s}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have heq : ((↑) : A.orderThreeFillingOpen r →
        TotalSpace (parameterMap A.periods)) '' K =
        {q | orderThreeFamilyRadius A.periods q ≤ s} := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hq
        exact ⟨⟨q, hq.trans_lt hsr⟩, hq, rfl⟩
    rw [heq]
    exact orderThreeFamilyRadius_le_isCompact A.periods (hsr.trans hr)
  let _ := A.orderThreeFillingAction r
  have heq : {Q : A.OrderThreeVaryingFilling r |
      A.orderThreeFillingRadius r Q ≤ s} = Quotient.mk _ '' K := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨q, rfl⟩ := Quotient.mk_surjective Q
      have hq : q ∈ K := by
        change orderThreeFamilyRadius A.periods q.1 ≤ s
        simpa using hQ
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      change orderThreeFamilyRadius A.periods q.1 ≤ s at hq
      simpa using hq
  rw [heq]
  exact hK.image continuous_quot_mk

/-- Every closed order-four radial sublevel strictly below the filling radius is compact. -/
public theorem orderFourFillingRadius_le_isCompact
    {s r : ℝ} (hsr : s < r) (hr : r < 1) :
    IsCompact {Q : A.OrderFourVaryingFilling r |
      A.orderFourFillingRadius r Q ≤ s} := by
  let K : Set (A.orderFourFillingOpen r) :=
    {q | orderFourFamilyRadius A.periods q.1 ≤ s}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have heq : ((↑) : A.orderFourFillingOpen r →
        TotalSpace (parameterMap A.periods)) '' K =
        {q | orderFourFamilyRadius A.periods q ≤ s} := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hq
        exact ⟨⟨q, hq.trans_lt hsr⟩, hq, rfl⟩
    rw [heq]
    exact orderFourFamilyRadius_le_isCompact A.periods (hsr.trans hr)
  let _ := A.orderFourFillingAction r
  have heq : {Q : A.OrderFourVaryingFilling r |
      A.orderFourFillingRadius r Q ≤ s} = Quotient.mk _ '' K := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨q, rfl⟩ := Quotient.mk_surjective Q
      have hq : q ∈ K := by
        change orderFourFamilyRadius A.periods q.1 ≤ s
        simpa using hQ
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      change orderFourFamilyRadius A.periods q.1 ≤ s at hq
      simpa using hq
  rw [heq]
  exact hK.image continuous_quot_mk

/-- Radial coordinate on the order-three punctured collar quotient. -/
@[expose] public noncomputable def orderThreePuncturedCollarRadius (r : ℝ) :
    Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) → ℝ := by
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  refine Quotient.lift (fun q ↦ orderThreeFamilyRadius A.periods q.1) ?_
  intro x y h
  change MulAction.orbitRel (FiniteCyclic 3) _ x y at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  calc
    orderThreeFamilyRadius A.periods x.1 =
        orderThreeFamilyRadius A.periods
          (orderThreeAffineFamilyRepresentation A.periods g y.1) := by
      exact congrArg (orderThreeFamilyRadius A.periods) (congrArg Subtype.val hg).symm
    _ = orderThreeFamilyRadius A.periods y.1 :=
      orderThreeFamilyRadius_representation A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction g y.1

/-- Radial coordinate on the order-four punctured collar quotient. -/
@[expose] public noncomputable def orderFourPuncturedCollarRadius (r : ℝ) :
    Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) → ℝ := by
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  refine Quotient.lift (fun q ↦ orderFourFamilyRadius A.periods q.1) ?_
  intro x y h
  change MulAction.orbitRel (FiniteCyclic 4) _ x y at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  calc
    orderFourFamilyRadius A.periods x.1 =
        orderFourFamilyRadius A.periods
          (orderFourAffineFamilyRepresentation A.periods g y.1) := by
      exact congrArg (orderFourFamilyRadius A.periods) (congrArg Subtype.val hg).symm
    _ = orderFourFamilyRadius A.periods y.1 :=
      orderFourFamilyRadius_representation A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction g y.1

@[simp]
public theorem orderThreePuncturedCollarRadius_mk (r : ℝ)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.orderThreePuncturedCollarRadius r (Quotient.mk _ q) =
      orderThreeFamilyRadius A.periods q.1 := by
  rw [orderThreePuncturedCollarRadius.eq_def]
  rfl

@[simp]
public theorem orderFourPuncturedCollarRadius_mk (r : ℝ)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.orderFourPuncturedCollarRadius r (Quotient.mk _ q) =
      orderFourFamilyRadius A.periods q.1 := by
  rw [orderFourPuncturedCollarRadius.eq_def]
  rfl

/-- The descended order-three punctured-collar radius is continuous. -/
public theorem orderThreePuncturedCollarRadius_continuous (r : ℝ) :
    Continuous (A.orderThreePuncturedCollarRadius r) := by
  rw [orderThreePuncturedCollarRadius.eq_def]
  exact continuous_quot_lift _
    ((orderThreeFamilyRadius_continuous A.periods).comp continuous_subtype_val)

/-- The descended order-four punctured-collar radius is continuous. -/
public theorem orderFourPuncturedCollarRadius_continuous (r : ℝ) :
    Continuous (A.orderFourPuncturedCollarRadius r) := by
  rw [orderFourPuncturedCollarRadius.eq_def]
  exact continuous_quot_lift _
    ((orderFourFamilyRadius_continuous A.periods).comp continuous_subtype_val)

/-- A closed radial annulus in the order-three punctured collar quotient is compact. -/
public theorem orderThreePuncturedCollarClosedAnnulus_isCompact
    {s t r : ℝ} (hs : 0 < s) (htr : t < r) (hr : r < 1) :
    IsCompact {Q : Quotient (restrictedOrbitRel
        (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)) |
      s ≤ A.orderThreePuncturedCollarRadius r Q ∧
        A.orderThreePuncturedCollarRadius r Q ≤ t} := by
  let S := (orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier
  let K : Set S := {q | s ≤ orderThreeFamilyRadius A.periods q.1 ∧
    orderThreeFamilyRadius A.periods q.1 ≤ t}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have heq : ((↑) : S → TotalSpace (parameterMap A.periods)) '' K =
        {q | s ≤ orderThreeFamilyRadius A.periods q ∧
          orderThreeFamilyRadius A.periods q ≤ t} := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hq
        have hcarrier : 0 < orderThreeFamilyRadius A.periods q ∧
            orderThreeFamilyRadius A.periods q < r :=
          ⟨hs.trans_le hq.1, hq.2.trans_lt htr⟩
        exact ⟨⟨q, hcarrier⟩, hq, rfl⟩
    rw [heq]
    exact orderThreeFamilyClosedAnnulus_isCompact A.periods s (htr.trans hr)
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  have heq : {Q : Quotient (restrictedOrbitRel
        (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)) |
      s ≤ A.orderThreePuncturedCollarRadius r Q ∧
        A.orderThreePuncturedCollarRadius r Q ≤ t} = Quotient.mk _ '' K := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨q, rfl⟩ := Quotient.mk_surjective Q
      have hq : q ∈ K := by
        change s ≤ orderThreeFamilyRadius A.periods q.1 ∧
          orderThreeFamilyRadius A.periods q.1 ≤ t
        simpa using hQ
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      change s ≤ orderThreeFamilyRadius A.periods q.1 ∧
        orderThreeFamilyRadius A.periods q.1 ≤ t at hq
      change s ≤ A.orderThreePuncturedCollarRadius r (Quotient.mk _ q) ∧
        A.orderThreePuncturedCollarRadius r (Quotient.mk _ q) ≤ t
      simpa only [A.orderThreePuncturedCollarRadius_mk] using hq
  rw [heq]
  exact hK.image continuous_quot_mk

/-- A closed radial annulus in the order-four punctured collar quotient is compact. -/
public theorem orderFourPuncturedCollarClosedAnnulus_isCompact
    {s t r : ℝ} (hs : 0 < s) (htr : t < r) (hr : r < 1) :
    IsCompact {Q : Quotient (restrictedOrbitRel
        (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)) |
      s ≤ A.orderFourPuncturedCollarRadius r Q ∧
        A.orderFourPuncturedCollarRadius r Q ≤ t} := by
  let S := (orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier
  let K : Set S := {q | s ≤ orderFourFamilyRadius A.periods q.1 ∧
    orderFourFamilyRadius A.periods q.1 ≤ t}
  have hK : IsCompact K := by
    rw [Subtype.isCompact_iff]
    have heq : ((↑) : S → TotalSpace (parameterMap A.periods)) '' K =
        {q | s ≤ orderFourFamilyRadius A.periods q ∧
          orderFourFamilyRadius A.periods q ≤ t} := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hq
        have hcarrier : 0 < orderFourFamilyRadius A.periods q ∧
            orderFourFamilyRadius A.periods q < r :=
          ⟨hs.trans_le hq.1, hq.2.trans_lt htr⟩
        exact ⟨⟨q, hcarrier⟩, hq, rfl⟩
    rw [heq]
    exact orderFourFamilyClosedAnnulus_isCompact A.periods s (htr.trans hr)
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  have heq : {Q : Quotient (restrictedOrbitRel
        (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)) |
      s ≤ A.orderFourPuncturedCollarRadius r Q ∧
        A.orderFourPuncturedCollarRadius r Q ≤ t} = Quotient.mk _ '' K := by
    ext Q
    constructor
    · intro hQ
      obtain ⟨q, rfl⟩ := Quotient.mk_surjective Q
      have hq : q ∈ K := by
        change s ≤ orderFourFamilyRadius A.periods q.1 ∧
          orderFourFamilyRadius A.periods q.1 ≤ t
        simpa using hQ
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      change s ≤ orderFourFamilyRadius A.periods q.1 ∧
        orderFourFamilyRadius A.periods q.1 ≤ t at hq
      change s ≤ A.orderFourPuncturedCollarRadius r (Quotient.mk _ q) ∧
        A.orderFourPuncturedCollarRadius r (Quotient.mk _ q) ≤ t
      simpa only [A.orderFourPuncturedCollarRadius_mk] using hq
  rw [heq]
  exact hK.image continuous_quot_mk

@[instance_reducible]
public noncomputable def totalSpaceCharts :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  infer_instance

public theorem totalSpace_isManifold :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) inferInstance A.totalSpaceCharts := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  exact (totalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods RegularSmoothnessOrder).1

public theorem totalSpace_projection_isLocalDiffeomorph :
    letI := A.totalSpaceCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (projection (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  exact (totalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods RegularSmoothnessOrder).2

/-- The same canonical total-space atlas supports the analytic regularity used by the elliptic
logarithmic gauges. -/
public theorem totalSpace_isManifold_analytic :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) inferInstance A.totalSpaceCharts := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  exact (totalSpace_isManifold_and_projection_isLocalDiffeomorph A.periods ω).1

/-- The canonical varying-torus projection is locally analytic, hence supplies the analytic
input required by the punctured logarithmic gauge. -/
public theorem totalSpace_projection_isLocalDiffeomorph_analytic :
    letI := A.totalSpaceCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ := A.totalSpaceCharts
  exact (totalSpace_isManifold_and_projection_isLocalDiffeomorph A.periods ω).2

@[instance_reducible]
public noncomputable def orderThreeFillingSourceCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderThreeFillingOpen r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderThreeFillingOpen r)
  infer_instance

@[instance_reducible]
public noncomputable def orderFourFillingSourceCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderFourFillingOpen r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.orderFourFillingOpen r)
  infer_instance

public theorem orderThreeFillingSource_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) inferInstance
      (A.orderThreeFillingSourceCharts r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderThreeFillingSourceCharts r
  change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (A.orderThreeFillingOpen r)
  infer_instance

public theorem orderFourFillingSource_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) inferInstance
      (A.orderFourFillingSourceCharts r) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderFourFillingSourceCharts r
  change IsManifold GlobalDeckTotalModel RegularSmoothnessOrder (A.orderFourFillingOpen r)
  infer_instance

public theorem orderThreeFillingRestrictedAction_contMDiff (r : ℝ) (g : FiniteCyclic 3) :
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : A.orderThreeFillingOpen r => g • q) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  have hcharts : A.orderThreeFillingSourceCharts r =
      (A.orderThreeFillingOpen r).instChartedSpace := by
    rfl
  rw [hcharts]
  rw [← ContMDiff.subtypeVal_comp_iff (A.orderThreeFillingOpen r)]
  convert (orderThreeAffineFamilyRepresentation_contMDiff A.periods
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).2 g).comp
      (contMDiff_subtype_val (I := GlobalDeckTotalModel)) using 1
  funext q
  rfl

public theorem orderFourFillingRestrictedAction_contMDiff (r : ℝ) (g : FiniteCyclic 4) :
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (fun q : A.orderFourFillingOpen r => g • q) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) :=
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).1
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  have hcharts : A.orderFourFillingSourceCharts r =
      (A.orderFourFillingOpen r).instChartedSpace := by
    rfl
  rw [hcharts]
  rw [← ContMDiff.subtypeVal_comp_iff (A.orderFourFillingOpen r)]
  convert (orderFourAffineFamilyRepresentation_contMDiff A.periods
    (totalSpace_isManifold_and_projection_isLocalDiffeomorph
      A.periods RegularSmoothnessOrder).2 g).comp
      (contMDiff_subtype_val (I := GlobalDeckTotalModel)) using 1
  funext q
  rfl

public theorem orderThreeFillingAction_free (r : ℝ) :
    letI := A.orderThreeFillingAction r
    IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) := by
  let _ := A.orderThreeFillingAction r
  let hfree := orderThreeAffineFamilyAction_free A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g q hq
  let _ := orderThreeAffineFamilyAction A.periods
  let _ : IsCancelSMul (FiniteCyclic 3) (TotalSpace (parameterMap A.periods)) := hfree
  apply IsCancelSMul.eq_one_of_smul (x := (q : TotalSpace (parameterMap A.periods)))
  exact congrArg Subtype.val hq

public theorem orderFourFillingAction_free (r : ℝ) :
    letI := A.orderFourFillingAction r
    IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) := by
  let _ := A.orderFourFillingAction r
  let hfree := orderFourAffineFamilyAction_free A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g q hq
  let _ := orderFourAffineFamilyAction A.periods
  let _ : IsCancelSMul (FiniteCyclic 4) (TotalSpace (parameterMap A.periods)) := hfree
  apply IsCancelSMul.eq_one_of_smul (x := (q : TotalSpace (parameterMap A.periods)))
  exact congrArg Subtype.val hq

public theorem orderThreeFillingAction_continuousConstSMul (r : ℝ) :
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  exact ⟨fun g => (A.orderThreeFillingRestrictedAction_contMDiff r g).continuous⟩

public theorem orderFourFillingAction_continuousConstSMul (r : ℝ) :
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  exact ⟨fun g => (A.orderFourFillingRestrictedAction_contMDiff r g).continuous⟩

public theorem totalSpace_t2 : T2Space (TotalSpace (parameterMap A.periods)) := by
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  infer_instance

/-- The finite order-three filling quotient is Hausdorff. -/
public theorem orderThreeFilling_t2 (r : ℝ) :
    T2Space (A.OrderThreeVaryingFilling r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  infer_instance

/-- The finite order-four filling quotient is Hausdorff. -/
public theorem orderFourFilling_t2 (r : ℝ) :
    T2Space (A.OrderFourVaryingFilling r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  infer_instance

@[instance_reducible]
public noncomputable def orderThreeFillingProductCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.OrderThreeVaryingFilling r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  infer_instance

@[instance_reducible]
public noncomputable def orderFourFillingProductCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (A.OrderFourVaryingFilling r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  infer_instance

public theorem orderThreeFillingProduct_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderThreeVaryingFilling r) inferInstance (A.orderThreeFillingProductCharts r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let _ := A.orderThreeFillingProductCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingRestrictedAction_contMDiff r)).1

public theorem orderFourFillingProduct_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance (ℂ × ComplexTwoSpace) inferInstance inferInstance
      (ModelProd ℂ ComplexTwoSpace) inferInstance GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderFourVaryingFilling r) inferInstance (A.orderFourFillingProductCharts r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let _ := A.orderFourFillingProductCharts r
  exact (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingRestrictedAction_contMDiff r)).1

/-- The order-three filling quotient projection is locally biholomorphic for the selected
product-model atlas. -/
public theorem orderThreeFilling_projection_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderThreeFillingSourceCharts r
    letI := A.orderThreeFillingAction r
    letI := A.orderThreeFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic 3)
        (A.orderThreeFillingOpen r))) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let _ := A.orderThreeFillingProductCharts r
  simpa only [quotientProjection.eq_def] using
    (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
      GlobalDeckTotalModel RegularSmoothnessOrder
        (A.orderThreeFillingRestrictedAction_contMDiff r)).2

/-- The order-four filling quotient projection is locally biholomorphic for the selected
product-model atlas. -/
public theorem orderFourFilling_projection_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderFourFillingSourceCharts r
    letI := A.orderFourFillingAction r
    letI := A.orderFourFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic 4)
        (A.orderFourFillingOpen r))) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let _ := A.orderFourFillingProductCharts r
  simpa only [quotientProjection.eq_def] using
    (orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
      GlobalDeckTotalModel RegularSmoothnessOrder
        (A.orderFourFillingRestrictedAction_contMDiff r)).2

@[expose, instance_reducible]
public noncomputable def orderThreeFillingComplexCharts (r : ℝ) :
    ChartedSpace ComplexModel (A.OrderThreeVaryingFilling r) := by
  let _ := A.orderThreeFillingProductCharts r
  exact globalDeckComplexCharts

@[expose, instance_reducible]
public noncomputable def orderFourFillingComplexCharts (r : ℝ) :
    ChartedSpace ComplexModel (A.OrderFourVaryingFilling r) := by
  let _ := A.orderFourFillingProductCharts r
  exact globalDeckComplexCharts

public theorem orderThreeFilling_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (A.OrderThreeVaryingFilling r) inferInstance (A.orderThreeFillingComplexCharts r) := by
  let _ := A.orderThreeFillingProductCharts r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderThreeVaryingFilling r) := A.orderThreeFillingProduct_isManifold r
  exact globalDeckComplexManifold

public theorem orderFourFilling_isManifold (r : ℝ) :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (A.OrderFourVaryingFilling r) inferInstance (A.orderFourFillingComplexCharts r) := by
  let _ := A.orderFourFillingProductCharts r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.OrderFourVaryingFilling r) := A.orderFourFillingProduct_isManifold r
  exact globalDeckComplexManifold

/-- Product-model quotient charts on the order-three punctured affine collar. -/
@[instance_reducible]
public noncomputable def orderThreePuncturedCollarProductCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  exact orderThreeAffinePuncturedQuotientCharts A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    A.modular.modularParameter.toTriangleUniformization_sourceAction r

/-- Product-model quotient charts on the order-four punctured affine collar. -/
@[instance_reducible]
public noncomputable def orderFourPuncturedCollarProductCharts (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  exact orderFourAffinePuncturedQuotientCharts A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    A.modular.modularParameter.toTriangleUniformization_sourceAction r

/-- Canonical complex-threefold charts on the order-three punctured collar quotient. -/
@[expose, instance_reducible]
public noncomputable def orderThreePuncturedCollarComplexCharts (r : ℝ) :
    ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.orderThreePuncturedCollarProductCharts r
  exact globalDeckComplexCharts

/-- Canonical complex-threefold charts on the order-four punctured collar quotient. -/
@[expose, instance_reducible]
public noncomputable def orderFourPuncturedCollarComplexCharts (r : ℝ) :
    ChartedSpace ComplexModel
      (Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r))) := by
  let _ := A.orderFourPuncturedCollarProductCharts r
  exact globalDeckComplexCharts

public theorem totalSpace_secondCountable :
    SecondCountableTopology (TotalSpace (parameterMap A.periods)) := by
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    fun a => (periodSection_contMDiff A.periods a RegularSmoothnessOrder).continuous
  exact ContinuousConstSMul.secondCountableTopology

public theorem orderThreeFilling_secondCountable (r : ℝ) :
    SecondCountableTopology (A.OrderThreeVaryingFilling r) := by
  let _ : SecondCountableTopology (TotalSpace (parameterMap A.periods)) :=
    A.totalSpace_secondCountable
  let _ : SecondCountableTopology (A.orderThreeFillingOpen r) := by infer_instance
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  exact ContinuousConstSMul.secondCountableTopology

public theorem orderFourFilling_secondCountable (r : ℝ) :
    SecondCountableTopology (A.OrderFourVaryingFilling r) := by
  let _ : SecondCountableTopology (TotalSpace (parameterMap A.periods)) :=
    A.totalSpace_secondCountable
  let _ : SecondCountableTopology (A.orderFourFillingOpen r) := by infer_instance
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  exact ContinuousConstSMul.secondCountableTopology

public theorem orderThreePuncturedCarrier_subset_filling (r : ℝ) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier ⊆
      A.orderThreeFillingOpen r := by
  intro q hq
  exact hq.2

public theorem orderFourPuncturedCarrier_subset_filling (r : ℝ) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier ⊆
      A.orderFourFillingOpen r := by
  intro q hq
  exact hq.2

@[expose] public def orderThreePuncturedSourceToFillingSource (r : ℝ) :
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier →
      A.orderThreeFillingOpen r :=
  Set.inclusion (A.orderThreePuncturedCarrier_subset_filling r)

@[expose] public def orderFourPuncturedSourceToFillingSource (r : ℝ) :
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier →
      A.orderFourFillingOpen r :=
  Set.inclusion (A.orderFourPuncturedCarrier_subset_filling r)

public theorem orderThreePuncturedSourceToFillingSource_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderThreePuncturedSourceToFillingSource r) := by
  apply Topology.IsOpenEmbedding.inclusion
    (A.orderThreePuncturedCarrier_subset_filling r)
  exact (orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier.preimage
      continuous_subtype_val

public theorem orderFourPuncturedSourceToFillingSource_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderFourPuncturedSourceToFillingSource r) := by
  apply Topology.IsOpenEmbedding.inclusion
    (A.orderFourPuncturedCarrier_subset_filling r)
  exact (orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier.preimage
      continuous_subtype_val

/-- The inclusion of the order-three punctured affine collar into the filling source is locally
biholomorphic. -/
public theorem orderThreePuncturedSourceToFillingSource_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderThreeFillingSourceCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreePuncturedSourceToFillingSource r) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderThreeFillingSourceCharts r
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨(orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier⟩
  let W : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    A.orderThreeFillingOpen r
  have hsourceCharts : orderThreeAffinePuncturedCarrierCharts A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r =
      V.instChartedSpace := rfl
  have htargetCharts : A.orderThreeFillingSourceCharts r = W.instChartedSpace := rfl
  rw [hsourceCharts, htargetCharts]
  change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
    RegularSmoothnessOrder
      (fun x : V ↦ (⟨x.1, A.orderThreePuncturedCarrier_subset_filling r x.2⟩ : W))
  exact opensInclusion_isLocalDiffeomorph V W
    (A.orderThreePuncturedCarrier_subset_filling r)

/-- The order-four punctured source inclusion is locally biholomorphic as well. -/
public theorem orderFourPuncturedSourceToFillingSource_isLocalDiffeomorph (r : ℝ) :
    letI := A.totalSpaceCharts
    letI := A.orderFourFillingSourceCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourPuncturedSourceToFillingSource r) := by
  let _ := A.totalSpaceCharts
  let _ := A.orderFourFillingSourceCharts r
  let V : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    ⟨(orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).isOpen_carrier⟩
  let W : TopologicalSpace.Opens (TotalSpace (parameterMap A.periods)) :=
    A.orderFourFillingOpen r
  have hsourceCharts : orderFourAffinePuncturedCarrierCharts A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r =
      V.instChartedSpace := rfl
  have htargetCharts : A.orderFourFillingSourceCharts r = W.instChartedSpace := rfl
  rw [hsourceCharts, htargetCharts]
  change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
    RegularSmoothnessOrder
      (fun x : V ↦ (⟨x.1, A.orderFourPuncturedCarrier_subset_filling r x.2⟩ : W))
  exact opensInclusion_isLocalDiffeomorph V W
    (A.orderFourPuncturedCarrier_subset_filling r)

@[expose] public noncomputable def orderThreePuncturedCollarToFilling (r : ℝ) :
    Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.OrderThreeVaryingFilling r := by
  let _ := A.orderThreeFillingAction r
  refine Quotient.map (A.orderThreePuncturedSourceToFillingSource r) ?_
  intro x y hxy
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  change MulAction.orbitRel (FiniteCyclic 3) _ x y at hxy
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
  change MulAction.orbitRel (FiniteCyclic 3) _
    (A.orderThreePuncturedSourceToFillingSource r x)
    (A.orderThreePuncturedSourceToFillingSource r y)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, Subtype.ext ?_⟩
  change orderThreeAffineFamilyRepresentation A.periods g y = x
  exact congrArg Subtype.val hg

@[expose] public noncomputable def orderFourPuncturedCollarToFilling (r : ℝ) :
    Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.OrderFourVaryingFilling r := by
  let _ := A.orderFourFillingAction r
  refine Quotient.map (A.orderFourPuncturedSourceToFillingSource r) ?_
  intro x y hxy
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  change MulAction.orbitRel (FiniteCyclic 4) _ x y at hxy
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
  change MulAction.orbitRel (FiniteCyclic 4) _
    (A.orderFourPuncturedSourceToFillingSource r x)
    (A.orderFourPuncturedSourceToFillingSource r y)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨g, hg⟩ := hxy
  refine ⟨g, Subtype.ext ?_⟩
  change orderFourAffineFamilyRepresentation A.periods g y = x
  exact congrArg Subtype.val hg

@[simp]
public theorem orderThreePuncturedCollarToFilling_mk (r : ℝ)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.orderThreePuncturedCollarToFilling r (Quotient.mk _ q) =
      Quotient.mk _ (A.orderThreePuncturedSourceToFillingSource r q) :=
  by
    rw [orderThreePuncturedCollarToFilling.eq_def]
    rfl

@[simp]
public theorem orderFourPuncturedCollarToFilling_mk (r : ℝ)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.orderFourPuncturedCollarToFilling r (Quotient.mk _ q) =
      Quotient.mk _ (A.orderFourPuncturedSourceToFillingSource r q) :=
  by
    rw [orderFourPuncturedCollarToFilling.eq_def]
    rfl

/-- The order-three collar inclusion preserves the descended radial coordinate. -/
public theorem orderThreeFillingRadius_puncturedCollarToFilling (r : ℝ)
    (Q : Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r))) :
    A.orderThreeFillingRadius r (A.orderThreePuncturedCollarToFilling r Q) =
      A.orderThreePuncturedCollarRadius r Q := by
  induction Q using Quotient.inductionOn with
  | _ q =>
      rw [A.orderThreePuncturedCollarToFilling_mk,
        A.orderThreeFillingRadius_mk, A.orderThreePuncturedCollarRadius_mk]
      rfl

/-- The order-four collar inclusion preserves the descended radial coordinate. -/
public theorem orderFourFillingRadius_puncturedCollarToFilling (r : ℝ)
    (Q : Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r))) :
    A.orderFourFillingRadius r (A.orderFourPuncturedCollarToFilling r Q) =
      A.orderFourPuncturedCollarRadius r Q := by
  induction Q using Quotient.inductionOn with
  | _ q =>
      rw [A.orderFourPuncturedCollarToFilling_mk,
        A.orderFourFillingRadius_mk, A.orderFourPuncturedCollarRadius_mk]
      rfl

/-- The order-three punctured collar fills exactly the positive-radius part of the local
filling. -/
public theorem orderThreePuncturedCollarToFilling_range (r : ℝ) :
    Set.range (A.orderThreePuncturedCollarToFilling r) =
      {Q | 0 < A.orderThreeFillingRadius r Q} := by
  ext Q
  induction Q using Quotient.inductionOn with
  | _ q =>
      constructor
      · rintro ⟨P, hP⟩
        change 0 < A.orderThreeFillingRadius r (Quotient.mk _ q)
        rw [← hP, A.orderThreeFillingRadius_puncturedCollarToFilling]
        induction P using Quotient.inductionOn with
        | _ p =>
            rw [A.orderThreePuncturedCollarRadius_mk]
            exact p.property.1
      · intro hQ
        change 0 < A.orderThreeFillingRadius r (Quotient.mk _ q) at hQ
        have hpos : 0 < orderThreeFamilyRadius A.periods q.1 := by
          simpa only [A.orderThreeFillingRadius_mk] using hQ
        let p : (orderThreeAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
          ⟨q.1, hpos, q.property⟩
        exact ⟨Quotient.mk _ p, by
          rw [A.orderThreePuncturedCollarToFilling_mk]
          rfl⟩

/-- The order-four punctured collar fills exactly the positive-radius part of the local
filling. -/
public theorem orderFourPuncturedCollarToFilling_range (r : ℝ) :
    Set.range (A.orderFourPuncturedCollarToFilling r) =
      {Q | 0 < A.orderFourFillingRadius r Q} := by
  ext Q
  induction Q using Quotient.inductionOn with
  | _ q =>
      constructor
      · rintro ⟨P, hP⟩
        change 0 < A.orderFourFillingRadius r (Quotient.mk _ q)
        rw [← hP, A.orderFourFillingRadius_puncturedCollarToFilling]
        induction P using Quotient.inductionOn with
        | _ p =>
            rw [A.orderFourPuncturedCollarRadius_mk]
            exact p.property.1
      · intro hQ
        change 0 < A.orderFourFillingRadius r (Quotient.mk _ q) at hQ
        have hpos : 0 < orderFourFamilyRadius A.periods q.1 := by
          simpa only [A.orderFourFillingRadius_mk] using hQ
        let p : (orderFourAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
          ⟨q.1, hpos, q.property⟩
        exact ⟨Quotient.mk _ p, by
          rw [A.orderFourPuncturedCollarToFilling_mk]
          rfl⟩

/-- The descended order-three punctured collar map into its filling is locally
biholomorphic. -/
public theorem orderThreePuncturedCollarToFilling_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderThreePuncturedCollarProductCharts r
    letI := A.orderThreeFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreePuncturedCollarToFilling r) := by
  let hsource := A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods hsource r)
  let _ : IsCancelSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier A.periods hsource r).carrier :=
    orderThreeAffinePuncturedAction_free A.periods hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 3)
      (orderThreeAffinePuncturedCarrier A.periods hsource r).carrier :=
    ⟨fun g ↦ (orderThreeAffinePuncturedAction_contMDiff A.periods
      A.totalSpace_projection_isLocalDiffeomorph hsource r g).continuous⟩
  let _ := A.orderThreePuncturedCollarProductCharts r
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreeFillingOpen r) := A.orderThreeFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let _ := A.orderThreeFillingProductCharts r
  have hsourceProjection :=
    (orderThreeAffinePuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
      A.periods A.totalSpace_projection_isLocalDiffeomorph hsource r).2
  have htargetProjection := A.orderThreeFilling_projection_isLocalDiffeomorph r
  have hcover := A.orderThreePuncturedSourceToFillingSource_isLocalDiffeomorph r
  apply quotientDescent_isLocalDiffeomorph
    (Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods hsource r)))
    (Quotient.mk (MulAction.orbitRel (FiniteCyclic 3)
      (A.orderThreeFillingOpen r)))
    (A.orderThreePuncturedSourceToFillingSource r)
    (A.orderThreePuncturedCollarToFilling r)
    hsourceProjection htargetProjection hcover
  · funext q
    exact A.orderThreePuncturedCollarToFilling_mk r q
  · exact Quotient.mk_surjective

/-- The descended order-four punctured collar map into its filling is locally
biholomorphic. -/
public theorem orderFourPuncturedCollarToFilling_isLocalDiffeomorph (r : ℝ) :
    letI := A.orderFourPuncturedCollarProductCharts r
    letI := A.orderFourFillingProductCharts r
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourPuncturedCollarToFilling r) := by
  let hsource := A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods hsource r)
  let _ : IsCancelSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier A.periods hsource r).carrier :=
    orderFourAffinePuncturedAction_free A.periods hsource r
  let _ : ContinuousConstSMul (FiniteCyclic 4)
      (orderFourAffinePuncturedCarrier A.periods hsource r).carrier :=
    ⟨fun g ↦ (orderFourAffinePuncturedAction_contMDiff A.periods
      A.totalSpace_projection_isLocalDiffeomorph hsource r g).continuous⟩
  let _ := A.orderFourPuncturedCollarProductCharts r
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourFillingOpen r) := A.orderFourFillingSource_isManifold r
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let _ := A.orderFourFillingProductCharts r
  have hsourceProjection :=
    (orderFourAffinePuncturedQuotient_isManifold_and_projection_isLocalDiffeomorph
      A.periods A.totalSpace_projection_isLocalDiffeomorph hsource r).2
  have htargetProjection := A.orderFourFilling_projection_isLocalDiffeomorph r
  have hcover := A.orderFourPuncturedSourceToFillingSource_isLocalDiffeomorph r
  apply quotientDescent_isLocalDiffeomorph
    (Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods hsource r)))
    (Quotient.mk (MulAction.orbitRel (FiniteCyclic 4)
      (A.orderFourFillingOpen r)))
    (A.orderFourPuncturedSourceToFillingSource r)
    (A.orderFourPuncturedCollarToFilling r)
    hsourceProjection htargetProjection hcover
  · funext q
    exact A.orderFourPuncturedCollarToFilling_mk r q
  · exact Quotient.mk_surjective

public theorem orderThreePuncturedCollarToFilling_continuous (r : ℝ) :
    Continuous (A.orderThreePuncturedCollarToFilling r) := by
  rw [orderThreePuncturedCollarToFilling.eq_def]
  exact continuous_quot_map _
    (orderThreePuncturedSourceToFillingSource_isOpenEmbedding (A := A) r).continuous

public theorem orderFourPuncturedCollarToFilling_continuous (r : ℝ) :
    Continuous (A.orderFourPuncturedCollarToFilling r) := by
  rw [orderFourPuncturedCollarToFilling.eq_def]
  exact continuous_quot_map _
    (orderFourPuncturedSourceToFillingSource_isOpenEmbedding (A := A) r).continuous

public theorem orderThreePuncturedCollarToFilling_injective (r : ℝ) :
    Function.Injective (A.orderThreePuncturedCollarToFilling r) := by
  let _ := A.orderThreeFillingAction r
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods)
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)
      change MulAction.orbitRel (FiniteCyclic 3) _ x y
      rw [A.orderThreePuncturedCollarToFilling_mk,
        A.orderThreePuncturedCollarToFilling_mk] at hxy
      rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
      obtain ⟨g, hg⟩ := hxy
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨g, Subtype.ext ?_⟩
      change orderThreeAffineFamilyRepresentation A.periods g y = x
      exact congrArg Subtype.val hg

public theorem orderFourPuncturedCollarToFilling_injective (r : ℝ) :
    Function.Injective (A.orderFourPuncturedCollarToFilling r) := by
  let _ := A.orderFourFillingAction r
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ x =>
    induction y using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods)
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r)
      change MulAction.orbitRel (FiniteCyclic 4) _ x y
      rw [A.orderFourPuncturedCollarToFilling_mk,
        A.orderFourPuncturedCollarToFilling_mk] at hxy
      rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
      obtain ⟨g, hg⟩ := hxy
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨g, Subtype.ext ?_⟩
      change orderFourAffineFamilyRepresentation A.periods g y = x
      exact congrArg Subtype.val hg

public theorem orderThreePuncturedCollarToFilling_isOpenMap (r : ℝ) :
    IsOpenMap (A.orderThreePuncturedCollarToFilling r) := by
  let _ := A.orderThreeFillingSourceCharts r
  let _ := A.orderThreeFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  intro U hU
  let pS := Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r))
  let pT := Quotient.mk (MulAction.orbitRel (FiniteCyclic 3)
    (A.orderThreeFillingOpen r))
  have hpre : IsOpen (pS ⁻¹' U) := continuous_quot_mk.isOpen_preimage U hU
  have hsource : IsOpen (A.orderThreePuncturedSourceToFillingSource r '' (pS ⁻¹' U)) :=
    (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).isOpenMap _ hpre
  have htarget : IsOpen (pT ''
      (A.orderThreePuncturedSourceToFillingSource r '' (pS ⁻¹' U))) :=
    isOpenMap_quotient_mk'_mul _ hsource
  convert htarget using 1
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    obtain ⟨s, rfl⟩ := Quotient.mk_surjective x
    exact ⟨A.orderThreePuncturedSourceToFillingSource r s,
      ⟨s, hxU, rfl⟩, (A.orderThreePuncturedCollarToFilling_mk r s).symm⟩
  · rintro ⟨t, ⟨s, hsU, rfl⟩, rfl⟩
    exact ⟨Quotient.mk _ s, hsU, A.orderThreePuncturedCollarToFilling_mk r s⟩

public theorem orderFourPuncturedCollarToFilling_isOpenMap (r : ℝ) :
    IsOpenMap (A.orderFourPuncturedCollarToFilling r) := by
  let _ := A.orderFourFillingSourceCharts r
  let _ := A.orderFourFillingAction r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  intro U hU
  let pS := Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r))
  let pT := Quotient.mk (MulAction.orbitRel (FiniteCyclic 4)
    (A.orderFourFillingOpen r))
  have hpre : IsOpen (pS ⁻¹' U) := continuous_quot_mk.isOpen_preimage U hU
  have hsource : IsOpen (A.orderFourPuncturedSourceToFillingSource r '' (pS ⁻¹' U)) :=
    (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).isOpenMap _ hpre
  have htarget : IsOpen (pT ''
      (A.orderFourPuncturedSourceToFillingSource r '' (pS ⁻¹' U))) :=
    isOpenMap_quotient_mk'_mul _ hsource
  convert htarget using 1
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    obtain ⟨s, rfl⟩ := Quotient.mk_surjective x
    exact ⟨A.orderFourPuncturedSourceToFillingSource r s,
      ⟨s, hxU, rfl⟩, (A.orderFourPuncturedCollarToFilling_mk r s).symm⟩
  · rintro ⟨t, ⟨s, hsU, rfl⟩, rfl⟩
    exact ⟨Quotient.mk _ s, hsU, A.orderFourPuncturedCollarToFilling_mk r s⟩

public theorem orderThreePuncturedCollarToFilling_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderThreePuncturedCollarToFilling r) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (A.orderThreePuncturedCollarToFilling_continuous r)
    (A.orderThreePuncturedCollarToFilling_injective r)
    (A.orderThreePuncturedCollarToFilling_isOpenMap r)

public theorem orderFourPuncturedCollarToFilling_isOpenEmbedding (r : ℝ) :
    IsOpenEmbedding (A.orderFourPuncturedCollarToFilling r) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (A.orderFourPuncturedCollarToFilling_continuous r)
    (A.orderFourPuncturedCollarToFilling_injective r)
    (A.orderFourPuncturedCollarToFilling_isOpenMap r)

@[expose] public noncomputable def orderThreePuncturedCollarToCentralFamily
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.CentralFamily := by
  let _ := A.totalSpaceCharts
  exact orderThreeAffineCollarToPuncturedGlobalFamily A.periods
    A.totalSpace_projection_isLocalDiffeomorph_analytic
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

@[expose] public noncomputable def orderFourPuncturedCollarToCentralFamily
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)) →
      A.CentralFamily := by
  let _ := A.totalSpaceCharts
  exact orderFourAffineCollarToPuncturedGlobalFamily A.periods
    A.totalSpace_projection_isLocalDiffeomorph_analytic
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

/-- The order-three collar map covers the evident orbit of its affine base point. -/
public theorem centralBaseOrbit_orderThreePuncturedCollarToCentralFamily
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r)
    (q : (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.centralBaseOrbit
        (A.orderThreePuncturedCollarToCentralFamily D (Quotient.mk _ q)) =
      Quotient.mk _ (familyTotalSpaceBase A.periods q.1) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold_analytic
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  have hmap : A.orderThreePuncturedCollarToCentralFamily D (Quotient.mk _ q) =
      Quotient.mk _ (orderThreeCollarToRegular A.periods hproper D
        (orderThreePuncturedCollarGaugeDiffeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph_analytic r q)) := by
    rw [orderThreePuncturedCollarToCentralFamily.eq_def]
    exact orderThreeAffineCollarToPuncturedGlobalFamily_mk A.periods
      A.totalSpace_projection_isLocalDiffeomorph_analytic hproper hsource D q
  rw [hmap, A.centralBaseOrbit_mk]
  apply congrArg (Quotient.mk _)
  let qg := orderThreePuncturedCollarGaugeDiffeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph_analytic r q
  have hregular :
      (regularTotalSpaceBase A.periods
        (orderThreeCollarToRegular A.periods hproper D qg)).1 =
        familyTotalSpaceBase A.periods qg.1 := by
    have h := congrArg (familyTotalSpaceBase A.periods)
      (regularFamilyInclusion_orderThreeCollarToRegular
        A.periods hproper D qg)
    rw [familyTotalSpaceBase_regularFamilyInclusion] at h
    exact h
  rw [hregular]
  dsimp only [qg]
  change familyTotalSpaceBase A.periods
      (orderThreePrincipalGaugeEquiv A.periods q.1) =
    familyTotalSpaceBase A.periods q.1
  rw [orderThreePrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
    familyTotalSpaceBase_familyTranslationMap]

/-- The order-four collar map covers the evident orbit of its affine base point. -/
public theorem centralBaseOrbit_orderFourPuncturedCollarToCentralFamily
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r)
    (q : (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    A.centralBaseOrbit
        (A.orderFourPuncturedCollarToCentralFamily D (Quotient.mk _ q)) =
      Quotient.mk _ (familyTotalSpaceBase A.periods q.1) := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold_analytic
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  have hmap : A.orderFourPuncturedCollarToCentralFamily D (Quotient.mk _ q) =
      Quotient.mk _ (orderFourCollarToRegular A.periods hproper D
        (orderFourPuncturedCollarGaugeDiffeomorph A.periods
          A.totalSpace_projection_isLocalDiffeomorph_analytic r q)) := by
    rw [orderFourPuncturedCollarToCentralFamily.eq_def]
    exact orderFourAffineCollarToPuncturedGlobalFamily_mk A.periods
      A.totalSpace_projection_isLocalDiffeomorph_analytic hproper hsource D q
  rw [hmap, A.centralBaseOrbit_mk]
  apply congrArg (Quotient.mk _)
  let qg := orderFourPuncturedCollarGaugeDiffeomorph A.periods
    A.totalSpace_projection_isLocalDiffeomorph_analytic r q
  have hregular :
      (regularTotalSpaceBase A.periods
        (orderFourCollarToRegular A.periods hproper D qg)).1 =
        familyTotalSpaceBase A.periods qg.1 := by
    have h := congrArg (familyTotalSpaceBase A.periods)
      (regularFamilyInclusion_orderFourCollarToRegular
        A.periods hproper D qg)
    rw [familyTotalSpaceBase_regularFamilyInclusion] at h
    exact h
  rw [hregular]
  dsimp only [qg]
  change familyTotalSpaceBase A.periods
      (orderFourPrincipalGaugeEquiv A.periods q.1) =
    familyTotalSpaceBase A.periods q.1
  rw [orderFourPrincipalGaugeEquiv.eq_def, familyTranslationEquiv_apply,
    familyTotalSpaceBase_familyTranslationMap]

/-- If a central point's base orbit has a representative in the order-three Cayley collar, then
the point itself comes from the full affine collar.  The chosen preimage has exactly the Cayley
radius of that representative. -/
public theorem exists_orderThreePuncturedCollar_preimage_of_baseOrbit_cayley
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r)
    (C : A.CentralFamily) (z : UpperHalfPlane)
    (hz : ‖(orderThreeCayleyHomeomorph z).1‖ < r)
    (hbase : A.centralBaseOrbit C = Quotient.mk _ z) :
    ∃ Q, A.orderThreePuncturedCollarToCentralFamily D Q = C ∧
      A.orderThreePuncturedCollarRadius r Q =
        ‖(orderThreeCayleyHomeomorph z).1‖ := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := triangleSourceMulAction U
  let _ := regularFamilyDeckAction A.periods
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold_analytic
  induction C using Quotient.inductionOn with
  | _ x =>
      rw [A.centralBaseOrbit_mk] at hbase
      have hrel := Quotient.exact hbase.symm
      change MulAction.orbitRel Delta UpperHalfPlane z
        (regularTotalSpaceBase A.periods x).1 at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨g, hg⟩ := hrel
      let x' := regularFamilyDeckMap A.periods g x
      have hx'base : (regularTotalSpaceBase A.periods x').1 = z := by
        rw [regularTotalSpaceBase_familyDeckMap, regularSourceEquiv_val]
        exact hg
      let y := regularFamilyInclusion A.periods x'
      have hybase : familyTotalSpaceBase A.periods y = z := by
        rw [show y = regularFamilyInclusion A.periods x' from rfl,
          familyTotalSpaceBase_regularFamilyInclusion, hx'base]
      have hypos : 0 < orderThreeFamilyRadius A.periods y := by
        rw [orderThreeFamilyRadius.eq_def, hybase, norm_pos_iff]
        intro hzero
        have hcenter : orderThreeCayleyHomeomorph z = discCenter := by
          apply Subtype.ext
          simpa [discCenter] using hzero
        have hzfixed : z = fuchsianOneFixedPoint := by
          calc
            z = orderThreeCayleyHomeomorph.symm
                (orderThreeCayleyHomeomorph z) :=
              (orderThreeCayleyHomeomorph.symm_apply_apply z).symm
            _ = orderThreeCayleyHomeomorph.symm discCenter := congrArg _ hcenter
            _ = fuchsianOneFixedPoint :=
              EllipticLocalTrivialization.orderThreeCayleyHomeomorph_symm_center
        apply A.centralBaseOrbit_ne_orderThree (Quotient.mk _ x)
        rw [A.centralBaseOrbit_mk, hbase, hzfixed,
          ← (ellipticFixedPoints_eq_of_fuchsian hsource).1]
      have hylt : orderThreeFamilyRadius A.periods y < r := by
        rw [orderThreeFamilyRadius.eq_def, hybase]
        exact hz
      let yc : orderThreePuncturedFamilyCollar A.periods r :=
        ⟨y, hypos, hylt⟩
      let gauge := orderThreePuncturedCollarGaugeDiffeomorph A.periods
        A.totalSpace_projection_isLocalDiffeomorph_analytic r
      let q : (orderThreeAffinePuncturedCarrier A.periods hsource r).carrier :=
        gauge.symm yc
      have hgauge : gauge q = yc := gauge.apply_symm_apply yc
      have hregular : orderThreeCollarToRegular A.periods hproper D (gauge q) = x' := by
        apply regularFamilyInclusion_injective A.periods
        rw [regularFamilyInclusion_orderThreeCollarToRegular]
        exact congrArg Subtype.val hgauge
      have hmap :
          A.orderThreePuncturedCollarToCentralFamily D (Quotient.mk _ q) =
            Quotient.mk _ (orderThreeCollarToRegular A.periods hproper D (gauge q)) := by
        rw [orderThreePuncturedCollarToCentralFamily.eq_def]
        exact orderThreeAffineCollarToPuncturedGlobalFamily_mk A.periods
          A.totalSpace_projection_isLocalDiffeomorph_analytic hproper hsource D q
      refine ⟨Quotient.mk _ q, ?_, ?_⟩
      · rw [hmap, hregular]
        apply Quotient.sound
        change MulAction.orbitRel Delta (RegularTotalSpace A.periods) x' x
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        exact ⟨g, rfl⟩
      · rw [A.orderThreePuncturedCollarRadius_mk]
        change orderThreeFamilyRadius A.periods q.1 = _
        rw [← orderThreeFamilyRadius_principalGauge A.periods q.1]
        change orderThreeFamilyRadius A.periods (gauge q).1 = _
        rw [hgauge, orderThreeFamilyRadius.eq_def, hybase]

/-- The analogous order-four lifting statement, again retaining the exact radial coordinate of
the chosen Cayley representative. -/
public theorem exists_orderFourPuncturedCollar_preimage_of_baseOrbit_cayley
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r)
    (C : A.CentralFamily) (z : UpperHalfPlane)
    (hz : ‖(orderFourCayleyHomeomorph z).1‖ < r)
    (hbase : A.centralBaseOrbit C = Quotient.mk _ z) :
    ∃ Q, A.orderFourPuncturedCollarToCentralFamily D Q = C ∧
      A.orderFourPuncturedCollarRadius r Q =
        ‖(orderFourCayleyHomeomorph z).1‖ := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := triangleSourceMulAction U
  let _ := regularFamilyDeckAction A.periods
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold_analytic
  induction C using Quotient.inductionOn with
  | _ x =>
      rw [A.centralBaseOrbit_mk] at hbase
      have hrel := Quotient.exact hbase.symm
      change MulAction.orbitRel Delta UpperHalfPlane z
        (regularTotalSpaceBase A.periods x).1 at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨g, hg⟩ := hrel
      let x' := regularFamilyDeckMap A.periods g x
      have hx'base : (regularTotalSpaceBase A.periods x').1 = z := by
        rw [regularTotalSpaceBase_familyDeckMap, regularSourceEquiv_val]
        exact hg
      let y := regularFamilyInclusion A.periods x'
      have hybase : familyTotalSpaceBase A.periods y = z := by
        rw [show y = regularFamilyInclusion A.periods x' from rfl,
          familyTotalSpaceBase_regularFamilyInclusion, hx'base]
      have hypos : 0 < orderFourFamilyRadius A.periods y := by
        rw [orderFourFamilyRadius.eq_def, hybase, norm_pos_iff]
        intro hzero
        have hcenter : orderFourCayleyHomeomorph z = discCenter := by
          apply Subtype.ext
          simpa [discCenter] using hzero
        have hzfixed : z = fuchsianTwoFixedPoint := by
          calc
            z = orderFourCayleyHomeomorph.symm
                (orderFourCayleyHomeomorph z) :=
              (orderFourCayleyHomeomorph.symm_apply_apply z).symm
            _ = orderFourCayleyHomeomorph.symm discCenter := congrArg _ hcenter
            _ = fuchsianTwoFixedPoint :=
              EllipticLocalTrivialization.orderFourCayleyHomeomorph_symm_center
        apply A.centralBaseOrbit_ne_orderFour (Quotient.mk _ x)
        rw [A.centralBaseOrbit_mk, hbase, hzfixed,
          ← (ellipticFixedPoints_eq_of_fuchsian hsource).2]
      have hylt : orderFourFamilyRadius A.periods y < r := by
        rw [orderFourFamilyRadius.eq_def, hybase]
        exact hz
      let yc : orderFourPuncturedFamilyCollar A.periods r :=
        ⟨y, hypos, hylt⟩
      let gauge := orderFourPuncturedCollarGaugeDiffeomorph A.periods
        A.totalSpace_projection_isLocalDiffeomorph_analytic r
      let q : (orderFourAffinePuncturedCarrier A.periods hsource r).carrier :=
        gauge.symm yc
      have hgauge : gauge q = yc := gauge.apply_symm_apply yc
      have hregular : orderFourCollarToRegular A.periods hproper D (gauge q) = x' := by
        apply regularFamilyInclusion_injective A.periods
        rw [regularFamilyInclusion_orderFourCollarToRegular]
        exact congrArg Subtype.val hgauge
      have hmap :
          A.orderFourPuncturedCollarToCentralFamily D (Quotient.mk _ q) =
            Quotient.mk _ (orderFourCollarToRegular A.periods hproper D (gauge q)) := by
        rw [orderFourPuncturedCollarToCentralFamily.eq_def]
        exact orderFourAffineCollarToPuncturedGlobalFamily_mk A.periods
          A.totalSpace_projection_isLocalDiffeomorph_analytic hproper hsource D q
      refine ⟨Quotient.mk _ q, ?_, ?_⟩
      · rw [hmap, hregular]
        apply Quotient.sound
        change MulAction.orbitRel Delta (RegularTotalSpace A.periods) x' x
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        exact ⟨g, rfl⟩
      · rw [A.orderFourPuncturedCollarRadius_mk]
        change orderFourFamilyRadius A.periods q.1 = _
        rw [← orderFourFamilyRadius_principalGauge A.periods q.1]
        change orderFourFamilyRadius A.periods (gauge q).1 = _
        rw [hgauge, orderFourFamilyRadius.eq_def, hybase]

/-- Every central point has a neighborhood avoiding the sufficiently small order-three end. -/
public theorem exists_orderThreeCentralNeighborhood_avoids_small_collar
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r)
    (C : A.CentralFamily) :
    ∃ V : Set A.CentralFamily, IsOpen V ∧ C ∈ V ∧
      ∃ s : ℝ, 0 < s ∧ ∀ Q,
        A.orderThreePuncturedCollarRadius r Q < s →
          A.orderThreePuncturedCollarToCentralFamily D Q ∉ V := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := triangleSourceMulAction U
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    sourceActionProperlyDiscontinuous_to_instance hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane := ⟨fun g => by
    change Continuous (fun z : UpperHalfPlane => U.sourceAction g • z)
    rw [hsource]
    exact (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let q : UpperHalfPlane → A.FullBaseOrbitSpace := Quotient.mk _
  obtain ⟨S, T, hSopen, hTopen, hCS, hcenterT, hST⟩ :=
    t2_separation (A.centralBaseOrbit_ne_orderThree C)
  let V := A.centralBaseOrbit ⁻¹' S
  have hVopen : IsOpen V := hSopen.preimage A.centralBaseOrbit_continuous
  have hCV : C ∈ V := hCS
  have hpreOpen : IsOpen (q ⁻¹' T) := hTopen.preimage continuous_quot_mk
  have hfixed := ellipticFixedPoints_eq_of_fuchsian hsource
  have hone : fuchsianOneFixedPoint ∈ q ⁻¹' T := by
    change q fuchsianOneFixedPoint ∈ T
    rw [← hfixed.1]
    exact hcenterT
  obtain ⟨s, hs, _, hsT⟩ :=
    exists_cayleyRadius_subset fuchsianOneFixedPoint hpreOpen hone
  refine ⟨V, hVopen, hCV, s, hs, ?_⟩
  intro Q hsmall hmem
  induction Q using Quotient.inductionOn with
  | _ x =>
      have hxT : q (familyTotalSpaceBase A.periods x.1) ∈ T := by
        apply hsT
        change ‖(orderThreeCayleyHomeomorph
          (familyTotalSpaceBase A.periods x.1) : ℂ)‖ < s
        simpa only [A.orderThreePuncturedCollarRadius_mk,
          orderThreeFamilyRadius.eq_def] using hsmall
      have hxS : q (familyTotalSpaceBase A.periods x.1) ∈ S := by
        change A.centralBaseOrbit
          (A.orderThreePuncturedCollarToCentralFamily D (Quotient.mk _ x)) ∈ S at hmem
        rwa [A.centralBaseOrbit_orderThreePuncturedCollarToCentralFamily] at hmem
      exact Set.disjoint_left.mp hST hxS hxT

/-- Every central point has a neighborhood avoiding the sufficiently small order-four end. -/
public theorem exists_orderFourCentralNeighborhood_avoids_small_collar
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r)
    (C : A.CentralFamily) :
    ∃ V : Set A.CentralFamily, IsOpen V ∧ C ∈ V ∧
      ∃ s : ℝ, 0 < s ∧ ∀ Q,
        A.orderFourPuncturedCollarRadius r Q < s →
          A.orderFourPuncturedCollarToCentralFamily D Q ∉ V := by
  let U := A.modular.modularParameter.toTriangleUniformization
  let hsource : U.sourceAction = fuchsianSourceAction :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hproper : SourceActionProperlyDiscontinuous (U := U) :=
    sourceActionProperlyDiscontinuous_of_eq hsource
  let _ := triangleSourceMulAction U
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane :=
    sourceActionProperlyDiscontinuous_to_instance hproper
  let _ : ContinuousConstSMul Delta UpperHalfPlane := ⟨fun g => by
    change Continuous (fun z : UpperHalfPlane => U.sourceAction g • z)
    rw [hsource]
    exact (fuchsianSourceAction_contMDiff g 0).continuous⟩
  let q : UpperHalfPlane → A.FullBaseOrbitSpace := Quotient.mk _
  obtain ⟨S, T, hSopen, hTopen, hCS, hcenterT, hST⟩ :=
    t2_separation (A.centralBaseOrbit_ne_orderFour C)
  let V := A.centralBaseOrbit ⁻¹' S
  have hVopen : IsOpen V := hSopen.preimage A.centralBaseOrbit_continuous
  have hCV : C ∈ V := hCS
  have hpreOpen : IsOpen (q ⁻¹' T) := hTopen.preimage continuous_quot_mk
  have hfixed := ellipticFixedPoints_eq_of_fuchsian hsource
  have htwo : fuchsianTwoFixedPoint ∈ q ⁻¹' T := by
    change q fuchsianTwoFixedPoint ∈ T
    rw [← hfixed.2]
    exact hcenterT
  obtain ⟨s, hs, _, hsT⟩ :=
    exists_cayleyRadius_subset fuchsianTwoFixedPoint hpreOpen htwo
  refine ⟨V, hVopen, hCV, s, hs, ?_⟩
  intro Q hsmall hmem
  induction Q using Quotient.inductionOn with
  | _ x =>
      have hxT : q (familyTotalSpaceBase A.periods x.1) ∈ T := by
        apply hsT
        change ‖(orderFourCayleyHomeomorph
          (familyTotalSpaceBase A.periods x.1) : ℂ)‖ < s
        simpa only [A.orderFourPuncturedCollarRadius_mk,
          orderFourFamilyRadius.eq_def] using hsmall
      have hxS : q (familyTotalSpaceBase A.periods x.1) ∈ S := by
        change A.centralBaseOrbit
          (A.orderFourPuncturedCollarToCentralFamily D (Quotient.mk _ x)) ∈ S at hmem
        rwa [A.centralBaseOrbit_orderFourPuncturedCollarToCentralFamily] at hmem
      exact Set.disjoint_left.mp hST hxS hxT

public theorem orderThreePuncturedCollarToCentralFamily_isOpenEmbedding
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsOpenEmbedding (A.orderThreePuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  exact orderThreeAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

public theorem orderFourPuncturedCollarToCentralFamily_isOpenEmbedding
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsOpenEmbedding (A.orderFourPuncturedCollarToCentralFamily D) := by
  let _ := A.totalSpaceCharts
  exact orderFourAffineCollarToPuncturedGlobalFamily_isOpenEmbedding_actual A.periods
    A.totalSpace_projection_isLocalDiffeomorph
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
    A.modular.modularParameter.toTriangleUniformization_sourceAction D

/-- On every closed annulus away from the collapsed order-three center, the paired
central/filling collar map has compact image. -/
public theorem orderThreePuncturedCollarPairClosedAnnulus_isCompact
    {s t r : ℝ} (hs : 0 < s) (htr : t < r) (hr : r < 1)
    (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsCompact ((fun Q =>
      (A.orderThreePuncturedCollarToCentralFamily D Q,
        A.orderThreePuncturedCollarToFilling r Q)) ''
      {Q | s ≤ A.orderThreePuncturedCollarRadius r Q ∧
        A.orderThreePuncturedCollarRadius r Q ≤ t}) :=
  (A.orderThreePuncturedCollarClosedAnnulus_isCompact hs htr hr).image
    ((A.orderThreePuncturedCollarToCentralFamily_isOpenEmbedding D).continuous.prodMk
      (A.orderThreePuncturedCollarToFilling_continuous r))

/-- On every closed annulus away from the collapsed order-four center, the paired
central/filling collar map has compact image. -/
public theorem orderFourPuncturedCollarPairClosedAnnulus_isCompact
    {s t r : ℝ} (hs : 0 < s) (htr : t < r) (hr : r < 1)
    (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    IsCompact ((fun Q =>
      (A.orderFourPuncturedCollarToCentralFamily D Q,
        A.orderFourPuncturedCollarToFilling r Q)) ''
      {Q | s ≤ A.orderFourPuncturedCollarRadius r Q ∧
        A.orderFourPuncturedCollarRadius r Q ≤ t}) :=
  (A.orderFourPuncturedCollarClosedAnnulus_isCompact hs htr hr).image
    ((A.orderFourPuncturedCollarToCentralFamily_isOpenEmbedding D).continuous.prodMk
      (A.orderFourPuncturedCollarToFilling_continuous r))

/-- The selected order-three collar map into the central family is locally biholomorphic for the
canonical paper atlases. -/
public theorem orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.orderThreePuncturedCollarProductCharts r
    letI := A.centralFamilyProductCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderThreePuncturedCollarToCentralFamily D) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hsource := A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold_analytic
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound
      (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  have hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace A.periods) := hregular.1
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian A.periods hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  let _ := A.orderThreePuncturedCollarProductCharts r
  let _ := A.centralFamilyProductCharts
  have hinclusion := regularFamilyInclusion_isLocalDiffeomorph_actual A.periods hproper
  have hcollar := orderThreeCollarToRegular_isLocalDiffeomorph
    A.periods hproper D hinclusion
  have htargetData :=
    puncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
      A.periods hsource hproper
  have htarget : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder
      (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace A.periods))) := by
    simpa only [quotientProjection.eq_def, centralFamilyProductCharts.eq_def] using
      htargetData.2
  change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
    RegularSmoothnessOrder
    (orderThreeAffineCollarToPuncturedGlobalFamily A.periods
      A.totalSpace_projection_isLocalDiffeomorph_analytic hproper hsource D)
  exact orderThreeAffineCollarToPuncturedGlobalFamily_isLocalDiffeomorph_of_projections
    A.periods A.totalSpace_projection_isLocalDiffeomorph_analytic
      A.totalSpace_projection_isLocalDiffeomorph hproper hsource D hcollar htarget

/-- The selected order-four collar map into the central family is locally biholomorphic for the
same canonical paper atlases. -/
public theorem orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.orderFourPuncturedCollarProductCharts r
    letI := A.centralFamilyProductCharts
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel RegularSmoothnessOrder
      (A.orderFourPuncturedCollarToCentralFamily D) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction
  let hsource := A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel ω
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold_analytic
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap A.periods)
  let _ := familyContinuousConstSMul (regularParameterMap A.periods)
    fun a => (regularPeriodSection_contMDiff A.periods hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound
      (regularParameterMap A.periods)
      (regularParameterMap_compactUniformLowerBound A.periods))
  have hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    A.periods hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace A.periods) := hregular.1
  let _ : LocallyCompactSpace (RegularTotalSpace A.periods) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction A.periods
  let _ : IsCancelSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian A.periods hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source A.periods hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace A.periods) :=
    regularFamilyDeckAction_continuousConstSMul A.periods hproper
  let _ := A.orderFourPuncturedCollarProductCharts r
  let _ := A.centralFamilyProductCharts
  have hinclusion := regularFamilyInclusion_isLocalDiffeomorph_actual A.periods hproper
  have hcollar := orderFourCollarToRegular_isLocalDiffeomorph
    A.periods hproper D hinclusion
  have htargetData :=
    puncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
      A.periods hsource hproper
  have htarget : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder
      (Quotient.mk (MulAction.orbitRel Delta (RegularTotalSpace A.periods))) := by
    simpa only [quotientProjection.eq_def, centralFamilyProductCharts.eq_def] using
      htargetData.2
  change IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
    RegularSmoothnessOrder
    (orderFourAffineCollarToPuncturedGlobalFamily A.periods
      A.totalSpace_projection_isLocalDiffeomorph_analytic hproper hsource D)
  exact orderFourAffineCollarToPuncturedGlobalFamily_isLocalDiffeomorph_of_projections
    A.periods A.totalSpace_projection_isLocalDiffeomorph_analytic
      A.totalSpace_projection_isLocalDiffeomorph hproper hsource D hcollar htarget

/-- The order-three collar-to-filling map is locally biholomorphic in the canonical `ℂ³`
atlases used by the four-piece paper gluing. -/
public theorem orderThreePuncturedCollarToFilling_isLocalDiffeomorph_complex (r : ℝ) :
    letI := A.orderThreePuncturedCollarComplexCharts r
    letI := A.orderThreeFillingComplexCharts r
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderThreePuncturedCollarToFilling r) := by
  let _ := A.orderThreePuncturedCollarProductCharts r
  let _ := A.orderThreeFillingProductCharts r
  exact globalDeckComplexLocalDiffeomorph
    (A.orderThreePuncturedCollarToFilling_isLocalDiffeomorph r)

/-- The order-four collar-to-filling map is locally biholomorphic in the canonical `ℂ³`
atlases used by the four-piece paper gluing. -/
public theorem orderFourPuncturedCollarToFilling_isLocalDiffeomorph_complex (r : ℝ) :
    letI := A.orderFourPuncturedCollarComplexCharts r
    letI := A.orderFourFillingComplexCharts r
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderFourPuncturedCollarToFilling r) := by
  let _ := A.orderFourPuncturedCollarProductCharts r
  let _ := A.orderFourFillingProductCharts r
  exact globalDeckComplexLocalDiffeomorph
    (A.orderFourPuncturedCollarToFilling_isLocalDiffeomorph r)

/-- The order-three collar-to-central-family map is locally biholomorphic in the canonical
`ComplexModel` atlases. -/
public theorem orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
    {r : ℝ} (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.orderThreePuncturedCollarComplexCharts r
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderThreePuncturedCollarToCentralFamily D) := by
  let _ := A.orderThreePuncturedCollarProductCharts r
  let _ := A.centralFamilyProductCharts
  exact globalDeckComplexLocalDiffeomorph
    (A.orderThreePuncturedCollarToCentralFamily_isLocalDiffeomorph D)

/-- The order-four collar-to-central-family map is locally biholomorphic in the canonical
`ComplexModel` atlases. -/
public theorem orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph_complex
    {r : ℝ} (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    letI := A.orderFourPuncturedCollarComplexCharts r
    letI := A.centralFamilyComplexCharts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.orderFourPuncturedCollarToCentralFamily D) := by
  let _ := A.orderFourPuncturedCollarProductCharts r
  let _ := A.centralFamilyProductCharts
  exact globalDeckComplexLocalDiffeomorph
    (A.orderFourPuncturedCollarToCentralFamily_isLocalDiffeomorph D)

public structure OrderThreeFillingPiece where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  sourceData : OrderThreeLinearCollarSourceData
    (U := A.modular.modularParameter.toTriangleUniformization) radius

public structure OrderFourFillingPiece where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  sourceData : OrderFourLinearCollarSourceData
    (U := A.modular.modularParameter.toTriangleUniformization) radius

public theorem orderThreeLinearCollarSourceData_mono {r' r : ℝ} (hrr : r' ≤ r)
    (D : OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    OrderThreeLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r' := by
  rw [OrderThreeLinearCollarSourceData.eq_def] at D ⊢
  constructor
  · intro z hz hzr
    exact D.1 z hz (hzr.trans_le hrr)
  · intro z x hzr hxr g hg
    exact D.2 z x (hzr.trans_le hrr) (hxr.trans_le hrr) g hg

public theorem orderFourLinearCollarSourceData_mono {r' r : ℝ} (hrr : r' ≤ r)
    (D : OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r) :
    OrderFourLinearCollarSourceData
      (U := A.modular.modularParameter.toTriangleUniformization) r' := by
  rw [OrderFourLinearCollarSourceData.eq_def] at D ⊢
  constructor
  · intro z hz hzr
    exact D.1 z hz (hzr.trans_le hrr)
  · intro z x hzr hxr g hg
    exact D.2 z x (hzr.trans_le hrr) (hxr.trans_le hrr) g hg

public theorem exists_orderThreeFillingPiece : Nonempty A.OrderThreeFillingPiece := by
  obtain ⟨r, hr, hr1, D⟩ := exists_orderThreeLinearCollarSourceData
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact ⟨⟨r, hr, hr1, D⟩⟩

public theorem exists_orderFourFillingPiece : Nonempty A.OrderFourFillingPiece := by
  obtain ⟨r, hr, hr1, D⟩ := exists_orderFourLinearCollarSourceData
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    (sourceActionProperlyDiscontinuous_of_eq
      A.modular.modularParameter.toTriangleUniformization_sourceAction)
  exact ⟨⟨r, hr, hr1, D⟩⟩

public theorem exists_orderThreeFillingPiece_below {R : ℝ} (hR : 0 < R) :
    ∃ P : A.OrderThreeFillingPiece, P.radius < R := by
  obtain ⟨P⟩ := A.exists_orderThreeFillingPiece
  let r := min P.radius (R / 2)
  have hr : 0 < r := lt_min P.radius_pos (half_pos hR)
  have hrr : r ≤ P.radius := min_le_left _ _
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  exact ⟨⟨r, hr, hrr.trans_lt P.radius_lt_one,
    A.orderThreeLinearCollarSourceData_mono hrr P.sourceData⟩, hrR⟩

public theorem exists_orderFourFillingPiece_below {R : ℝ} (hR : 0 < R) :
    ∃ P : A.OrderFourFillingPiece, P.radius < R := by
  obtain ⟨P⟩ := A.exists_orderFourFillingPiece
  let r := min P.radius (R / 2)
  have hr : 0 < r := lt_min P.radius_pos (half_pos hR)
  have hrr : r ≤ P.radius := min_le_left _ _
  have hrR : r < R := (min_le_right _ _).trans_lt (half_lt_self hR)
  exact ⟨⟨r, hr, hrr.trans_lt P.radius_lt_one,
    A.orderFourLinearCollarSourceData_mono hrr P.sourceData⟩, hrR⟩

@[expose] public noncomputable def orderThreeFillingPiece : A.OrderThreeFillingPiece :=
  Classical.choice A.exists_orderThreeFillingPiece

@[expose] public noncomputable def orderFourFillingPiece : A.OrderFourFillingPiece :=
  Classical.choice A.exists_orderFourFillingPiece

public abbrev SelectedOrderThreeFilling :=
  A.OrderThreeVaryingFilling A.orderThreeFillingPiece.radius

public abbrev SelectedOrderFourFilling :=
  A.OrderFourVaryingFilling A.orderFourFillingPiece.radius

public abbrev ComplexDiscBall (r : ℝ) :=
  {w : ComplexUnitDisc // ‖(w : ℂ)‖ < r}

/-- The punctured Cayley-coordinate disc underlying either common elliptic collar. -/
public abbrev ComplexDiscPuncturedBall (r : ℝ) :=
  {w : ComplexUnitDisc // 0 < ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ < r}

/-- Angular motion in the complex plane through angle `theta`. -/
@[expose] public noncomputable def complexAngularPath (theta : ℝ) (w : ℂ) :
    Path w (Complex.exp ((theta : ℂ) * Complex.I) * w) where
  toFun t := Complex.exp (((t : ℝ) * theta : ℝ) * Complex.I) * w
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

public theorem norm_complexAngularPath (theta : ℝ) (w : ℂ) (t : unitInterval) :
    ‖complexAngularPath theta w t‖ = ‖w‖ := by
  change ‖Complex.exp ((((t : ℝ) * theta : ℝ) : ℂ) * Complex.I) * w‖ = ‖w‖
  rw [norm_mul, Complex.norm_exp]
  simp

/-- Angular motion preserves both inequalities defining the punctured disc. -/
@[expose] public noncomputable def complexDiscPuncturedBallAngularPath
    {r : ℝ} (theta : ℝ) (w : ComplexDiscPuncturedBall r) :
    Path w
      ⟨⟨Complex.exp ((theta : ℂ) * Complex.I) * w.1.1, by
          rw [norm_mul, Complex.norm_exp]
          simpa using w.1.2⟩,
        by
          rw [norm_mul, Complex.norm_exp]
          simpa using w.2⟩ :=
  { toFun := fun t =>
      ⟨⟨complexAngularPath theta w.1.1 t, by
          rw [norm_complexAngularPath]
          exact w.1.2⟩,
        by
          rw [norm_complexAngularPath]
          exact w.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact (complexAngularPath theta w.1.1).continuous
    source' := by
      apply Subtype.ext
      apply Subtype.ext
      simp
    target' := by
      apply Subtype.ext
      apply Subtype.ext
      simp }

public theorem exp_arg_mul_I_eq_of_norm_eq_one (lambda : ℂ)
    (hlambda : ‖lambda‖ = 1) :
    Complex.exp ((Complex.arg lambda : ℂ) * Complex.I) = lambda := by
  simpa [hlambda] using Complex.norm_mul_exp_arg_mul_I lambda

/-- The principal-argument angular path from `w` to multiplication by a unit scalar. -/
@[expose] public noncomputable def complexAngularPathToUnit
    (lambda : ℂ) (hlambda : ‖lambda‖ = 1) (w : ℂ) :
    Path w (lambda * w) :=
  (complexAngularPath (Complex.arg lambda) w).cast rfl
    (by rw [exp_arg_mul_I_eq_of_norm_eq_one lambda hlambda])

/-- Multiplication by a unit scalar on the punctured Cayley-coordinate disc. -/
@[expose] public noncomputable def complexDiscPuncturedBallScalar
    {r : ℝ} (lambda : ℂ) (hlambda : ‖lambda‖ = 1)
    (w : ComplexDiscPuncturedBall r) : ComplexDiscPuncturedBall r :=
  ⟨⟨lambda * w.1.1, by simpa [norm_mul, hlambda] using w.1.2⟩,
    by simpa [norm_mul, hlambda] using w.2⟩

/-- Multiplication by a unit scalar is continuous on the punctured Cayley disc. -/
public theorem complexDiscPuncturedBallScalar_continuous
    {r : ℝ} (lambda : ℂ) (hlambda : ‖lambda‖ = 1) :
    Continuous (complexDiscPuncturedBallScalar (r := r) lambda hlambda) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  fun_prop

/-- The principal-argument angular path inside the punctured disc. -/
@[expose] public noncomputable def complexDiscPuncturedBallAngularPathToUnit
    {r : ℝ} (lambda : ℂ) (hlambda : ‖lambda‖ = 1)
    (w : ComplexDiscPuncturedBall r) :
    Path w (complexDiscPuncturedBallScalar lambda hlambda w) :=
  (complexDiscPuncturedBallAngularPath (Complex.arg lambda) w).cast rfl (by
    apply Subtype.ext
    apply Subtype.ext
    change lambda * w.1.1 =
      Complex.exp ((Complex.arg lambda : ℂ) * Complex.I) * w.1.1
    rw [exp_arg_mul_I_eq_of_norm_eq_one lambda hlambda])

/-- The angular path through the order-three elliptic base rotation. -/
@[expose] public noncomputable def orderThreeDiscPuncturedPath
    {r : ℝ} (w : ComplexDiscPuncturedBall r) :
    Path w (complexDiscPuncturedBallScalar orderThreeMultiplier
      norm_orderThreeMultiplier w) :=
  complexDiscPuncturedBallAngularPathToUnit orderThreeMultiplier
    norm_orderThreeMultiplier w

public theorem orderThreeDiscPuncturedPath_target_val {r : ℝ}
    (w : ComplexDiscPuncturedBall r) :
    (complexDiscPuncturedBallScalar orderThreeMultiplier
      norm_orderThreeMultiplier w).1 = orderThreeDiscRotation w.1 := by
  apply Subtype.ext
  change orderThreeMultiplier * w.1.1 = (orderThreeDiscRotation w.1).1
  exact (discScalarEquiv_apply_val orderThreeMultiplier
    norm_orderThreeMultiplier w.1).symm

/-- The angular path through the order-four elliptic base rotation. -/
@[expose] public noncomputable def orderFourDiscPuncturedPath
    {r : ℝ} (w : ComplexDiscPuncturedBall r) :
    Path w (complexDiscPuncturedBallScalar orderFourMultiplier
      norm_orderFourMultiplier w) :=
  complexDiscPuncturedBallAngularPathToUnit orderFourMultiplier
    norm_orderFourMultiplier w

public theorem orderFourDiscPuncturedPath_target_val {r : ℝ}
    (w : ComplexDiscPuncturedBall r) :
    (complexDiscPuncturedBallScalar orderFourMultiplier
      norm_orderFourMultiplier w).1 = orderFourDiscRotation w.1 := by
  apply Subtype.ext
  change orderFourMultiplier * w.1.1 = (orderFourDiscRotation w.1).1
  exact (discScalarEquiv_apply_val orderFourMultiplier
    norm_orderFourMultiplier w.1).symm

/-- Polar coordinates cover the punctured Cayley-coordinate disc. -/
@[expose] public noncomputable def complexDiscPuncturedBallRadialCover
    {r : ℝ} (hr1 : r < 1) :
    Set.Ioo (0 : ℝ) r × Metric.sphere (0 : ℂ) 1 →
      ComplexDiscPuncturedBall r := fun p => by
  have hu : ‖p.2.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.2.2
  have hn : ‖p.1.1 • p.2.1‖ = p.1.1 := by
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos p.1.2.1]
  exact ⟨⟨p.1.1 • p.2.1, by rw [hn]; exact p.1.2.2.trans hr1⟩,
    ⟨by rw [hn]; exact p.1.2.1, by rw [hn]; exact p.1.2.2⟩⟩

public theorem complexDiscPuncturedBallRadialCover_continuous
    {r : ℝ} (hr1 : r < 1) :
    Continuous (complexDiscPuncturedBallRadialCover hr1) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

public theorem complexDiscPuncturedBallRadialCover_surjective
    {r : ℝ} (hr1 : r < 1) :
    Function.Surjective (complexDiscPuncturedBallRadialCover hr1) := by
  rintro ⟨⟨w, hw1⟩, hw0, hwr⟩
  have hn : ‖w‖ ≠ 0 := ne_of_gt hw0
  let s : Set.Ioo (0 : ℝ) r := ⟨‖w‖, hw0, hwr⟩
  let u : Metric.sphere (0 : ℂ) 1 := ⟨‖w‖⁻¹ • w, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hn]⟩
  refine ⟨(s, u), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ‖w‖ • (‖w‖⁻¹ • w) = w
  rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

@[expose] public noncomputable def complexDiscBallHomeomorph
    {r : ℝ} (hr1 : r < 1) : ComplexDiscBall r ≃ₜ Metric.ball (0 : ℂ) r where
  toFun w := ⟨w.1.1, by
    simpa only [Metric.mem_ball, dist_zero_right] using w.2⟩
  invFun w :=
    let hw : ‖(w.1 : ℂ)‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using w.2
    ⟨⟨w.1, hw.trans hr1⟩, hw⟩
  left_inv w := by
    apply Subtype.ext
    rfl
  right_inv w := by
    apply Subtype.ext
    rfl
  continuous_toFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _

/-- The filled Cayley-coordinate disc is contractible. -/
public theorem complexDiscBall_contractible {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContractibleSpace (ComplexDiscBall r) := by
  let _ : ContractibleSpace (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).contractibleSpace (Metric.nonempty_ball.mpr hr)
  exact (complexDiscBallHomeomorph hr1).contractibleSpace

/-- Include the punctured Cayley disc into the full filling disc. -/
@[expose] public noncomputable def complexDiscPuncturedBallToBall {r : ℝ} :
    C(ComplexDiscPuncturedBall r, ComplexDiscBall r) :=
  ⟨fun w => ⟨w.1, w.2.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩

/-- Include the punctured affine cover into the full disc-times-vector-space filling cover. -/
@[expose] public noncomputable def complexDiscPuncturedCoverToBallCover {r : ℝ} :
    C(ComplexDiscPuncturedBall r × ComplexTwoSpace,
      ComplexDiscBall r × ComplexTwoSpace) :=
  (complexDiscPuncturedBallToBall (r := r)).prodMap (ContinuousMap.id _)

public theorem complexDiscBall_connected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ConnectedSpace (ComplexDiscBall r) := by
  let _ : ConnectedSpace (Metric.ball (0 : ℂ) r) := by
    apply isConnected_iff_connectedSpace.mp
    exact ⟨Metric.nonempty_ball.mpr hr, (convex_ball (0 : ℂ) r).isPreconnected⟩
  exact (complexDiscBallHomeomorph hr1).symm.surjective.connectedSpace
    (complexDiscBallHomeomorph hr1).symm.continuous

/-- The Cayley-coordinate disc used to cover each elliptic filling is path connected. -/
public theorem complexDiscBall_pathConnected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (ComplexDiscBall r) := by
  have hball : IsPathConnected (Metric.ball (0 : ℂ) r) :=
    (convex_ball (0 : ℂ) r).isPathConnected (Metric.nonempty_ball.mpr hr)
  let _ : PathConnectedSpace (Metric.ball (0 : ℂ) r) :=
    isPathConnected_iff_pathConnectedSpace.mp hball
  exact (complexDiscBallHomeomorph hr1).symm.surjective.pathConnectedSpace
    (complexDiscBallHomeomorph hr1).symm.continuous

/-- The punctured Cayley-coordinate disc is path connected: polar radius lies in `(0,r)`,
while its unit complex direction lies on a path-connected circle. -/
public theorem complexDiscPuncturedBall_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (ComplexDiscPuncturedBall r) := by
  have hIoo : IsPathConnected (Set.Ioo (0 : ℝ) r) :=
    (convex_Ioo (𝕜 := ℝ) 0 r).isPathConnected
      ⟨r / 2, half_pos hr, half_lt_self hr⟩
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank]
    norm_num [Complex.finrank_real_complex]
  have hsphere : IsPathConnected (Metric.sphere (0 : ℂ) 1) :=
    isPathConnected_sphere hrank 0 (by norm_num)
  let _ : PathConnectedSpace (Set.Ioo (0 : ℝ) r) :=
    isPathConnected_iff_pathConnectedSpace.mp hIoo
  let _ : PathConnectedSpace (Metric.sphere (0 : ℂ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp hsphere
  exact (complexDiscPuncturedBallRadialCover_surjective hr1).pathConnectedSpace
    (complexDiscPuncturedBallRadialCover_continuous hr1)

@[expose] public noncomputable def orderThreeFillingCoverMap (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace → A.orderThreeFillingOpen r := fun p =>
  ⟨Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2), by
    rw [orderThreeFillingOpen]
    change orderThreeFamilyRadius A.periods
      (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)) < r
    rw [orderThreeFamilyRadius.eq_def,
      familyTotalSpaceBase_mk, orderThreeCayleyHomeomorph.apply_symm_apply]
    exact p.1.2⟩

@[expose] public noncomputable def orderFourFillingCoverMap (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace → A.orderFourFillingOpen r := fun p =>
  ⟨Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2), by
    rw [orderFourFillingOpen]
    change orderFourFamilyRadius A.periods
      (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2)) < r
    rw [orderFourFamilyRadius.eq_def,
      familyTotalSpaceBase_mk, orderFourCayleyHomeomorph.apply_symm_apply]
    exact p.1.2⟩

public theorem orderThreeFillingCoverMap_continuous (r : ℝ) :
    Continuous (A.orderThreeFillingCoverMap r) := by
  unfold orderThreeFillingCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscBall r × ComplexTwoSpace => (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderThreeCayleyHomeomorph.symm.continuous.comp
      hfst).prodMk continuous_snd)

public theorem orderFourFillingCoverMap_continuous (r : ℝ) :
    Continuous (A.orderFourFillingCoverMap r) := by
  unfold orderFourFillingCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscBall r × ComplexTwoSpace => (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderFourCayleyHomeomorph.symm.continuous.comp
      hfst).prodMk continuous_snd)

public theorem orderThreeFillingCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderThreeFillingCoverMap r) := by
  rintro ⟨q, hq⟩
  change orderThreeFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderThreeCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderThreeFillingCoverMap.eq_def]
      change Quotient.mk _
        (orderThreeCayleyHomeomorph.symm (orderThreeCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderThreeCayleyHomeomorph.symm_apply_apply]

public theorem orderFourFillingCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderFourFillingCoverMap r) := by
  rintro ⟨q, hq⟩
  change orderFourFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderFourCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderFourFillingCoverMap.eq_def]
      change Quotient.mk _
        (orderFourCayleyHomeomorph.symm (orderFourCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderFourCayleyHomeomorph.symm_apply_apply]

/-- The punctured Cayley disc times the affine fibre covers the order-three collar before its
finite cyclic quotient. -/
@[expose] public noncomputable def orderThreePuncturedCoverMap (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := fun p =>
  ⟨Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2), by
    change 0 < orderThreeFamilyRadius A.periods
        (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)) ∧
      orderThreeFamilyRadius A.periods
        (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2)) < r
    simpa only [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk,
      orderThreeCayleyHomeomorph.apply_symm_apply] using p.1.2⟩

/-- The analogous affine cover of the order-four collar before its finite cyclic quotient. -/
@[expose] public noncomputable def orderFourPuncturedCoverMap (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := fun p =>
  ⟨Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2), by
    change 0 < orderFourFamilyRadius A.periods
        (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2)) ∧
      orderFourFamilyRadius A.periods
        (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2)) < r
    simpa only [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk,
      orderFourCayleyHomeomorph.apply_symm_apply] using p.1.2⟩

public theorem orderThreePuncturedCoverMap_continuous (r : ℝ) :
    Continuous (A.orderThreePuncturedCoverMap r) := by
  unfold orderThreePuncturedCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscPuncturedBall r × ComplexTwoSpace =>
        (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderThreeCayleyHomeomorph.symm.continuous.comp hfst).prodMk continuous_snd)

public theorem orderFourPuncturedCoverMap_continuous (r : ℝ) :
    Continuous (A.orderFourPuncturedCoverMap r) := by
  unfold orderFourPuncturedCoverMap
  apply Continuous.subtype_mk
  have hfst : Continuous
      (fun p : ComplexDiscPuncturedBall r × ComplexTwoSpace =>
        (p.1 : ComplexUnitDisc)) :=
    continuous_subtype_val.comp continuous_fst
  exact continuous_quot_mk.comp
    ((orderFourCayleyHomeomorph.symm.continuous.comp hfst).prodMk continuous_snd)

public theorem orderThreePuncturedCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderThreePuncturedCoverMap r) := by
  rintro ⟨q, hq⟩
  change 0 < orderThreeFamilyRadius A.periods q ∧
    orderThreeFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderThreeCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderThreePuncturedCoverMap.eq_def]
      change Quotient.mk _
        (orderThreeCayleyHomeomorph.symm (orderThreeCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderThreeCayleyHomeomorph.symm_apply_apply]

public theorem orderFourPuncturedCoverMap_surjective (r : ℝ) :
    Function.Surjective (A.orderFourPuncturedCoverMap r) := by
  rintro ⟨q, hq⟩
  change 0 < orderFourFamilyRadius A.periods q ∧
    orderFourFamilyRadius A.periods q < r at hq
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨(⟨orderFourCayleyHomeomorph p.1, ?_⟩, p.2), ?_⟩
    · simpa [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk] using hq
    · apply Subtype.ext
      rw [orderFourPuncturedCoverMap.eq_def]
      change Quotient.mk _
        (orderFourCayleyHomeomorph.symm (orderFourCayleyHomeomorph p.1), p.2) =
          Quotient.mk _ p
      rw [orderFourCayleyHomeomorph.symm_apply_apply]

/-- The order-three affine generator written on the punctured-disc times vector-space cover. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverGenerator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace :=
  let w' := complexDiscPuncturedBallScalar orderThreeMultiplier
    norm_orderThreeMultiplier p.1
  (w', orderThreeTwistSection A.periods (orderThreeCayleyHomeomorph.symm w'.1) +
    periodTransport g₁
      (parameterMap A.periods (orderThreeCayleyHomeomorph.symm p.1.1)) p.2)

/-- The explicit order-three cover generator maps to the actual cyclic action. -/
public theorem orderThreePuncturedCoverMap_generator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := restrictedMulAction
      (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)
    A.orderThreePuncturedCoverMap r
        (orderThreeAffinePuncturedCoverGenerator A p) =
      cyclicGenerator 3 • A.orderThreePuncturedCoverMap r p := by
  let hsource :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods hsource r)
  apply Subtype.ext
  rw [orderThreePuncturedCoverMap]
  change Quotient.mk _
      (orderThreeCayleyHomeomorph.symm
          (orderThreeAffinePuncturedCoverGenerator A p).1.1,
        (orderThreeAffinePuncturedCoverGenerator A p).2) =
    orderThreeAffineFamilyRepresentation A.periods (cyclicGenerator 3)
      (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2))
  change Quotient.mk _
      (orderThreeCayleyHomeomorph.symm
          (orderThreeAffinePuncturedCoverGenerator A p).1.1,
        (orderThreeAffinePuncturedCoverGenerator A p).2) =
    (cyclicRepresentation 3 (orderThreeAffineFamilyGenerator A.periods)
      (orderThreeAffineFamilyGenerator_pow A.periods))
        (Multiplicative.ofAdd 1)
        (Quotient.mk _ (orderThreeCayleyHomeomorph.symm p.1.1, p.2))
  rw [cyclicRepresentation_generator]
  simp only [orderThreeAffineFamilyGenerator, Equiv.Perm.mul_apply,
    familyDeckEquiv_apply, familyDeckMap_mk, deckMap,
    familyTranslationEquiv_apply, familyTranslationMap_mk,
    familyTranslationCover]
  apply congrArg (Quotient.mk _)
  have hbase : orderThreeCayleyHomeomorph.symm
        (complexDiscPuncturedBallScalar orderThreeMultiplier
          norm_orderThreeMultiplier p.1).1 =
      A.modular.modularParameter.toTriangleUniformization.sourceAction g₁ •
        orderThreeCayleyHomeomorph.symm p.1.1 := by
    apply orderThreeCayleyHomeomorph.injective
    rw [orderThreeCayleyHomeomorph.apply_symm_apply]
    rw [hsource, orderThreeCayleyHomeomorph_generator,
      orderThreeCayleyHomeomorph.apply_symm_apply]
    exact orderThreeDiscPuncturedPath_target_val p.1
  apply Prod.ext
  · exact hbase
  · change orderThreeTwistSection A.periods
        (orderThreeCayleyHomeomorph.symm
          (complexDiscPuncturedBallScalar orderThreeMultiplier
            norm_orderThreeMultiplier p.1).1) + _ =
      orderThreeTwistSection A.periods
        (A.modular.modularParameter.toTriangleUniformization.sourceAction g₁ •
          orderThreeCayleyHomeomorph.symm p.1.1) + _
    rw [hbase]

/-- The order-three angular-and-affine path before mapping to either torus quotient. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverLiftPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path p (orderThreeAffinePuncturedCoverGenerator A p) :=
  (orderThreeDiscPuncturedPath p.1).prod
    (Path.segment p.2 (orderThreeAffinePuncturedCoverGenerator A p).2)

/-- An explicit order-three deck path: angular motion in the base and a straight fibre path. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverDeckPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := restrictedMulAction
      (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)
    Path (A.orderThreePuncturedCoverMap r p)
      (cyclicGenerator 3 • A.orderThreePuncturedCoverMap r p) := by
  let _ := restrictedMulAction
    (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  exact ((orderThreeAffinePuncturedCoverLiftPath A p).map
    (A.orderThreePuncturedCoverMap_continuous r)).cast rfl
      (A.orderThreePuncturedCoverMap_generator p).symm

/-- The order-four affine generator written on the punctured-disc times vector-space cover. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverGenerator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace :=
  let w' := complexDiscPuncturedBallScalar orderFourMultiplier
    norm_orderFourMultiplier p.1
  (w', orderFourTwistSection A.periods (orderFourCayleyHomeomorph.symm w'.1) +
    periodTransport g₂
      (parameterMap A.periods (orderFourCayleyHomeomorph.symm p.1.1)) p.2)

/-- The explicit order-four cover generator maps to the actual cyclic action. -/
public theorem orderFourPuncturedCoverMap_generator {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := restrictedMulAction
      (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)
    A.orderFourPuncturedCoverMap r
        (orderFourAffinePuncturedCoverGenerator A p) =
      cyclicGenerator 4 • A.orderFourPuncturedCoverMap r p := by
  let hsource :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods hsource r)
  apply Subtype.ext
  rw [orderFourPuncturedCoverMap]
  change Quotient.mk _
      (orderFourCayleyHomeomorph.symm
          (orderFourAffinePuncturedCoverGenerator A p).1.1,
        (orderFourAffinePuncturedCoverGenerator A p).2) =
    orderFourAffineFamilyRepresentation A.periods (cyclicGenerator 4)
      (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2))
  change Quotient.mk _
      (orderFourCayleyHomeomorph.symm
          (orderFourAffinePuncturedCoverGenerator A p).1.1,
        (orderFourAffinePuncturedCoverGenerator A p).2) =
    (cyclicRepresentation 4 (orderFourAffineFamilyGenerator A.periods)
      (orderFourAffineFamilyGenerator_pow A.periods))
        (Multiplicative.ofAdd 1)
        (Quotient.mk _ (orderFourCayleyHomeomorph.symm p.1.1, p.2))
  rw [cyclicRepresentation_generator]
  simp only [orderFourAffineFamilyGenerator, Equiv.Perm.mul_apply,
    familyDeckEquiv_apply, familyDeckMap_mk, deckMap,
    familyTranslationEquiv_apply, familyTranslationMap_mk,
    familyTranslationCover]
  apply congrArg (Quotient.mk _)
  have hbase : orderFourCayleyHomeomorph.symm
        (complexDiscPuncturedBallScalar orderFourMultiplier
          norm_orderFourMultiplier p.1).1 =
      A.modular.modularParameter.toTriangleUniformization.sourceAction g₂ •
        orderFourCayleyHomeomorph.symm p.1.1 := by
    apply orderFourCayleyHomeomorph.injective
    rw [orderFourCayleyHomeomorph.apply_symm_apply]
    rw [hsource, orderFourCayleyHomeomorph_generator,
      orderFourCayleyHomeomorph.apply_symm_apply]
    exact orderFourDiscPuncturedPath_target_val p.1
  apply Prod.ext
  · exact hbase
  · change orderFourTwistSection A.periods
        (orderFourCayleyHomeomorph.symm
          (complexDiscPuncturedBallScalar orderFourMultiplier
            norm_orderFourMultiplier p.1).1) + _ =
      orderFourTwistSection A.periods
        (A.modular.modularParameter.toTriangleUniformization.sourceAction g₂ •
          orderFourCayleyHomeomorph.symm p.1.1) + _
    rw [hbase]

/-- The order-four angular-and-affine path before mapping to either torus quotient. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverLiftPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path p (orderFourAffinePuncturedCoverGenerator A p) :=
  (orderFourDiscPuncturedPath p.1).prod
    (Path.segment p.2 (orderFourAffinePuncturedCoverGenerator A p).2)

/-- An explicit order-four deck path: angular motion in the base and a straight fibre path. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverDeckPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    let _ := restrictedMulAction
      (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r)
    Path (A.orderFourPuncturedCoverMap r p)
      (cyclicGenerator 4 • A.orderFourPuncturedCoverMap r p) := by
  let _ := restrictedMulAction
    (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r)
  exact ((orderFourAffinePuncturedCoverLiftPath A p).map
    (A.orderFourPuncturedCoverMap_continuous r)).cast rfl
      (A.orderFourPuncturedCoverMap_generator p).symm

/-- Forget the order-three punctured-radius conditions and convert the Cayley base coordinate
back to the upper half-plane. -/
@[expose] public noncomputable def orderThreePuncturedAffineCoverToFamilyCover {r : ℝ} :
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      UpperHalfPlane × ComplexTwoSpace := fun p =>
  (orderThreeCayleyHomeomorph.symm p.1.1, p.2)

public theorem orderThreePuncturedAffineCoverToFamilyCover_continuous {r : ℝ} :
    Continuous (orderThreePuncturedAffineCoverToFamilyCover (r := r)) := by
  exact (orderThreeCayleyHomeomorph.symm.continuous.comp
    (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd

public theorem orderThreePuncturedAffineCoverToFamilyCover_injective {r : ℝ} :
    Function.Injective (orderThreePuncturedAffineCoverToFamilyCover (r := r)) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    exact orderThreeCayleyHomeomorph.symm.injective (congrArg Prod.fst h)
  · exact congrArg (fun x : UpperHalfPlane × ComplexTwoSpace => x.2) h

/-- The explicit Cayley-coordinate generator is the restriction of the lifted affine family
generator on the vector-bundle cover. -/
public theorem orderThreeAffinePuncturedCoverGenerator_intertwines {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    orderThreePuncturedAffineCoverToFamilyCover
        (orderThreeAffinePuncturedCoverGenerator A p) =
      orderThreeAffineFamilyCoverGenerator A.periods
        (orderThreePuncturedAffineCoverToFamilyCover p) := by
  let hsource :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  have hbase : orderThreeCayleyHomeomorph.symm
        (complexDiscPuncturedBallScalar orderThreeMultiplier
          norm_orderThreeMultiplier p.1).1 =
      A.modular.modularParameter.toTriangleUniformization.sourceAction g₁ •
        orderThreeCayleyHomeomorph.symm p.1.1 := by
    apply orderThreeCayleyHomeomorph.injective
    rw [orderThreeCayleyHomeomorph.apply_symm_apply]
    rw [hsource, orderThreeCayleyHomeomorph_generator,
      orderThreeCayleyHomeomorph.apply_symm_apply]
    exact orderThreeDiscPuncturedPath_target_val p.1
  apply Prod.ext
  · exact hbase
  · change orderThreeTwistSection A.periods
        (orderThreeCayleyHomeomorph.symm
          (complexDiscPuncturedBallScalar orderThreeMultiplier
            norm_orderThreeMultiplier p.1).1) + _ =
      orderThreeTwistSection A.periods
        (A.modular.modularParameter.toTriangleUniformization.sourceAction g₁ •
          orderThreeCayleyHomeomorph.symm p.1.1) +
        periodTransport g₁
          (parameterMap A.periods (orderThreeCayleyHomeomorph.symm p.1.1)) p.2
    rw [hbase]

/-- The explicit order-three affine generator is continuous on the punctured Cayley cover. -/
public theorem orderThreeAffinePuncturedCoverGenerator_continuous {r : ℝ} :
    Continuous (orderThreeAffinePuncturedCoverGenerator A (r := r)) := by
  apply Continuous.prodMk
  · exact (complexDiscPuncturedBallScalar_continuous
      orderThreeMultiplier norm_orderThreeMultiplier).comp continuous_fst
  · have htotal : Continuous (fun p : ComplexDiscPuncturedBall r × ComplexTwoSpace =>
        orderThreeAffineFamilyCoverGenerator A.periods
          (orderThreePuncturedAffineCoverToFamilyCover p)) :=
      (orderThreeAffineFamilyCoverGenerator_continuous A.periods).comp
        orderThreePuncturedAffineCoverToFamilyCover_continuous
    convert continuous_snd.comp htotal using 1
    funext p
    exact congrArg Prod.snd
      (orderThreeAffinePuncturedCoverGenerator_intertwines A p)

/-- Translation by the accumulated order-three period on the explicit punctured affine cover. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverPeriodTranslate {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace :=
  (p.1, periodVector
    (parameterMap A.periods (orderThreeCayleyHomeomorph.symm p.1.1)).1
      LatticeData.epsilon + p.2)

/-- Three iterations of the explicit punctured-cover generator return to the original Cayley
base and translate the fibre by the exact integral period `epsilon`. -/
public theorem orderThreeAffinePuncturedCoverGenerator_iterate_three {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    (orderThreeAffinePuncturedCoverGenerator A)^[3] p =
      orderThreeAffinePuncturedCoverPeriodTranslate A p := by
  apply orderThreePuncturedAffineCoverToFamilyCover_injective
  have hsem : Function.Semiconj
      (orderThreePuncturedAffineCoverToFamilyCover (r := r))
      (orderThreeAffinePuncturedCoverGenerator A (r := r))
      (orderThreeAffineFamilyCoverGenerator A.periods) :=
    orderThreeAffinePuncturedCoverGenerator_intertwines A (r := r)
  rw [hsem.iterate_right 3 p]
  change (orderThreeAffineFamilyCoverGenerator A.periods ^ 3)
      (orderThreePuncturedAffineCoverToFamilyCover p) = _
  rw [orderThreeAffineFamilyCoverGenerator_pow_apply]
  rfl

/-- Forget the order-four punctured-radius conditions and convert the Cayley base coordinate
back to the upper half-plane. -/
@[expose] public noncomputable def orderFourPuncturedAffineCoverToFamilyCover {r : ℝ} :
    ComplexDiscPuncturedBall r × ComplexTwoSpace →
      UpperHalfPlane × ComplexTwoSpace := fun p =>
  (orderFourCayleyHomeomorph.symm p.1.1, p.2)

public theorem orderFourPuncturedAffineCoverToFamilyCover_continuous {r : ℝ} :
    Continuous (orderFourPuncturedAffineCoverToFamilyCover (r := r)) := by
  exact (orderFourCayleyHomeomorph.symm.continuous.comp
    (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd

public theorem orderFourPuncturedAffineCoverToFamilyCover_injective {r : ℝ} :
    Function.Injective (orderFourPuncturedAffineCoverToFamilyCover (r := r)) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    exact orderFourCayleyHomeomorph.symm.injective (congrArg Prod.fst h)
  · exact congrArg (fun x : UpperHalfPlane × ComplexTwoSpace => x.2) h

/-- The explicit order-four Cayley generator is the corresponding restricted lifted affine
family generator. -/
public theorem orderFourAffinePuncturedCoverGenerator_intertwines {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    orderFourPuncturedAffineCoverToFamilyCover
        (orderFourAffinePuncturedCoverGenerator A p) =
      orderFourAffineFamilyCoverGenerator A.periods
        (orderFourPuncturedAffineCoverToFamilyCover p) := by
  let hsource :=
    A.modular.modularParameter.toTriangleUniformization_sourceAction
  have hbase : orderFourCayleyHomeomorph.symm
        (complexDiscPuncturedBallScalar orderFourMultiplier
          norm_orderFourMultiplier p.1).1 =
      A.modular.modularParameter.toTriangleUniformization.sourceAction g₂ •
        orderFourCayleyHomeomorph.symm p.1.1 := by
    apply orderFourCayleyHomeomorph.injective
    rw [orderFourCayleyHomeomorph.apply_symm_apply]
    rw [hsource, orderFourCayleyHomeomorph_generator,
      orderFourCayleyHomeomorph.apply_symm_apply]
    exact orderFourDiscPuncturedPath_target_val p.1
  apply Prod.ext
  · exact hbase
  · change orderFourTwistSection A.periods
        (orderFourCayleyHomeomorph.symm
          (complexDiscPuncturedBallScalar orderFourMultiplier
            norm_orderFourMultiplier p.1).1) + _ =
      orderFourTwistSection A.periods
        (A.modular.modularParameter.toTriangleUniformization.sourceAction g₂ •
          orderFourCayleyHomeomorph.symm p.1.1) +
        periodTransport g₂
          (parameterMap A.periods (orderFourCayleyHomeomorph.symm p.1.1)) p.2
    rw [hbase]

/-- The explicit order-four affine generator is continuous on the punctured Cayley cover. -/
public theorem orderFourAffinePuncturedCoverGenerator_continuous {r : ℝ} :
    Continuous (orderFourAffinePuncturedCoverGenerator A (r := r)) := by
  apply Continuous.prodMk
  · exact (complexDiscPuncturedBallScalar_continuous
      orderFourMultiplier norm_orderFourMultiplier).comp continuous_fst
  · have htotal : Continuous (fun p : ComplexDiscPuncturedBall r × ComplexTwoSpace =>
        orderFourAffineFamilyCoverGenerator A.periods
          (orderFourPuncturedAffineCoverToFamilyCover p)) :=
      (orderFourAffineFamilyCoverGenerator_continuous A.periods).comp
        orderFourPuncturedAffineCoverToFamilyCover_continuous
    convert continuous_snd.comp htotal using 1
    funext p
    exact congrArg Prod.snd
      (orderFourAffinePuncturedCoverGenerator_intertwines A p)

/-- Translation by the accumulated order-four period on the explicit punctured affine cover. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverPeriodTranslate {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace :=
  (p.1, periodVector
    (parameterMap A.periods (orderFourCayleyHomeomorph.symm p.1.1)).1
      (-LatticeData.epsilon') + p.2)

/-- Four iterations of the explicit punctured-cover generator return to the original Cayley base
and translate the fibre by the exact integral period `-epsilon'`. -/
public theorem orderFourAffinePuncturedCoverGenerator_iterate_four {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    (orderFourAffinePuncturedCoverGenerator A)^[4] p =
      orderFourAffinePuncturedCoverPeriodTranslate A p := by
  apply orderFourPuncturedAffineCoverToFamilyCover_injective
  have hsem : Function.Semiconj
      (orderFourPuncturedAffineCoverToFamilyCover (r := r))
      (orderFourAffinePuncturedCoverGenerator A (r := r))
      (orderFourAffineFamilyCoverGenerator A.periods) :=
    orderFourAffinePuncturedCoverGenerator_intertwines A (r := r)
  rw [hsem.iterate_right 4 p]
  change (orderFourAffineFamilyCoverGenerator A.periods ^ 4)
      (orderFourPuncturedAffineCoverToFamilyCover p) = _
  rw [orderFourAffineFamilyCoverGenerator_pow_apply]
  rfl

/-- The concatenation of the three successive lifted order-three affine paths. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverLiftPathThree {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path p ((orderThreeAffinePuncturedCoverGenerator A)^[3] p) :=
  iteratedForwardPath (orderThreeAffinePuncturedCoverGenerator A)
    (orderThreeAffinePuncturedCoverLiftPath A) 3 p

/-- Include the threefold iterated order-three path into the full filling cover and use its exact
`epsilon` endpoint. -/
@[expose] public noncomputable def orderThreeAffinePuncturedCoverLiftPathThreeToFull {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path (complexDiscPuncturedCoverToBallCover p)
      (complexDiscPuncturedCoverToBallCover
        (orderThreeAffinePuncturedCoverPeriodTranslate A p)) :=
  ((orderThreeAffinePuncturedCoverLiftPathThree A p).map
    complexDiscPuncturedCoverToBallCover.continuous).cast rfl
      (congrArg complexDiscPuncturedCoverToBallCover
        (orderThreeAffinePuncturedCoverGenerator_iterate_three A p)).symm

/-- The pure straight-fibre path to the same `epsilon` period translate in the full filling
cover. -/
@[expose] public noncomputable def orderThreeFullCoverPeriodPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path (complexDiscPuncturedCoverToBallCover p)
      (complexDiscPuncturedCoverToBallCover
        (orderThreeAffinePuncturedCoverPeriodTranslate A p)) :=
  (Path.refl (complexDiscPuncturedBallToBall p.1)).prod
    (Path.segment p.2
      (periodVector
        (parameterMap A.periods (orderThreeCayleyHomeomorph.symm p.1.1)).1
          LatticeData.epsilon + p.2))

/-- Passing through the filled disc center removes the angular winding: in the full order-three
filling cover, the threefold affine path is homotopic relative endpoints to the straight
`epsilon` period path. -/
public theorem orderThreeAffinePuncturedCoverLiftPathThree_homotopic_periodPath
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path.Homotopic
      (orderThreeAffinePuncturedCoverLiftPathThreeToFull A p)
      (orderThreeFullCoverPeriodPath A p) := by
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- The concatenation of the four successive lifted order-four affine paths. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverLiftPathFour {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path p ((orderFourAffinePuncturedCoverGenerator A)^[4] p) :=
  iteratedForwardPath (orderFourAffinePuncturedCoverGenerator A)
    (orderFourAffinePuncturedCoverLiftPath A) 4 p

/-- Include the fourfold iterated order-four path into the full filling cover and use its exact
`-epsilon'` endpoint. -/
@[expose] public noncomputable def orderFourAffinePuncturedCoverLiftPathFourToFull {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path (complexDiscPuncturedCoverToBallCover p)
      (complexDiscPuncturedCoverToBallCover
        (orderFourAffinePuncturedCoverPeriodTranslate A p)) :=
  ((orderFourAffinePuncturedCoverLiftPathFour A p).map
    complexDiscPuncturedCoverToBallCover.continuous).cast rfl
      (congrArg complexDiscPuncturedCoverToBallCover
        (orderFourAffinePuncturedCoverGenerator_iterate_four A p)).symm

/-- The pure straight-fibre path to the same `-epsilon'` period translate in the full filling
cover. -/
@[expose] public noncomputable def orderFourFullCoverPeriodPath {r : ℝ}
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path (complexDiscPuncturedCoverToBallCover p)
      (complexDiscPuncturedCoverToBallCover
        (orderFourAffinePuncturedCoverPeriodTranslate A p)) :=
  (Path.refl (complexDiscPuncturedBallToBall p.1)).prod
    (Path.segment p.2
      (periodVector
        (parameterMap A.periods (orderFourCayleyHomeomorph.symm p.1.1)).1
          (-LatticeData.epsilon') + p.2))

/-- In the full order-four filling cover, the fourfold affine path is homotopic relative
endpoints to the straight `-epsilon'` period path. -/
public theorem orderFourAffinePuncturedCoverLiftPathFour_homotopic_periodPath
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path.Homotopic
      (orderFourAffinePuncturedCoverLiftPathFourToFull A p)
      (orderFourFullCoverPeriodPath A p) := by
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- The order-three relative homotopy persists after projecting the full affine cover to the
prequotient filling source. -/
public theorem
    orderThreeAffinePuncturedCoverLiftPathThree_fillingCover_homotopic_periodPath
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path.Homotopic
      ((orderThreeAffinePuncturedCoverLiftPathThreeToFull A p).map
        (A.orderThreeFillingCoverMap_continuous r))
      ((orderThreeFullCoverPeriodPath A p).map
        (A.orderThreeFillingCoverMap_continuous r)) := by
  let f : C(ComplexDiscBall r × ComplexTwoSpace, A.orderThreeFillingOpen r) :=
    ⟨A.orderThreeFillingCoverMap r, A.orderThreeFillingCoverMap_continuous r⟩
  exact (orderThreeAffinePuncturedCoverLiftPathThree_homotopic_periodPath
    A hr hr1 p).map f

/-- The order-four relative homotopy likewise persists in its prequotient filling source. -/
public theorem
    orderFourAffinePuncturedCoverLiftPathFour_fillingCover_homotopic_periodPath
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (p : ComplexDiscPuncturedBall r × ComplexTwoSpace) :
    Path.Homotopic
      ((orderFourAffinePuncturedCoverLiftPathFourToFull A p).map
        (A.orderFourFillingCoverMap_continuous r))
      ((orderFourFullCoverPeriodPath A p).map
        (A.orderFourFillingCoverMap_continuous r)) := by
  let f : C(ComplexDiscBall r × ComplexTwoSpace, A.orderFourFillingOpen r) :=
    ⟨A.orderFourFillingCoverMap r, A.orderFourFillingCoverMap_continuous r⟩
  exact (orderFourAffinePuncturedCoverLiftPathFour_homotopic_periodPath
    A hr hr1 p).map f

/-- The prequotient source of the order-three filling is path connected. -/
public theorem orderThreeFillingOpen_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (A.orderThreeFillingOpen r) := by
  let _ : PathConnectedSpace (ComplexDiscBall r) := complexDiscBall_pathConnected hr hr1
  exact (A.orderThreeFillingCoverMap_surjective r).pathConnectedSpace
    (A.orderThreeFillingCoverMap_continuous r)

/-- The prequotient source of the order-four filling is path connected. -/
public theorem orderFourFillingOpen_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (A.orderFourFillingOpen r) := by
  let _ : PathConnectedSpace (ComplexDiscBall r) := complexDiscBall_pathConnected hr hr1
  exact (A.orderFourFillingCoverMap_surjective r).pathConnectedSpace
    (A.orderFourFillingCoverMap_continuous r)

/-- The prequotient order-three affine collar is path connected. -/
public theorem orderThreeAffinePuncturedCarrier_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace ((orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) := by
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  exact (A.orderThreePuncturedCoverMap_surjective r).pathConnectedSpace
    (A.orderThreePuncturedCoverMap_continuous r)

/-- The prequotient order-four affine collar is path connected. -/
public theorem orderFourAffinePuncturedCarrier_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace ((orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) := by
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  exact (A.orderFourPuncturedCoverMap_surjective r).pathConnectedSpace
    (A.orderFourPuncturedCoverMap_continuous r)

/-- The order-three affine filling quotient is path connected. -/
public theorem orderThreeFilling_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (A.OrderThreeVaryingFilling r) := by
  let _ : PathConnectedSpace (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingOpen_pathConnected hr hr1
  let _ := A.orderThreeFillingAction r
  infer_instance

/-- The order-four affine filling quotient is path connected. -/
public theorem orderFourFilling_pathConnected
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    PathConnectedSpace (A.OrderFourVaryingFilling r) := by
  let _ : PathConnectedSpace (A.orderFourFillingOpen r) :=
    A.orderFourFillingOpen_pathConnected hr hr1
  let _ := A.orderFourFillingAction r
  infer_instance

public theorem orderThreeFilling_connected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ConnectedSpace (A.OrderThreeVaryingFilling r) := by
  let _ : ConnectedSpace (ComplexDiscBall r) := complexDiscBall_connected hr hr1
  let _ : ConnectedSpace (A.orderThreeFillingOpen r) :=
    (A.orderThreeFillingCoverMap_surjective r).connectedSpace
      (orderThreeFillingCoverMap_continuous (A := A) r)
  let _ := A.orderThreeFillingAction r
  infer_instance

public theorem orderFourFilling_connected {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ConnectedSpace (A.OrderFourVaryingFilling r) := by
  let _ : ConnectedSpace (ComplexDiscBall r) := complexDiscBall_connected hr hr1
  let _ : ConnectedSpace (A.orderFourFillingOpen r) :=
    (A.orderFourFillingCoverMap_surjective r).connectedSpace
      (orderFourFillingCoverMap_continuous (A := A) r)
  let _ := A.orderFourFillingAction r
  infer_instance

public abbrev SelectedOrderThreePuncturedCollar :=
  Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.orderThreeFillingPiece.radius))

public abbrev SelectedOrderFourPuncturedCollar :=
  Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction
      A.orderFourFillingPiece.radius))

@[instance_reducible]
public noncomputable def selectedOrderThreeFillingComplexCharts :
    ChartedSpace ComplexModel A.SelectedOrderThreeFilling :=
  A.orderThreeFillingComplexCharts A.orderThreeFillingPiece.radius

@[instance_reducible]
public noncomputable def selectedOrderFourFillingComplexCharts :
    ChartedSpace ComplexModel A.SelectedOrderFourFilling :=
  A.orderFourFillingComplexCharts A.orderFourFillingPiece.radius

public noncomputable instance selectedOrderThreeFillingManifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      A.SelectedOrderThreeFilling inferInstance
      A.selectedOrderThreeFillingComplexCharts :=
  A.orderThreeFilling_isManifold A.orderThreeFillingPiece.radius

public noncomputable instance selectedOrderFourFillingManifold :
    @IsManifold ℂ inferInstance ComplexModel inferInstance inferInstance ComplexModel
      inferInstance (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      A.SelectedOrderFourFilling inferInstance
      A.selectedOrderFourFillingComplexCharts :=
  A.orderFourFilling_isManifold A.orderFourFillingPiece.radius

public noncomputable instance selectedOrderThreeFillingConnected :
    ConnectedSpace A.SelectedOrderThreeFilling :=
  A.orderThreeFilling_connected A.orderThreeFillingPiece.radius_pos
    A.orderThreeFillingPiece.radius_lt_one

public noncomputable instance selectedOrderFourFillingConnected :
    ConnectedSpace A.SelectedOrderFourFilling :=
  A.orderFourFilling_connected A.orderFourFillingPiece.radius_pos
    A.orderFourFillingPiece.radius_lt_one

public noncomputable instance selectedOrderThreeFillingSecondCountable :
    SecondCountableTopology A.SelectedOrderThreeFilling :=
  A.orderThreeFilling_secondCountable A.orderThreeFillingPiece.radius

public noncomputable instance selectedOrderFourFillingSecondCountable :
    SecondCountableTopology A.SelectedOrderFourFilling :=
  A.orderFourFilling_secondCountable A.orderFourFillingPiece.radius

@[expose] public noncomputable def selectedOrderThreePuncturedCollarToFilling :
    A.SelectedOrderThreePuncturedCollar → A.SelectedOrderThreeFilling :=
  A.orderThreePuncturedCollarToFilling A.orderThreeFillingPiece.radius

@[expose] public noncomputable def selectedOrderFourPuncturedCollarToFilling :
    A.SelectedOrderFourPuncturedCollar → A.SelectedOrderFourFilling :=
  A.orderFourPuncturedCollarToFilling A.orderFourFillingPiece.radius

public theorem selectedOrderThreePuncturedCollarToFilling_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderThreePuncturedCollarToFilling :=
  A.orderThreePuncturedCollarToFilling_isOpenEmbedding
    A.orderThreeFillingPiece.radius

public theorem selectedOrderFourPuncturedCollarToFilling_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderFourPuncturedCollarToFilling :=
  A.orderFourPuncturedCollarToFilling_isOpenEmbedding
    A.orderFourFillingPiece.radius

@[expose] public noncomputable def selectedOrderThreePuncturedCollarToCentralFamily :
    A.SelectedOrderThreePuncturedCollar → A.CentralFamily :=
  A.orderThreePuncturedCollarToCentralFamily A.orderThreeFillingPiece.sourceData

@[expose] public noncomputable def selectedOrderFourPuncturedCollarToCentralFamily :
    A.SelectedOrderFourPuncturedCollar → A.CentralFamily :=
  A.orderFourPuncturedCollarToCentralFamily A.orderFourFillingPiece.sourceData

public theorem selectedOrderThreePuncturedCollarToCentralFamily_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderThreePuncturedCollarToCentralFamily :=
  A.orderThreePuncturedCollarToCentralFamily_isOpenEmbedding
    A.orderThreeFillingPiece.sourceData

public theorem selectedOrderFourPuncturedCollarToCentralFamily_isOpenEmbedding :
    IsOpenEmbedding A.selectedOrderFourPuncturedCollarToCentralFamily :=
  A.orderFourPuncturedCollarToCentralFamily_isOpenEmbedding
    A.orderFourFillingPiece.sourceData

end PaperAnalyticData

end

end SphereSixComplex.Geometry
