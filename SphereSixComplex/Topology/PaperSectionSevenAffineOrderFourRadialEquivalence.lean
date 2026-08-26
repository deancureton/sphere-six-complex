module

public import SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
public import SphereSixComplex.Topology.PaperSectionSevenAffineRegularBaseRadialEquivalence

/-!
# The order-four lifted affine radial equivalence

The order-four affine radial deformation already exists on the regular base cover.  This file
transports it to the regular torus family by moving fibre vectors with constant real period
coordinates, and concludes that the order-four affine disc lift includes into the order-four
affine half-plane lift by a full-deck equivariant homotopy equivalence.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex
open SphereSixComplex.Periods
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EquivariantQuotientHomeomorph

variable (A : PaperAnalyticData)

/-- The fibre vector with the same real period coordinates, read off at a new base point. -/
public noncomputable def regularFlatVector
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) : ComplexTwoSpace :=
  (fullRankDomain (regularParameterMap A.periods b)).realEquiv
    (periodCoordinates (regularParameterMap A.periods p.1) p.2)

/-- Flat transport is compatible with the fibrewise period translations. -/
public theorem regularFlatVector_smul
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (a : FamilyPeriodGroup (regularParameterMap A.periods))
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    A.regularFlatVector b (a • p) =
      periodVector (regularParameterMap A.periods b).1 a.coeff +
        A.regularFlatVector b p := by
  have hcoord : periodCoordinates (regularParameterMap A.periods (a • p).1) (a • p).2 =
      integerToReal a.coeff +
        periodCoordinates (regularParameterMap A.periods p.1) p.2 := by
    rw [family_smul_fst, family_smul_snd]
    change (fullRankDomain (regularParameterMap A.periods p.1)).realEquiv.symm
        (periodVector (regularParameterMap A.periods p.1).1 a.coeff + p.2) = _
    rw [map_add]
    congr 1
    apply (fullRankDomain (regularParameterMap A.periods p.1)).realEquiv.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact ((fullRankDomain (regularParameterMap A.periods p.1)).map_integer a.coeff).symm
  change (fullRankDomain (regularParameterMap A.periods b)).realEquiv
    (periodCoordinates (regularParameterMap A.periods (a • p).1) (a • p).2) = _
  rw [hcoord, map_add,
    (fullRankDomain (regularParameterMap A.periods b)).map_integer]
  rfl

/-- The fibrewise flat transport of the regular torus family: the point of the fibre over a new
base point with unchanged real period coordinates. -/
public noncomputable def regularFlatTransport
    (bx : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      RegularTotalSpace A.periods) : RegularTotalSpace A.periods :=
  Quotient.lift
    (fun p ↦ (Quotient.mk _ (bx.1, A.regularFlatVector bx.1 p) : RegularTotalSpace A.periods))
    (by
      intro p q hpq
      obtain ⟨g, hg⟩ := hpq
      apply Quotient.sound
      refine ⟨g, ?_⟩
      apply Prod.ext
      · rfl
      · change periodVector (regularParameterMap A.periods bx.1).1 g.coeff +
          A.regularFlatVector bx.1 q = A.regularFlatVector bx.1 p
        rw [← A.regularFlatVector_smul bx.1 g q]
        exact congrArg (A.regularFlatVector bx.1) hg)
    bx.2

@[simp]
public theorem regularFlatTransport_mk
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    A.regularFlatTransport (b, Quotient.mk _ p) =
      Quotient.mk _ (b, A.regularFlatVector b p) :=
  rfl

/-- Flat transport lands over the prescribed base point. -/
public theorem regularTotalSpaceBase_regularFlatTransport
    (bx : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      RegularTotalSpace A.periods) :
    regularTotalSpaceBase A.periods (A.regularFlatTransport bx) = bx.1 := by
  obtain ⟨b, x⟩ := bx
  induction x using Quotient.inductionOn with
  | _ p => rfl

/-- Flat transport to the base point of a family point is the identity. -/
public theorem regularFlatTransport_self (x : RegularTotalSpace A.periods) :
    A.regularFlatTransport (regularTotalSpaceBase A.periods x, x) = x := by
  induction x using Quotient.inductionOn with
  | _ p =>
    change (Quotient.mk _ (p.1, A.regularFlatVector p.1 p) :
      RegularTotalSpace A.periods) = Quotient.mk _ p
    congr 1
    apply Prod.ext
    · rfl
    · change (fullRankDomain (regularParameterMap A.periods p.1)).realEquiv
        ((fullRankDomain (regularParameterMap A.periods p.1)).realEquiv.symm p.2) = p.2
      exact ContinuousLinearEquiv.apply_symm_apply _ _

public theorem regularParameterMap_regularSourceEquiv (g : Delta)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) :
    regularParameterMap A.periods (regularSourceEquiv g b) =
      rhoParameters g (regularParameterMap A.periods b) :=
  parameterMap_equivariant A.periods g b.1

/-- Flat transport intertwines the lifted deck maps on the vector-bundle cover. -/
public theorem regularFlatVector_regularDeckMap (g : Delta)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    A.regularFlatVector (regularSourceEquiv g b) (regularDeckMap A.periods g p) =
      periodTransport g (regularParameterMap A.periods b) (A.regularFlatVector b p) := by
  change (fullRankDomain (regularParameterMap A.periods (regularSourceEquiv g b))).realEquiv
      (periodCoordinates (regularParameterMap A.periods (regularSourceEquiv g p.1))
        (periodTransport g (regularParameterMap A.periods p.1) p.2)) =
    (fullRankDomain (rhoParameters g (regularParameterMap A.periods b))).realEquiv
      (rhoLambdaReal g
        ((fullRankDomain (regularParameterMap A.periods b)).realEquiv.symm
          ((fullRankDomain (regularParameterMap A.periods b)).realEquiv
            (periodCoordinates (regularParameterMap A.periods p.1) p.2))))
  rw [ContinuousLinearEquiv.symm_apply_apply,
    A.regularParameterMap_regularSourceEquiv g b,
    A.regularParameterMap_regularSourceEquiv g p.1, periodCoordinates_transport]

/-- Flat transport is equivariant for the full triangle-group deck action. -/
public theorem regularFlatTransport_deck (g : Delta)
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (x : RegularTotalSpace A.periods) :
    A.regularFlatTransport (actionMap A.regularBaseDeckAction g b,
        actionMap (regularFamilyDeckAction A.periods) g x) =
      actionMap (regularFamilyDeckAction A.periods) g (A.regularFlatTransport (b, x)) := by
  induction x using Quotient.inductionOn with
  | _ p =>
    change (Quotient.mk _ (regularSourceEquiv g b,
        A.regularFlatVector (regularSourceEquiv g b) (regularDeckMap A.periods g p)) :
      RegularTotalSpace A.periods) =
      Quotient.mk _ (regularDeckMap A.periods g (b, A.regularFlatVector b p))
    rw [A.regularFlatVector_regularDeckMap g b p]
    rfl

public theorem regularFlatVector_eq
    (b : RegularBase (U := A.modular.modularParameter.toTriangleUniformization))
    (p : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :
    A.regularFlatVector b p =
      periodRealLinear (regularParameterMap A.periods b).1
        (periodCoordinates (regularParameterMap A.periods p.1) p.2) :=
  FullRank.ofSetupInequalities_realEquiv_apply _ _ _

public theorem regularFlatVector_continuous :
    Continuous (fun bp : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) ↦ A.regularFlatVector bp.1 bp.2) := by
  have hcoord : Continuous
      (fun bp : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace) ↦
        periodCoordinates (parameterMap A.periods bp.2.1.1) bp.2.2) :=
    (EllipticRealPeriodProductTrivialization.periodCoordinates_parameterMap_continuous
      A.periods).comp
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        (continuous_snd.comp continuous_snd))
  have h := (periodRealLinear_parameterMap_continuous A.periods).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk hcoord)
  exact h.congr fun bp ↦ (A.regularFlatVector_eq bp.1 bp.2).symm

public theorem regularFlatTransport_continuous : Continuous A.regularFlatTransport := by
  have hperiod : ∀ a : IntegerPeriods,
      Continuous (fun b : RegularBase
        (U := A.modular.modularParameter.toTriangleUniformization) ↦
          periodVector (regularParameterMap A.periods b).1 a) := fun a ↦
    (periodSection_contMDiff A.periods a 0).continuous.comp continuous_subtype_val
  let _ : ContinuousConstSMul (FamilyPeriodGroup (regularParameterMap A.periods))
      (RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
        ComplexTwoSpace) :=
    familyContinuousConstSMul (regularParameterMap A.periods) hperiod
  let mk : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace → RegularTotalSpace A.periods := Quotient.mk _
  have hq : IsOpenQuotientMap (Prod.map
      (id : RegularBase (U := A.modular.modularParameter.toTriangleUniformization) →
        RegularBase (U := A.modular.modularParameter.toTriangleUniformization)) mk) :=
    IsOpenQuotientMap.id.prodMap
      (MulAction.isOpenQuotientMap_quotientMk
        (Γ := FamilyPeriodGroup (regularParameterMap A.periods))
        (T := RegularBase (U := A.modular.modularParameter.toTriangleUniformization) ×
          ComplexTwoSpace))
  apply hq.isQuotientMap.continuous_iff.mpr
  exact continuous_quot_mk.comp
    (continuous_fst.prodMk A.regularFlatVector_continuous)

section FamilyTransport

variable {A}
variable {small big : Set RegularCoordinateBase}
variable {Cs Cb : InvariantOpenCarrier (regularFamilyDeckAction A.periods)}

/-- The base point of a family point of an invariant carrier, as a point of the corresponding
regular-base region preimage. -/
public def carrierBasePoint (hC : ∀ q, q ∈ Cs.carrier ↔
    A.regularCoordinate (regularTotalSpaceBase A.periods q) ∈ small) :
    C(Cs.carrier, coveringRegionPreimage A.regularCoordinate small) where
  toFun q := ⟨regularTotalSpaceBase A.periods q.1, (hC q.1).mp q.2⟩
  continuous_toFun :=
    ((regularTotalSpaceBase_continuous A.periods).comp continuous_subtype_val).subtype_mk _

public theorem carrierBasePoint_equivariant
    (hC : ∀ q, q ∈ Cs.carrier ↔
      A.regularCoordinate (regularTotalSpaceBase A.periods q) ∈ small)
    (g : Delta) (q : Cs.carrier) :
    carrierBasePoint hC (restrictedActionMap Cs g q) =
      actionMap (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant small) g (carrierBasePoint hC q) :=
  Subtype.ext (regularTotalSpaceBase_familyDeckMap A.periods g q.1)

/-- Flat transport to a base point of a coordinate region stays inside the matching carrier. -/
public theorem regularFlatTransport_mem_carrier
    (hC : ∀ q, q ∈ Cs.carrier ↔
      A.regularCoordinate (regularTotalSpaceBase A.periods q) ∈ small)
    (b : coveringRegionPreimage A.regularCoordinate small)
    (x : RegularTotalSpace A.periods) :
    A.regularFlatTransport (b.1, x) ∈ Cs.carrier := by
  refine (hC _).mpr ?_
  rw [A.regularTotalSpaceBase_regularFlatTransport (b.1, x)]
  exact b.2


/-- Transport a full-deck equivariant homotopy equivalence between preimages of two affine
coordinate regions in the regular base to the corresponding invariant carriers of the regular
torus family.  Fibres are moved by the flat transport, so the forward map stays the literal
inclusion. -/
public noncomputable def familyEquivOfBaseEquiv
    (hsub : Cs.carrier ⊆ Cb.carrier)
    (hCs : ∀ q, q ∈ Cs.carrier ↔
      A.regularCoordinate (regularTotalSpaceBase A.periods q) ∈ small)
    (hCb : ∀ q, q ∈ Cb.carrier ↔
      A.regularCoordinate (regularTotalSpaceBase A.periods q) ∈ big)
    (E : EquivariantHomotopyEquivData
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant small)
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant big))
    (hE : ∀ e, (E.toFun e).1 = e.1) :
    EquivariantHomotopyEquivData
      (restrictedMulAction (regularFamilyDeckAction A.periods) Cs)
      (restrictedMulAction (regularFamilyDeckAction A.periods) Cb) where
  toFun :=
    { toFun := fun q ↦ ⟨q.1, hsub q.2⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }
  invFun :=
    { toFun := fun y ↦ ⟨A.regularFlatTransport ((E.invFun (carrierBasePoint hCb y)).1, y.1),
        regularFlatTransport_mem_carrier hCs (E.invFun (carrierBasePoint hCb y)) y.1⟩
      continuous_toFun :=
        (A.regularFlatTransport_continuous.comp
          ((continuous_subtype_val.comp
            (E.invFun.continuous.comp (carrierBasePoint hCb).continuous)).prodMk
              continuous_subtype_val)).subtype_mk _ }
  toFun_equivariant := fun _ _ ↦ rfl
  invFun_equivariant := fun g y ↦ by
    apply Subtype.ext
    change A.regularFlatTransport
        ((E.invFun (carrierBasePoint hCb (restrictedActionMap Cb g y))).1,
          actionMap (regularFamilyDeckAction A.periods) g y.1) =
      actionMap (regularFamilyDeckAction A.periods) g
        (A.regularFlatTransport ((E.invFun (carrierBasePoint hCb y)).1, y.1))
    rw [carrierBasePoint_equivariant hCb g y, E.invFun_equivariant]
    exact A.regularFlatTransport_deck g (E.invFun (carrierBasePoint hCb y)).1 y.1
  leftInvHomotopy :=
    { toFun := fun tq ↦
        ⟨A.regularFlatTransport
            ((E.leftInvHomotopy (tq.1, carrierBasePoint hCs tq.2)).1, tq.2.1),
          regularFlatTransport_mem_carrier hCs _ _⟩
      continuous_toFun :=
        (A.regularFlatTransport_continuous.comp
          ((continuous_subtype_val.comp
            (E.leftInvHomotopy.continuous.comp
              (continuous_fst.prodMk
                ((carrierBasePoint hCs).continuous.comp continuous_snd)))).prodMk
            (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun q ↦ by
        apply Subtype.ext
        have hb : E.toFun (carrierBasePoint hCs q) =
            carrierBasePoint hCb (⟨q.1, hsub q.2⟩ : Cb.carrier) :=
          Subtype.ext (hE (carrierBasePoint hCs q))
        change A.regularFlatTransport
            ((E.leftInvHomotopy (0, carrierBasePoint hCs q)).1, q.1) =
          A.regularFlatTransport
            ((E.invFun (carrierBasePoint hCb (⟨q.1, hsub q.2⟩ : Cb.carrier))).1, q.1)
        rw [E.leftInvHomotopy.apply_zero]
        change A.regularFlatTransport
            ((E.invFun (E.toFun (carrierBasePoint hCs q))).1, q.1) = _
        rw [hb]
      map_one_left := fun q ↦ by
        apply Subtype.ext
        change A.regularFlatTransport
            ((E.leftInvHomotopy (1, carrierBasePoint hCs q)).1, q.1) = q.1
        rw [E.leftInvHomotopy.apply_one]
        exact A.regularFlatTransport_self q.1 }
  rightInvHomotopy :=
    { toFun := fun ty ↦
        ⟨A.regularFlatTransport
            ((E.rightInvHomotopy (ty.1, carrierBasePoint hCb ty.2)).1, ty.2.1),
          regularFlatTransport_mem_carrier hCb _ _⟩
      continuous_toFun :=
        (A.regularFlatTransport_continuous.comp
          ((continuous_subtype_val.comp
            (E.rightInvHomotopy.continuous.comp
              (continuous_fst.prodMk
                ((carrierBasePoint hCb).continuous.comp continuous_snd)))).prodMk
            (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      map_zero_left := fun y ↦ by
        apply Subtype.ext
        change A.regularFlatTransport
            ((E.rightInvHomotopy (0, carrierBasePoint hCb y)).1, y.1) =
          A.regularFlatTransport ((E.invFun (carrierBasePoint hCb y)).1, y.1)
        rw [E.rightInvHomotopy.apply_zero]
        change A.regularFlatTransport
            ((E.toFun (E.invFun (carrierBasePoint hCb y))).1, y.1) = _
        rw [hE (E.invFun (carrierBasePoint hCb y))]
      map_one_left := fun y ↦ by
        apply Subtype.ext
        change A.regularFlatTransport
            ((E.rightInvHomotopy (1, carrierBasePoint hCb y)).1, y.1) = y.1
        rw [E.rightInvHomotopy.apply_one]
        exact A.regularFlatTransport_self y.1 }
  leftInvHomotopy_equivariant := fun g t q ↦ by
    apply Subtype.ext
    change A.regularFlatTransport
        ((E.leftInvHomotopy (t, carrierBasePoint hCs (restrictedActionMap Cs g q))).1,
          actionMap (regularFamilyDeckAction A.periods) g q.1) =
      actionMap (regularFamilyDeckAction A.periods) g
        (A.regularFlatTransport ((E.leftInvHomotopy (t, carrierBasePoint hCs q)).1, q.1))
    rw [carrierBasePoint_equivariant hCs g q, E.leftInvHomotopy_equivariant]
    exact A.regularFlatTransport_deck g (E.leftInvHomotopy (t, carrierBasePoint hCs q)).1 q.1
  rightInvHomotopy_equivariant := fun g t y ↦ by
    apply Subtype.ext
    change A.regularFlatTransport
        ((E.rightInvHomotopy (t, carrierBasePoint hCb (restrictedActionMap Cb g y))).1,
          actionMap (regularFamilyDeckAction A.periods) g y.1) =
      actionMap (regularFamilyDeckAction A.periods) g
        (A.regularFlatTransport ((E.rightInvHomotopy (t, carrierBasePoint hCb y)).1, y.1))
    rw [carrierBasePoint_equivariant hCb g y, E.rightInvHomotopy_equivariant]
    exact A.regularFlatTransport_deck g (E.rightInvHomotopy (t, carrierBasePoint hCb y)).1 y.1

@[simp]
public theorem familyEquivOfBaseEquiv_toFun
    (hsub : Cs.carrier ⊆ Cb.carrier)
    (hCs : ∀ q, q ∈ Cs.carrier ↔
      A.regularCoordinate (regularTotalSpaceBase A.periods q) ∈ small)
    (hCb : ∀ q, q ∈ Cb.carrier ↔
      A.regularCoordinate (regularTotalSpaceBase A.periods q) ∈ big)
    (E : EquivariantHomotopyEquivData
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant small)
      (coveringRegionPreimageAction A.regularBaseDeckAction A.regularCoordinate
        A.regularCoordinate_deck_invariant big))
    (hE : ∀ e, (E.toFun e).1 = e.1) (q : Cs.carrier) :
    (familyEquivOfBaseEquiv hsub hCs hCb E hE).toFun q = ⟨q.1, hsub q.2⟩ :=
  rfl

end FamilyTransport

/-- The order-four affine disc lift includes into the order-four affine half-plane lift by a
full-deck equivariant homotopy equivalence on the genuine regular cover. -/
public theorem exists_orderFourAffineRadialEquiv
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 - 1 / 3) :
    ∃ E : EquivariantHomotopyEquivData
        (A.orderFourAffineDiscLiftAction r) A.orderFourAffineHalfPlaneLiftAction,
      (E.toFun : (A.orderFourAffineDiscLiftCarrier r).carrier →
        A.orderFourAffineHalfPlaneLiftCarrier.carrier) =
          A.orderFourAffineDiscLiftInclusion hr :=
  ⟨familyEquivOfBaseEquiv (A.orderFourAffineDiscLiftCarrier_subset_halfPlane hr)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl)
    (A.orderFourBaseRadialEquiv (half_pos hr0) (half_lt_self hr0) hr) (fun _ ↦ rfl), rfl⟩

end SphereSixComplex.Geometry.PaperAnalyticData

end
