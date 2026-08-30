module

public import SphereSixComplex.Topology.PaperActualEllipticFillingDeckTransport
public import SphereSixComplex.Topology.PaperAffineCyclicRadialQuotientCovering

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology

variable (A : PaperAnalyticData)

/-- Reassociation of a disc-ball product as a radial product ball. -/
public def complexDiscBallProductRadialHomeomorph
    {r : ℝ} {T : Type} [TopologicalSpace T] :
    ComplexDiscBall r × T ≃ₜ RadialProductBall r T where
  toFun p := ⟨(p.1.1, p.2), p.1.2⟩
  invFun p := (⟨p.1.1, p.2⟩, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd) _
  continuous_invFun :=
    (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
      (continuous_snd.comp continuous_subtype_val)

/-- Reindexing a regular quotient-cover action along a group equivalence preserves the regular
quotient-cover structure. -/
public theorem isQuotientCoveringMap_compMulEquiv
    {G H E B : Type*} [Group G] [Group H]
    [TopologicalSpace E] [TopologicalSpace B]
    (actionH : MulAction H E) (e : G ≃* H) (f : E → B)
    (hf : @IsQuotientCoveringMap E B _ _ f H _ actionH) :
    let actionG := @MulAction.compHom H G E _ actionH _ e.toMonoidHom
    @IsQuotientCoveringMap E B _ _ f G _ actionG := by
  let _ := actionH
  let actionG := MulAction.compHom E e.toMonoidHom
  let _ := actionG
  refine
    { toIsQuotientMap := hf.toIsQuotientMap
      continuous_const_smul := fun g ↦ hf.continuous_const_smul (e g)
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · intro x y
    constructor
    · intro hxy
      obtain ⟨h, hh⟩ := hf.apply_eq_iff_mem_orbit.mp hxy
      obtain ⟨g, rfl⟩ := e.surjective h
      exact ⟨g, hh⟩
    · rintro ⟨g, hg⟩
      exact hf.apply_eq_iff_mem_orbit.mpr ⟨e g, hg⟩
  · intro x
    obtain ⟨U, hU, hdisj⟩ := hf.disjoint x
    refine ⟨U, hU, ?_⟩
    intro g hg
    apply e.injective
    simpa using hdisj (e g) hg

@[instance_reducible]
public noncomputable def orderThreeActualCentralFillingDeckAction :
    MulAction A.orderThreeActualEllipticBoundaryDeckData.FillingDeck ComplexTwoSpace := by
  let P := orderThreeCentralFiberPresentationData A.periods
  let actionH := affineCyclicFillingDeckAction P
  let _ := actionH
  exact MulAction.compHom ComplexTwoSpace
    A.orderThreeActualToCanonicalFillingDeckEquiv.toMonoidHom

public theorem orderThreeActualCentralFilling_isQuotientCoveringMap :
    letI := A.orderThreeActualCentralFillingDeckAction
    IsQuotientCoveringMap
      (complexTwoReducedCentralFiberProjection
        (D := orderThreeRadialActionData A.periods))
      A.orderThreeActualEllipticBoundaryDeckData.FillingDeck := by
  let P := orderThreeCentralFiberPresentationData A.periods
  let actionH := affineCyclicFillingDeckAction P
  exact isQuotientCoveringMap_compMulEquiv actionH
    A.orderThreeActualToCanonicalFillingDeckEquiv _
    (orderThreeAffineCyclicFilling_isQuotientCoveringMap A.periods)

@[instance_reducible]
public noncomputable def orderFourActualCentralFillingDeckAction :
    MulAction A.orderFourActualEllipticBoundaryDeckData.FillingDeck ComplexTwoSpace := by
  let P := orderFourCentralFiberPresentationData A.periods
  let actionH := affineCyclicFillingDeckAction P
  let _ := actionH
  exact MulAction.compHom ComplexTwoSpace
    A.orderFourActualToCanonicalFillingDeckEquiv.toMonoidHom

public theorem orderFourActualCentralFilling_isQuotientCoveringMap :
    letI := A.orderFourActualCentralFillingDeckAction
    IsQuotientCoveringMap
      (complexTwoReducedCentralFiberProjection
        (D := orderFourRadialActionData A.periods))
      A.orderFourActualEllipticBoundaryDeckData.FillingDeck := by
  let P := orderFourCentralFiberPresentationData A.periods
  let actionH := affineCyclicFillingDeckAction P
  exact isQuotientCoveringMap_compMulEquiv actionH
    A.orderFourActualToCanonicalFillingDeckEquiv _
    (orderFourAffineCyclicFilling_isQuotientCoveringMap A.periods)

public noncomputable def orderThreeActualFillingDegree :
    A.orderThreeActualEllipticBoundaryDeckData.FillingDeck →* FiniteCyclic 3 :=
  (canonicalAffineCyclicFillingExtension
    (orderThreeCentralFiberPresentationData A.periods)).proj.comp
      A.orderThreeActualToCanonicalFillingDeckEquiv.toMonoidHom

public noncomputable def orderFourActualFillingDegree :
    A.orderFourActualEllipticBoundaryDeckData.FillingDeck →* FiniteCyclic 4 :=
  (canonicalAffineCyclicFillingExtension
    (orderFourCentralFiberPresentationData A.periods)).proj.comp
      A.orderFourActualToCanonicalFillingDeckEquiv.toMonoidHom

public noncomputable def orderThreeActualDiscRepresentation :
    A.orderThreeActualEllipticBoundaryDeckData.FillingDeck →* Equiv.Perm ComplexUnitDisc :=
  (cyclicRepresentation 3 orderThreeDiscRotation orderThreeDiscRotation_pow).comp
    A.orderThreeActualFillingDegree

public noncomputable def orderFourActualDiscRepresentation :
    A.orderFourActualEllipticBoundaryDeckData.FillingDeck →* Equiv.Perm ComplexUnitDisc :=
  (cyclicRepresentation 4 orderFourDiscRotation orderFourDiscRotation_pow).comp
    A.orderFourActualFillingDegree

public theorem orderThreeActualDiscRepresentation_norm
    (g : A.orderThreeActualEllipticBoundaryDeckData.FillingDeck) (u : ComplexUnitDisc) :
    ‖((A.orderThreeActualDiscRepresentation g u : ComplexUnitDisc) : ℂ)‖ = ‖(u : ℂ)‖ := by
  rw [orderThreeActualDiscRepresentation, MonoidHom.comp_apply,
    cyclic_eq_generator_pow (A.orderThreeActualFillingDegree g), map_pow,
    show cyclicGenerator 3 = Multiplicative.ofAdd 1 from rfl,
    cyclicRepresentation_generator]
  change ‖(((orderThreeDiscRotation ^
    (Multiplicative.toAdd (A.orderThreeActualFillingDegree g)).val) u :
      ComplexUnitDisc) : ℂ)‖ = _
  rw [show orderThreeDiscRotation =
      discScalarEquiv orderThreeMultiplier norm_orderThreeMultiplier from rfl,
    discScalarEquiv_pow_apply_val, norm_mul, norm_pow,
    norm_orderThreeMultiplier, one_pow, one_mul]

public theorem orderFourActualDiscRepresentation_norm
    (g : A.orderFourActualEllipticBoundaryDeckData.FillingDeck) (u : ComplexUnitDisc) :
    ‖((A.orderFourActualDiscRepresentation g u : ComplexUnitDisc) : ℂ)‖ = ‖(u : ℂ)‖ := by
  rw [orderFourActualDiscRepresentation, MonoidHom.comp_apply,
    cyclic_eq_generator_pow (A.orderFourActualFillingDegree g), map_pow,
    show cyclicGenerator 4 = Multiplicative.ofAdd 1 from rfl,
    cyclicRepresentation_generator]
  change ‖(((orderFourDiscRotation ^
    (Multiplicative.toAdd (A.orderFourActualFillingDegree g)).val) u :
      ComplexUnitDisc) : ℂ)‖ = _
  rw [show orderFourDiscRotation =
      discScalarEquiv orderFourMultiplier norm_orderFourMultiplier from rfl,
    discScalarEquiv_pow_apply_val, norm_mul, norm_pow,
    norm_orderFourMultiplier, one_pow, one_mul]

@[instance_reducible]
public noncomputable def orderThreeActualDiscBallAction :
    MulAction A.orderThreeActualEllipticBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderThree.radius) where
  smul g u := ⟨A.orderThreeActualDiscRepresentation g u.1, by
    rw [A.orderThreeActualDiscRepresentation_norm]
    exact u.2⟩
  one_smul u := by
    apply Subtype.ext
    change A.orderThreeActualDiscRepresentation 1 u.1 = u.1
    rw [map_one]
    rfl
  mul_smul g h u := by
    apply Subtype.ext
    change A.orderThreeActualDiscRepresentation (g * h) u.1 =
      A.orderThreeActualDiscRepresentation g (A.orderThreeActualDiscRepresentation h u.1)
    rw [map_mul]
    rfl

@[instance_reducible]
public noncomputable def orderFourActualDiscBallAction :
    MulAction A.orderFourActualEllipticBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderFour.radius) where
  smul g u := ⟨A.orderFourActualDiscRepresentation g u.1, by
    rw [A.orderFourActualDiscRepresentation_norm]
    exact u.2⟩
  one_smul u := by
    apply Subtype.ext
    change A.orderFourActualDiscRepresentation 1 u.1 = u.1
    rw [map_one]
    rfl
  mul_smul g h u := by
    apply Subtype.ext
    change A.orderFourActualDiscRepresentation (g * h) u.1 =
      A.orderFourActualDiscRepresentation g (A.orderFourActualDiscRepresentation h u.1)
    rw [map_mul]
    rfl

@[instance_reducible]
public noncomputable def orderThreeActualFixedRadialFillingDeckAction :
    MulAction A.orderThreeActualEllipticBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace) := by
  let _ := A.orderThreeActualDiscBallAction
  let _ := A.orderThreeActualCentralFillingDeckAction
  infer_instance

@[instance_reducible]
public noncomputable def orderFourActualFixedRadialFillingDeckAction :
    MulAction A.orderFourActualEllipticBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace) := by
  let _ := A.orderFourActualDiscBallAction
  let _ := A.orderFourActualCentralFillingDeckAction
  infer_instance

@[instance_reducible]
public noncomputable def orderThreeActualUnitRadialFillingDeckAction :
    MulAction A.orderThreeActualEllipticBoundaryDeckData.FillingDeck
      (ComplexUnitDisc × ComplexTwoSpace) := by
  let P := orderThreeCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  let _ := actionH
  exact MulAction.compHom (ComplexUnitDisc × ComplexTwoSpace)
    A.orderThreeActualToCanonicalFillingDeckEquiv.toMonoidHom

public theorem orderThreeActualUnitRadialFilling_isQuotientCoveringMap :
    letI := A.orderThreeActualUnitRadialFillingDeckAction
    IsQuotientCoveringMap
      (affineCyclicRadialFillingProjection
        (orderThreeCentralFiberPresentationData A.periods))
      A.orderThreeActualEllipticBoundaryDeckData.FillingDeck := by
  let P := orderThreeCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  exact isQuotientCoveringMap_compMulEquiv actionH
    A.orderThreeActualToCanonicalFillingDeckEquiv _
    (affineCyclicRadialFilling_isQuotientCoveringMap P
      (orderThreeCentralFiberPresentationData_lift_continuous A.periods)
      (orderThreeCentralFiberPresentationData_lift_symm_continuous A.periods))

@[instance_reducible]
public noncomputable def orderFourActualUnitRadialFillingDeckAction :
    MulAction A.orderFourActualEllipticBoundaryDeckData.FillingDeck
      (ComplexUnitDisc × ComplexTwoSpace) := by
  let P := orderFourCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  let _ := actionH
  exact MulAction.compHom (ComplexUnitDisc × ComplexTwoSpace)
    A.orderFourActualToCanonicalFillingDeckEquiv.toMonoidHom

public theorem orderFourActualUnitRadialFilling_isQuotientCoveringMap :
    letI := A.orderFourActualUnitRadialFillingDeckAction
    IsQuotientCoveringMap
      (affineCyclicRadialFillingProjection
        (orderFourCentralFiberPresentationData A.periods))
      A.orderFourActualEllipticBoundaryDeckData.FillingDeck := by
  let P := orderFourCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  exact isQuotientCoveringMap_compMulEquiv actionH
    A.orderFourActualToCanonicalFillingDeckEquiv _
    (affineCyclicRadialFilling_isQuotientCoveringMap P
      (orderFourCentralFiberPresentationData_lift_continuous A.periods)
      (orderFourCentralFiberPresentationData_lift_symm_continuous A.periods))

public noncomputable def orderThreeActualCoverToCanonicalRadialHomeomorph :
    ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace ≃ₜ
      ComplexUnitDisc × ComplexTwoSpace :=
  (A.orderThreeFillingCoverRealPeriodHomeomorph
      A.starSeparation.orderThree.radius).trans
    ((complexDiscBallProductRadialHomeomorph
      (r := A.starSeparation.orderThree.radius) (T := ComplexTwoSpace)).trans
      (radialProductBallHomeomorph A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one))

public noncomputable def orderFourActualCoverToCanonicalRadialHomeomorph :
    ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace ≃ₜ
      ComplexUnitDisc × ComplexTwoSpace :=
  (A.orderFourFillingCoverRealPeriodHomeomorph
      A.starSeparation.orderFour.radius).trans
    ((complexDiscBallProductRadialHomeomorph
      (r := A.starSeparation.orderFour.radius) (T := ComplexTwoSpace)).trans
      (radialProductBallHomeomorph A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one))

@[instance_reducible]
public noncomputable def orderThreeActualRadialFillingDeckAction :
    MulAction A.orderThreeActualEllipticBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace) :=
  pullbackMulActionHomeomorph A.orderThreeActualUnitRadialFillingDeckAction
    A.orderThreeActualCoverToCanonicalRadialHomeomorph

public theorem orderThreeActualCanonicalRadialProjection_isQuotientCoveringMap :
    letI := A.orderThreeActualRadialFillingDeckAction
    IsQuotientCoveringMap
      ((affineCyclicRadialFillingProjection
        (orderThreeCentralFiberPresentationData A.periods)) ∘
          A.orderThreeActualCoverToCanonicalRadialHomeomorph)
      A.orderThreeActualEllipticBoundaryDeckData.FillingDeck := by
  exact isQuotientCoveringMap_comp_homeomorph
    A.orderThreeActualUnitRadialFillingDeckAction
    A.orderThreeActualCoverToCanonicalRadialHomeomorph _
    A.orderThreeActualUnitRadialFilling_isQuotientCoveringMap

@[instance_reducible]
public noncomputable def orderFourActualRadialFillingDeckAction :
    MulAction A.orderFourActualEllipticBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace) :=
  pullbackMulActionHomeomorph A.orderFourActualUnitRadialFillingDeckAction
    A.orderFourActualCoverToCanonicalRadialHomeomorph

public theorem orderFourActualCanonicalRadialProjection_isQuotientCoveringMap :
    letI := A.orderFourActualRadialFillingDeckAction
    IsQuotientCoveringMap
      ((affineCyclicRadialFillingProjection
        (orderFourCentralFiberPresentationData A.periods)) ∘
          A.orderFourActualCoverToCanonicalRadialHomeomorph)
      A.orderFourActualEllipticBoundaryDeckData.FillingDeck := by
  exact isQuotientCoveringMap_comp_homeomorph
    A.orderFourActualUnitRadialFillingDeckAction
    A.orderFourActualCoverToCanonicalRadialHomeomorph _
    A.orderFourActualUnitRadialFilling_isQuotientCoveringMap

public noncomputable def orderThreeActualFillingToCanonicalRadialHomeomorph :
    A.actualVanKampenFourPieceCover.ellipticThree ≃ₜ
      (orderThreeRadialActionData A.periods).FillingQuotient :=
  A.orderThreeFillingToActualPieceHomeomorph.symm.trans
    ((orderThreeAffineRadialCompatibility A
      A.starSeparation.orderThree.radius
      A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).toProductIdentification.quotientHomeomorph)

public noncomputable def orderFourActualFillingToCanonicalRadialHomeomorph :
    A.actualVanKampenFourPieceCover.ellipticFour ≃ₜ
      (orderFourRadialActionData A.periods).FillingQuotient :=
  A.orderFourFillingToActualPieceHomeomorph.symm.trans
    ((orderFourAffineRadialCompatibility A
      A.starSeparation.orderFour.radius
      A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).toProductIdentification.quotientHomeomorph)

public theorem orderThreeActualFillingProjection_canonicalRadial
    (q : ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace) :
    A.orderThreeActualFillingToCanonicalRadialHomeomorph
        (A.orderThreeActualEllipticFillingProjection q) =
      affineCyclicRadialFillingProjection
        (orderThreeCentralFiberPresentationData A.periods)
        (A.orderThreeActualCoverToCanonicalRadialHomeomorph q) := by
  change
    (orderThreeAffineRadialCompatibility A
      A.starSeparation.orderThree.radius
      A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).toProductIdentification.quotientHomeomorph
        (A.orderThreeFillingToActualPieceHomeomorph.symm
          (A.orderThreeActualEllipticFillingProjection q)) = _
  have hproj : A.orderThreeActualEllipticFillingProjection q =
      A.orderThreeFillingToActualPieceHomeomorph
        (A.orderThreeActualFillingCoverProjection
          A.starSeparation.orderThree.radius q) := rfl
  rw [hproj]
  rw [A.orderThreeFillingToActualPieceHomeomorph.symm_apply_apply]
  have hcover : A.orderThreeActualFillingCoverProjection
      A.starSeparation.orderThree.radius q =
    (Quotient.mk _ (A.orderThreeFillingCoverMap
      A.starSeparation.orderThree.radius q) :
        (orderThreeAffineRadialCompatibility A
          A.starSeparation.orderThree.radius
          A.starSeparation.orderThree.radius_pos
          A.starSeparation.orderThree.radius_lt_one).toProductIdentification.SourceQuotient) :=
    rfl
  rw [hcover, EquivariantRadialProductIdentification.quotientHomeomorph_mk]
  apply congrArg (Quotient.mk _)
  apply Prod.ext
  · apply Subtype.ext
    change (((orderThreeRadialWholeFillingChart A
      A.starSeparation.orderThree.radius
      A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).toProductHomeomorph
        (A.orderThreeFillingCoverMap A.starSeparation.orderThree.radius q)).1 : ℂ) = _
    rw [orderThreeRadialWholeFillingChart_apply_fst_val,
      A.orderThreeFillingProductMap_coverMap_eq_fixed]
    rfl
  · change ((orderThreeRadialWholeFillingChart A
      A.starSeparation.orderThree.radius
      A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).toProductHomeomorph
        (A.orderThreeFillingCoverMap A.starSeparation.orderThree.radius q)).2 = _
    rw [orderThreeRadialWholeFillingChart_apply_snd,
      A.orderThreeFillingProductMap_coverMap_eq_fixed]
    rfl

public theorem orderFourActualFillingProjection_canonicalRadial
    (q : ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace) :
    A.orderFourActualFillingToCanonicalRadialHomeomorph
        (A.orderFourActualEllipticFillingProjection q) =
      affineCyclicRadialFillingProjection
        (orderFourCentralFiberPresentationData A.periods)
        (A.orderFourActualCoverToCanonicalRadialHomeomorph q) := by
  change
    (orderFourAffineRadialCompatibility A
      A.starSeparation.orderFour.radius
      A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).toProductIdentification.quotientHomeomorph
        (A.orderFourFillingToActualPieceHomeomorph.symm
          (A.orderFourActualEllipticFillingProjection q)) = _
  have hproj : A.orderFourActualEllipticFillingProjection q =
      A.orderFourFillingToActualPieceHomeomorph
        (A.orderFourActualFillingCoverProjection
          A.starSeparation.orderFour.radius q) := rfl
  rw [hproj]
  rw [A.orderFourFillingToActualPieceHomeomorph.symm_apply_apply]
  have hcover : A.orderFourActualFillingCoverProjection
      A.starSeparation.orderFour.radius q =
    (Quotient.mk _ (A.orderFourFillingCoverMap
      A.starSeparation.orderFour.radius q) :
        (orderFourAffineRadialCompatibility A
          A.starSeparation.orderFour.radius
          A.starSeparation.orderFour.radius_pos
          A.starSeparation.orderFour.radius_lt_one).toProductIdentification.SourceQuotient) :=
    rfl
  rw [hcover, EquivariantRadialProductIdentification.quotientHomeomorph_mk]
  apply congrArg (Quotient.mk _)
  apply Prod.ext
  · apply Subtype.ext
    change (((orderFourRadialWholeFillingChart A
      A.starSeparation.orderFour.radius
      A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).toProductHomeomorph
        (A.orderFourFillingCoverMap A.starSeparation.orderFour.radius q)).1 : ℂ) = _
    rw [orderFourRadialWholeFillingChart_apply_fst_val,
      A.orderFourFillingProductMap_coverMap_eq_fixed]
    rfl
  · change ((orderFourRadialWholeFillingChart A
      A.starSeparation.orderFour.radius
      A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).toProductHomeomorph
        (A.orderFourFillingCoverMap A.starSeparation.orderFour.radius q)).2 = _
    rw [orderFourRadialWholeFillingChart_apply_snd,
      A.orderFourFillingProductMap_coverMap_eq_fixed]
    rfl

public theorem orderThreeActualEllipticFillingProjection_isQuotientCoveringMap :
    letI := A.orderThreeActualRadialFillingDeckAction
    IsQuotientCoveringMap A.orderThreeActualEllipticFillingProjection
      A.orderThreeActualEllipticBoundaryDeckData.FillingDeck := by
  let _ := A.orderThreeActualRadialFillingDeckAction
  have h := A.orderThreeActualCanonicalRadialProjection_isQuotientCoveringMap.homeomorph_comp
    A.orderThreeActualFillingToCanonicalRadialHomeomorph.symm
  have heq :
      A.orderThreeActualFillingToCanonicalRadialHomeomorph.symm ∘
          ((affineCyclicRadialFillingProjection
            (orderThreeCentralFiberPresentationData A.periods)) ∘
              A.orderThreeActualCoverToCanonicalRadialHomeomorph) =
        A.orderThreeActualEllipticFillingProjection := by
    funext q
    calc
      A.orderThreeActualFillingToCanonicalRadialHomeomorph.symm
          (affineCyclicRadialFillingProjection
            (orderThreeCentralFiberPresentationData A.periods)
              (A.orderThreeActualCoverToCanonicalRadialHomeomorph q)) =
        A.orderThreeActualFillingToCanonicalRadialHomeomorph.symm
          (A.orderThreeActualFillingToCanonicalRadialHomeomorph
            (A.orderThreeActualEllipticFillingProjection q)) := by
              rw [A.orderThreeActualFillingProjection_canonicalRadial]
      _ = A.orderThreeActualEllipticFillingProjection q :=
        A.orderThreeActualFillingToCanonicalRadialHomeomorph.symm_apply_apply _
  rw [heq] at h
  exact h

public theorem orderFourActualEllipticFillingProjection_isQuotientCoveringMap :
    letI := A.orderFourActualRadialFillingDeckAction
    IsQuotientCoveringMap A.orderFourActualEllipticFillingProjection
      A.orderFourActualEllipticBoundaryDeckData.FillingDeck := by
  let _ := A.orderFourActualRadialFillingDeckAction
  have h := A.orderFourActualCanonicalRadialProjection_isQuotientCoveringMap.homeomorph_comp
    A.orderFourActualFillingToCanonicalRadialHomeomorph.symm
  have heq :
      A.orderFourActualFillingToCanonicalRadialHomeomorph.symm ∘
          ((affineCyclicRadialFillingProjection
            (orderFourCentralFiberPresentationData A.periods)) ∘
              A.orderFourActualCoverToCanonicalRadialHomeomorph) =
        A.orderFourActualEllipticFillingProjection := by
    funext q
    calc
      A.orderFourActualFillingToCanonicalRadialHomeomorph.symm
          (affineCyclicRadialFillingProjection
            (orderFourCentralFiberPresentationData A.periods)
              (A.orderFourActualCoverToCanonicalRadialHomeomorph q)) =
        A.orderFourActualFillingToCanonicalRadialHomeomorph.symm
          (A.orderFourActualFillingToCanonicalRadialHomeomorph
            (A.orderFourActualEllipticFillingProjection q)) := by
              rw [A.orderFourActualFillingProjection_canonicalRadial]
      _ = A.orderFourActualEllipticFillingProjection q :=
        A.orderFourActualFillingToCanonicalRadialHomeomorph.symm_apply_apply _
  rw [heq] at h
  exact h

end SphereSixComplex.Geometry.PaperAnalyticData
