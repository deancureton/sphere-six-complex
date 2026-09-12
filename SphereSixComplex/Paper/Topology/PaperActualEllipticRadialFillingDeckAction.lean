module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticFillingDeckTransport
public import SphereSixComplex.Paper.Topology.PaperAffineCyclicRadialQuotientCovering

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.EllipticFilling
open SphereSixComplex.AffineCyclicQuotientHomology
open _root_.SphereSixComplex.AffineCyclicQuotientHomology

variable (A : AnalyticData)

/-- Reassociation of a disc-ball product as a radial product ball. -/
public def complexDiscBallProductRadialHomeomorph
    {r : ℝ} {T : Type} [TopologicalSpace T] :
    ComplexDiscBall r × T ≃ₜ ComplexDisc.ProductBall r T where
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
public noncomputable def ellipticThreeUnitRadialFillingDeckAction :
    MulAction A.ellipticThreeBoundaryDeckData.FillingDeck
      (ComplexUnitDisc × ComplexTwoSpace) := by
  let P := orderThreeCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  let _ := actionH
  exact MulAction.compHom (ComplexUnitDisc × ComplexTwoSpace)
    A.ellipticThreeToCanonicalFillingDeckEquiv.toMonoidHom

public theorem ellipticThreeUnitRadialFilling_isQuotientCoveringMap :
    letI := A.ellipticThreeUnitRadialFillingDeckAction
    IsQuotientCoveringMap
      (affineCyclicRadialFillingProjection
        (orderThreeCentralFiberPresentationData A.periods))
      A.ellipticThreeBoundaryDeckData.FillingDeck := by
  let P := orderThreeCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  exact isQuotientCoveringMap_compMulEquiv actionH
    A.ellipticThreeToCanonicalFillingDeckEquiv _
    (affineCyclicRadialFilling_isQuotientCoveringMap P
      (orderThreeCentralFiberPresentationData_lift_continuous A.periods)
      (orderThreeCentralFiberPresentationData_lift_symm_continuous A.periods))

@[instance_reducible]
public noncomputable def ellipticFourUnitRadialFillingDeckAction :
    MulAction A.ellipticFourBoundaryDeckData.FillingDeck
      (ComplexUnitDisc × ComplexTwoSpace) := by
  let P := orderFourCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  let _ := actionH
  exact MulAction.compHom (ComplexUnitDisc × ComplexTwoSpace)
    A.ellipticFourToCanonicalFillingDeckEquiv.toMonoidHom

public theorem ellipticFourUnitRadialFilling_isQuotientCoveringMap :
    letI := A.ellipticFourUnitRadialFillingDeckAction
    IsQuotientCoveringMap
      (affineCyclicRadialFillingProjection
        (orderFourCentralFiberPresentationData A.periods))
      A.ellipticFourBoundaryDeckData.FillingDeck := by
  let P := orderFourCentralFiberPresentationData A.periods
  let actionH := affineCyclicRadialFillingDeckAction P
  exact isQuotientCoveringMap_compMulEquiv actionH
    A.ellipticFourToCanonicalFillingDeckEquiv _
    (affineCyclicRadialFilling_isQuotientCoveringMap P
      (orderFourCentralFiberPresentationData_lift_continuous A.periods)
      (orderFourCentralFiberPresentationData_lift_symm_continuous A.periods))

public noncomputable def ellipticThreeCoverToCanonicalRadialHomeomorph :
    ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace ≃ₜ
      ComplexUnitDisc × ComplexTwoSpace :=
  (A.orderThreeFillingCoverRealPeriodHomeomorph
      A.starSeparation.orderThree.radius).trans
    ((complexDiscBallProductRadialHomeomorph
      (r := A.starSeparation.orderThree.radius) (T := ComplexTwoSpace)).trans
      (ComplexDisc.productBallHomeomorph A.starSeparation.orderThree.radius_pos
        A.starSeparation.orderThree.radius_lt_one))

public noncomputable def ellipticFourCoverToCanonicalRadialHomeomorph :
    ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace ≃ₜ
      ComplexUnitDisc × ComplexTwoSpace :=
  (A.orderFourFillingCoverRealPeriodHomeomorph
      A.starSeparation.orderFour.radius).trans
    ((complexDiscBallProductRadialHomeomorph
      (r := A.starSeparation.orderFour.radius) (T := ComplexTwoSpace)).trans
      (ComplexDisc.productBallHomeomorph A.starSeparation.orderFour.radius_pos
        A.starSeparation.orderFour.radius_lt_one))

@[instance_reducible]
public noncomputable def ellipticThreeRadialFillingDeckAction :
    MulAction A.ellipticThreeBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace) :=
  pullbackMulActionHomeomorph A.ellipticThreeUnitRadialFillingDeckAction
    A.ellipticThreeCoverToCanonicalRadialHomeomorph

public theorem ellipticThreeCanonicalRadialProjection_isQuotientCoveringMap :
    letI := A.ellipticThreeRadialFillingDeckAction
    IsQuotientCoveringMap
      ((affineCyclicRadialFillingProjection
        (orderThreeCentralFiberPresentationData A.periods)) ∘
          A.ellipticThreeCoverToCanonicalRadialHomeomorph)
      A.ellipticThreeBoundaryDeckData.FillingDeck := by
  exact isQuotientCoveringMap_comp_homeomorph
    A.ellipticThreeUnitRadialFillingDeckAction
    A.ellipticThreeCoverToCanonicalRadialHomeomorph _
    A.ellipticThreeUnitRadialFilling_isQuotientCoveringMap

@[instance_reducible]
public noncomputable def ellipticFourRadialFillingDeckAction :
    MulAction A.ellipticFourBoundaryDeckData.FillingDeck
      (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace) :=
  pullbackMulActionHomeomorph A.ellipticFourUnitRadialFillingDeckAction
    A.ellipticFourCoverToCanonicalRadialHomeomorph

public theorem ellipticFourCanonicalRadialProjection_isQuotientCoveringMap :
    letI := A.ellipticFourRadialFillingDeckAction
    IsQuotientCoveringMap
      ((affineCyclicRadialFillingProjection
        (orderFourCentralFiberPresentationData A.periods)) ∘
          A.ellipticFourCoverToCanonicalRadialHomeomorph)
      A.ellipticFourBoundaryDeckData.FillingDeck := by
  exact isQuotientCoveringMap_comp_homeomorph
    A.ellipticFourUnitRadialFillingDeckAction
    A.ellipticFourCoverToCanonicalRadialHomeomorph _
    A.ellipticFourUnitRadialFilling_isQuotientCoveringMap

public noncomputable def ellipticThreeFillingToCanonicalRadialHomeomorph :
    A.actualVanKampenFourPieceCover.ellipticThree ≃ₜ
      (orderThreeRadialActionData A.periods).FillingQuotient :=
  A.orderThreeFillingToActualPieceHomeomorph.symm.trans
    ((orderThreeAffineRadialCompatibility A
      A.starSeparation.orderThree.radius
      A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).toProductIdentification.quotientHomeomorph)

public noncomputable def ellipticFourFillingToCanonicalRadialHomeomorph :
    A.actualVanKampenFourPieceCover.ellipticFour ≃ₜ
      (orderFourRadialActionData A.periods).FillingQuotient :=
  A.orderFourFillingToActualPieceHomeomorph.symm.trans
    ((orderFourAffineRadialCompatibility A
      A.starSeparation.orderFour.radius
      A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).toProductIdentification.quotientHomeomorph)

public theorem ellipticThreeFillingProjection_canonicalRadial
    (q : ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace) :
    A.ellipticThreeFillingToCanonicalRadialHomeomorph
        (A.ellipticThreeFillingProjection q) =
      affineCyclicRadialFillingProjection
        (orderThreeCentralFiberPresentationData A.periods)
        (A.ellipticThreeCoverToCanonicalRadialHomeomorph q) := by
  change
    (orderThreeAffineRadialCompatibility A
      A.starSeparation.orderThree.radius
      A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one).toProductIdentification.quotientHomeomorph
        (A.orderThreeFillingToActualPieceHomeomorph.symm
          (A.ellipticThreeFillingProjection q)) = _
  have hproj : A.ellipticThreeFillingProjection q =
      A.orderThreeFillingToActualPieceHomeomorph
        (A.ellipticThreeFillingCoverProjection
          A.starSeparation.orderThree.radius q) := rfl
  rw [hproj]
  rw [A.orderThreeFillingToActualPieceHomeomorph.symm_apply_apply]
  have hcover : A.ellipticThreeFillingCoverProjection
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

public theorem ellipticFourFillingProjection_canonicalRadial
    (q : ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace) :
    A.ellipticFourFillingToCanonicalRadialHomeomorph
        (A.ellipticFourFillingProjection q) =
      affineCyclicRadialFillingProjection
        (orderFourCentralFiberPresentationData A.periods)
        (A.ellipticFourCoverToCanonicalRadialHomeomorph q) := by
  change
    (orderFourAffineRadialCompatibility A
      A.starSeparation.orderFour.radius
      A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one).toProductIdentification.quotientHomeomorph
        (A.orderFourFillingToActualPieceHomeomorph.symm
          (A.ellipticFourFillingProjection q)) = _
  have hproj : A.ellipticFourFillingProjection q =
      A.orderFourFillingToActualPieceHomeomorph
        (A.ellipticFourFillingCoverProjection
          A.starSeparation.orderFour.radius q) := rfl
  rw [hproj]
  rw [A.orderFourFillingToActualPieceHomeomorph.symm_apply_apply]
  have hcover : A.ellipticFourFillingCoverProjection
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

public theorem ellipticThreeFillingProjection_isQuotientCoveringMap :
    letI := A.ellipticThreeRadialFillingDeckAction
    IsQuotientCoveringMap A.ellipticThreeFillingProjection
      A.ellipticThreeBoundaryDeckData.FillingDeck := by
  let _ := A.ellipticThreeRadialFillingDeckAction
  have h := A.ellipticThreeCanonicalRadialProjection_isQuotientCoveringMap.homeomorph_comp
    A.ellipticThreeFillingToCanonicalRadialHomeomorph.symm
  have heq :
      A.ellipticThreeFillingToCanonicalRadialHomeomorph.symm ∘
          ((affineCyclicRadialFillingProjection
            (orderThreeCentralFiberPresentationData A.periods)) ∘
              A.ellipticThreeCoverToCanonicalRadialHomeomorph) =
        A.ellipticThreeFillingProjection := by
    funext q
    calc
      A.ellipticThreeFillingToCanonicalRadialHomeomorph.symm
          (affineCyclicRadialFillingProjection
            (orderThreeCentralFiberPresentationData A.periods)
              (A.ellipticThreeCoverToCanonicalRadialHomeomorph q)) =
        A.ellipticThreeFillingToCanonicalRadialHomeomorph.symm
          (A.ellipticThreeFillingToCanonicalRadialHomeomorph
            (A.ellipticThreeFillingProjection q)) := by
              rw [A.ellipticThreeFillingProjection_canonicalRadial]
      _ = A.ellipticThreeFillingProjection q :=
        A.ellipticThreeFillingToCanonicalRadialHomeomorph.symm_apply_apply _
  rw [heq] at h
  exact h

public theorem ellipticFourFillingProjection_isQuotientCoveringMap :
    letI := A.ellipticFourRadialFillingDeckAction
    IsQuotientCoveringMap A.ellipticFourFillingProjection
      A.ellipticFourBoundaryDeckData.FillingDeck := by
  let _ := A.ellipticFourRadialFillingDeckAction
  have h := A.ellipticFourCanonicalRadialProjection_isQuotientCoveringMap.homeomorph_comp
    A.ellipticFourFillingToCanonicalRadialHomeomorph.symm
  have heq :
      A.ellipticFourFillingToCanonicalRadialHomeomorph.symm ∘
          ((affineCyclicRadialFillingProjection
            (orderFourCentralFiberPresentationData A.periods)) ∘
              A.ellipticFourCoverToCanonicalRadialHomeomorph) =
        A.ellipticFourFillingProjection := by
    funext q
    calc
      A.ellipticFourFillingToCanonicalRadialHomeomorph.symm
          (affineCyclicRadialFillingProjection
            (orderFourCentralFiberPresentationData A.periods)
              (A.ellipticFourCoverToCanonicalRadialHomeomorph q)) =
        A.ellipticFourFillingToCanonicalRadialHomeomorph.symm
          (A.ellipticFourFillingToCanonicalRadialHomeomorph
            (A.ellipticFourFillingProjection q)) := by
              rw [A.ellipticFourFillingProjection_canonicalRadial]
      _ = A.ellipticFourFillingProjection q :=
        A.ellipticFourFillingToCanonicalRadialHomeomorph.symm_apply_apply _
  rw [heq] at h
  exact h

end SphereSixComplex.Geometry.AnalyticData
