module

public import SphereSixComplex.Geometry.PaperAnalyticFillingPieces
public import SphereSixComplex.Geometry.GlobalTorusFiberFundamentalGroup

/-!
# Fundamental-group surjectivity for the elliptic collar inclusions

The period cover of either elliptic filling is a Cayley disc times the affine fibre.  Its
punctured collar is the corresponding punctured disc times the same fibre.  This file makes
those identifications at the level of the preimages of the regular family-period covering and
uses them to transfer surjectivity on fundamental groups through that covering.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open TorusFamily AnalyticTorusFamily GlobalTorusFamily ComplexTorus
open EllipticLocalCoordinates EllipticCayleyHomeomorph
open EllipticVaryingFamilyQuotient EllipticPuncturedCollarGaugeHomeomorph
open EllipticWholeFiberCompactCover
open EllipticLinearCollarGlobalDescent
open EquivariantQuotientHomeomorph

namespace PaperAnalyticData

variable (A : PaperAnalyticData)

/-- Cayley coordinates identify a filled elliptic vector-cover region with a disc times the
affine fibre. -/
@[expose] public noncomputable def cayleyBallVectorPreimageHomeomorph
    (e : UpperHalfPlane ≃ₜ ComplexUnitDisc) (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ
      {p : UpperHalfPlane × ComplexTwoSpace | ‖(e p.1 : ComplexUnitDisc).1‖ < r} where
  toFun p := ⟨(e.symm p.1.1, p.2), by
    change ‖((e (e.symm p.1.1) : ComplexUnitDisc) : ℂ)‖ < r
    rw [e.apply_symm_apply]
    exact p.1.2⟩
  invFun p := (⟨e p.1.1, p.2⟩, p.1.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact e.apply_symm_apply p.1.1
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.symm_apply_apply p.1.1
    · rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (e.symm.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  continuous_invFun := by
    exact (Continuous.subtype_mk
      (e.continuous.comp (continuous_fst.comp continuous_subtype_val)) _).prodMk
        (continuous_snd.comp continuous_subtype_val)

/-- The punctured Cayley region has the analogous product description. -/
@[expose] public noncomputable def cayleyPuncturedBallVectorPreimageHomeomorph
    (e : UpperHalfPlane ≃ₜ ComplexUnitDisc) (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace ≃ₜ
      {p : UpperHalfPlane × ComplexTwoSpace |
        0 < ‖(e p.1 : ComplexUnitDisc).1‖ ∧ ‖(e p.1 : ComplexUnitDisc).1‖ < r} where
  toFun p := ⟨(e.symm p.1.1, p.2), by
    change 0 < ‖((e (e.symm p.1.1) : ComplexUnitDisc) : ℂ)‖ ∧
      ‖((e (e.symm p.1.1) : ComplexUnitDisc) : ℂ)‖ < r
    rw [e.apply_symm_apply]
    exact p.1.2⟩
  invFun p := (⟨e p.1.1, p.2⟩, p.1.2)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact e.apply_symm_apply p.1.1
    · rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.symm_apply_apply p.1.1
    · rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (e.symm.continuous.comp
      (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
  continuous_invFun := by
    exact (Continuous.subtype_mk
      (e.continuous.comp (continuous_fst.comp continuous_subtype_val)) _).prodMk
        (continuous_snd.comp continuous_subtype_val)

public theorem orderThreeFillingCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderThreeFillingOpen r : Set (TotalSpace (parameterMap A.periods))) := by
  ext p
  change ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r ↔
    orderThreeFamilyRadius A.periods (Quotient.mk _ p) < r
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk]

public theorem orderFourFillingCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderFourFillingOpen r : Set (TotalSpace (parameterMap A.periods))) := by
  ext p
  change ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r ↔
    orderFourFamilyRadius A.periods (Quotient.mk _ p) < r
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk]

public theorem orderThreePuncturedCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        0 < ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
          ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := by
  ext p
  change (0 < ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
      ‖(orderThreeCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r) ↔
    (0 < orderThreeFamilyRadius A.periods (Quotient.mk _ p) ∧
      orderThreeFamilyRadius A.periods (Quotient.mk _ p) < r)
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_mk]

public theorem orderFourPuncturedCoverPreimage_eq (r : ℝ) :
    {p : UpperHalfPlane × ComplexTwoSpace |
        0 < ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
          ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r} =
      (projection (parameterMap A.periods)) ⁻¹'
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier := by
  ext p
  change (0 < ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ ∧
      ‖(orderFourCayleyHomeomorph p.1 : ComplexUnitDisc).1‖ < r) ↔
    (0 < orderFourFamilyRadius A.periods (Quotient.mk _ p) ∧
      orderFourFamilyRadius A.periods (Quotient.mk _ p) < r)
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_mk]

@[expose] public noncomputable def orderThreeFillingCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderThreeFillingOpen r : Set (TotalSpace (parameterMap A.periods))) :=
  (cayleyBallVectorPreimageHomeomorph orderThreeCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderThreeFillingCoverPreimage_eq r))

@[expose] public noncomputable def orderFourFillingCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (A.orderFourFillingOpen r : Set (TotalSpace (parameterMap A.periods))) :=
  (cayleyBallVectorPreimageHomeomorph orderFourCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderFourFillingCoverPreimage_eq r))

@[expose] public noncomputable def orderThreePuncturedCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (orderThreeAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
  (cayleyPuncturedBallVectorPreimageHomeomorph orderThreeCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderThreePuncturedCoverPreimage_eq r))

@[expose] public noncomputable def orderFourPuncturedCoverPreimageHomeomorph (r : ℝ) :
    ComplexDiscPuncturedBall r × ComplexTwoSpace ≃ₜ
      (projection (parameterMap A.periods)) ⁻¹'
        (orderFourAffinePuncturedCarrier A.periods
          A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier :=
  (cayleyPuncturedBallVectorPreimageHomeomorph orderFourCayleyHomeomorph r).trans
    (Homeomorph.setCongr (A.orderFourPuncturedCoverPreimage_eq r))

/-- The full family-period projection is a quotient covering by the globally labelled period
lattice.  Unlike the regular-family version, this statement includes the elliptic basepoints. -/
public theorem familyProjection_isQuotientCoveringMap :
    letI := familyMulAction (parameterMap A.periods)
    IsQuotientCoveringMap (projection (parameterMap A.periods))
      (FamilyPeriodGroup (parameterMap A.periods)) := by
  let _ := familyMulAction (parameterMap A.periods)
  let _ := familyIsCancelSMul (parameterMap A.periods)
  let _ := familyContinuousConstSMul (parameterMap A.periods)
    (fun a ↦ (periodSection_contMDiff A.periods a 0).continuous)
  let _ := familyProperlyDiscontinuousSMul (parameterMap A.periods)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap A.periods)
      (parameterMap_compactUniformLowerBound A.periods))
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- Before taking the finite cyclic quotient, the order-three punctured-collar inclusion
surjects on fundamental groups. -/
public theorem orderThreePuncturedSourceToFillingSource_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderThreePuncturedSourceToFillingSource r,
          (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩ :
          C((orderThreeAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
            A.orderThreeFillingOpen r))
        (⟨projection (parameterMap A.periods) x, hx⟩ :
          (orderThreeAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier)) := by
  let f := projection (parameterMap A.periods)
  let W : Set (TotalSpace (parameterMap A.periods)) :=
    (orderThreeAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier
  let V : Set (TotalSpace (parameterMap A.periods)) := A.orderThreeFillingOpen r
  have hWV : W ⊆ V := A.orderThreePuncturedCarrier_subset_filling r
  let _ := familyMulAction (parameterMap A.periods)
  let hf : IsQuotientCoveringMap f (FamilyPeriodGroup (parameterMap A.periods)) :=
    A.familyProjection_isQuotientCoveringMap
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  let _ : PathConnectedSpace (f ⁻¹' W) :=
    (A.orderThreePuncturedCoverPreimageHomeomorph r).surjective.pathConnectedSpace
      (A.orderThreePuncturedCoverPreimageHomeomorph r).continuous
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  let _ : SimplyConnectedSpace (f ⁻¹' V) :=
    (A.orderThreeFillingCoverPreimageHomeomorph r).toHomotopyEquiv
      |>.simplyConnectedSpace_iff.mp inferInstance
  have hsource : Function.Surjective
      (FundamentalGroup.map
        (continuousSetInclusion (fun _ hz ↦ hWV hz) : C(f ⁻¹' W, f ⁻¹' V))
        (⟨x, hx⟩ : f ⁻¹' W)) := by
    intro q
    exact ⟨1, Subsingleton.elim _ q⟩
  have h := quotientCovering_restrict_inclusion_fundamentalGroup_surjective
    hf hWV x hx hsource
  let actual : C(W, V) :=
    ⟨A.orderThreePuncturedSourceToFillingSource r,
      (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  have hactual : actual = continuousSetInclusion hWV := by
    ext z
    rfl
  change Function.Surjective
    (FundamentalGroup.map actual
      (⟨projection (parameterMap A.periods) x, hx⟩ : W))
  rw [hactual]
  exact h

/-- The analogous order-four inclusion before the finite cyclic quotient is also surjective on
fundamental groups. -/
public theorem orderFourPuncturedSourceToFillingSource_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderFourPuncturedSourceToFillingSource r,
          (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩ :
          C((orderFourAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier,
            A.orderFourFillingOpen r))
        (⟨projection (parameterMap A.periods) x, hx⟩ :
          (orderFourAffinePuncturedCarrier A.periods
            A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier)) := by
  let f := projection (parameterMap A.periods)
  let W : Set (TotalSpace (parameterMap A.periods)) :=
    (orderFourAffinePuncturedCarrier A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier
  let V : Set (TotalSpace (parameterMap A.periods)) := A.orderFourFillingOpen r
  have hWV : W ⊆ V := A.orderFourPuncturedCarrier_subset_filling r
  let _ := familyMulAction (parameterMap A.periods)
  let hf : IsQuotientCoveringMap f (FamilyPeriodGroup (parameterMap A.periods)) :=
    A.familyProjection_isQuotientCoveringMap
  let _ : PathConnectedSpace (ComplexDiscPuncturedBall r) :=
    complexDiscPuncturedBall_pathConnected hr hr1
  let _ : PathConnectedSpace (f ⁻¹' W) :=
    (A.orderFourPuncturedCoverPreimageHomeomorph r).surjective.pathConnectedSpace
      (A.orderFourPuncturedCoverPreimageHomeomorph r).continuous
  let _ : ContractibleSpace (ComplexDiscBall r) := complexDiscBall_contractible hr hr1
  let _ : SimplyConnectedSpace (ComplexDiscBall r × ComplexTwoSpace) := inferInstance
  let _ : SimplyConnectedSpace (f ⁻¹' V) :=
    (A.orderFourFillingCoverPreimageHomeomorph r).toHomotopyEquiv
      |>.simplyConnectedSpace_iff.mp inferInstance
  have hsource : Function.Surjective
      (FundamentalGroup.map
        (continuousSetInclusion (fun _ hz ↦ hWV hz) : C(f ⁻¹' W, f ⁻¹' V))
        (⟨x, hx⟩ : f ⁻¹' W)) := by
    intro q
    exact ⟨1, Subsingleton.elim _ q⟩
  have h := quotientCovering_restrict_inclusion_fundamentalGroup_surjective
    hf hWV x hx hsource
  let actual : C(W, V) :=
    ⟨A.orderFourPuncturedSourceToFillingSource r,
      (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  have hactual : actual = continuousSetInclusion hWV := by
    ext z
    rfl
  change Function.Surjective
    (FundamentalGroup.map actual
      (⟨projection (parameterMap A.periods) x, hx⟩ : W))
  rw [hactual]
  exact h

/-- After the finite order-three affine quotient, the actual collar map into the filling remains
surjective on fundamental groups. -/
public theorem orderThreePuncturedCollarToFilling_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderThreePuncturedCollarToFilling r,
          A.orderThreePuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
              (orderThreeAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderThreeVaryingFilling r))
        (Quotient.mk _
          (⟨projection (parameterMap A.periods) x, hx⟩ :
            (orderThreeAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier))) := by
  let S := orderThreeAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let q : S.carrier := ⟨projection (parameterMap A.periods) x, hx⟩
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace S.carrier := S.isOpen_carrier.locallyCompactSpace
  let _ : T2Space S.carrier := by infer_instance
  let _ : LocallyCompactSpace (A.orderThreeFillingOpen r) :=
    (A.orderThreeFillingOpen r).2.locallyCompactSpace
  let _ : T2Space (A.orderThreeFillingOpen r) := by infer_instance
  let _ := restrictedMulAction (orderThreeAffineFamilyAction A.periods) S
  let _ : IsCancelSMul (FiniteCyclic 3) S.carrier :=
    orderThreeAffinePuncturedAction_free A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ : ContinuousConstSMul (FiniteCyclic 3) S.carrier :=
    ⟨fun g ↦ (orderThreeAffinePuncturedAction_contMDiff A.periods
      A.totalSpace_projection_isLocalDiffeomorph
      A.modular.modularParameter.toTriangleUniformization_sourceAction r g).continuous⟩
  let _ := A.orderThreeFillingAction r
  let _ : IsCancelSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 3) (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingAction_continuousConstSMul r
  let hfS : IsQuotientCoveringMap
      (Quotient.mk (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods) S))
      (FiniteCyclic 3) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let hfV : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic 3) (A.orderThreeFillingOpen r)))
      (FiniteCyclic 3) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let sourceMap : C(S.carrier, A.orderThreeFillingOpen r) :=
    ⟨A.orderThreePuncturedSourceToFillingSource r,
      (A.orderThreePuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  let targetMap : C(Quotient (restrictedOrbitRel
      (orderThreeAffineFamilyAction A.periods) S), A.OrderThreeVaryingFilling r) :=
    ⟨A.orderThreePuncturedCollarToFilling r,
      A.orderThreePuncturedCollarToFilling_continuous r⟩
  have hcomm (y : S.carrier) :
      targetMap (Quotient.mk _ y) = Quotient.mk _ (sourceMap y) := by
    exact A.orderThreePuncturedCollarToFilling_mk r y
  have hequiv (g : FiniteCyclic 3) (y : S.carrier) :
      sourceMap (g • y) = g • sourceMap y := by
    apply Subtype.ext
    rfl
  let _ : PathConnectedSpace S.carrier :=
    A.orderThreeAffinePuncturedCarrier_pathConnected hr hr1
  let _ : PathConnectedSpace (A.orderThreeFillingOpen r) :=
    A.orderThreeFillingOpen_pathConnected hr hr1
  have hsource : Function.Surjective (FundamentalGroup.map sourceMap q) := by
    simpa [sourceMap, q, S] using
      A.orderThreePuncturedSourceToFillingSource_fundamentalGroup_surjective
        hr hr1 x hx
  have hmapOfEq := quotientCovering_equivariant_map_fundamentalGroup_surjective
    hfS hfV sourceMap targetMap hcomm hequiv q hsource
  exact fundamentalGroup_map_surjective_of_mapOfEq_surjective
    targetMap (Quotient.mk _ q) (Quotient.mk _ (sourceMap q)) (hcomm q) hmapOfEq

/-- The full order-four punctured-collar map is likewise surjective on fundamental groups. -/
public theorem orderFourPuncturedCollarToFilling_fundamentalGroup_surjective
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (x : UpperHalfPlane × ComplexTwoSpace)
    (hx : projection (parameterMap A.periods) x ∈
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderFourPuncturedCollarToFilling r,
          A.orderFourPuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
              (orderFourAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderFourVaryingFilling r))
        (Quotient.mk _
          (⟨projection (parameterMap A.periods) x, hx⟩ :
            (orderFourAffinePuncturedCarrier A.periods
              A.modular.modularParameter.toTriangleUniformization_sourceAction r).carrier))) := by
  let S := orderFourAffinePuncturedCarrier A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let q : S.carrier := ⟨projection (parameterMap A.periods) x, hx⟩
  let _ := A.totalSpaceCharts
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (TotalSpace (parameterMap A.periods)) := A.totalSpace_isManifold
  let _ : LocallyCompactSpace (TotalSpace (parameterMap A.periods)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ : T2Space (TotalSpace (parameterMap A.periods)) := A.totalSpace_t2
  let _ : LocallyCompactSpace S.carrier := S.isOpen_carrier.locallyCompactSpace
  let _ : T2Space S.carrier := by infer_instance
  let _ : LocallyCompactSpace (A.orderFourFillingOpen r) :=
    (A.orderFourFillingOpen r).2.locallyCompactSpace
  let _ : T2Space (A.orderFourFillingOpen r) := by infer_instance
  let _ := restrictedMulAction (orderFourAffineFamilyAction A.periods) S
  let _ : IsCancelSMul (FiniteCyclic 4) S.carrier :=
    orderFourAffinePuncturedAction_free A.periods
      A.modular.modularParameter.toTriangleUniformization_sourceAction r
  let _ : ContinuousConstSMul (FiniteCyclic 4) S.carrier :=
    ⟨fun g ↦ (orderFourAffinePuncturedAction_contMDiff A.periods
      A.totalSpace_projection_isLocalDiffeomorph
      A.modular.modularParameter.toTriangleUniformization_sourceAction r g).continuous⟩
  let _ := A.orderFourFillingAction r
  let _ : IsCancelSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_free r
  let _ : ContinuousConstSMul (FiniteCyclic 4) (A.orderFourFillingOpen r) :=
    A.orderFourFillingAction_continuousConstSMul r
  let hfS : IsQuotientCoveringMap
      (Quotient.mk (restrictedOrbitRel (orderFourAffineFamilyAction A.periods) S))
      (FiniteCyclic 4) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let hfV : IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (FiniteCyclic 4) (A.orderFourFillingOpen r)))
      (FiniteCyclic 4) := by
    exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
  let sourceMap : C(S.carrier, A.orderFourFillingOpen r) :=
    ⟨A.orderFourPuncturedSourceToFillingSource r,
      (A.orderFourPuncturedSourceToFillingSource_isOpenEmbedding r).continuous⟩
  let targetMap : C(Quotient (restrictedOrbitRel
      (orderFourAffineFamilyAction A.periods) S), A.OrderFourVaryingFilling r) :=
    ⟨A.orderFourPuncturedCollarToFilling r,
      A.orderFourPuncturedCollarToFilling_continuous r⟩
  have hcomm (y : S.carrier) :
      targetMap (Quotient.mk _ y) = Quotient.mk _ (sourceMap y) := by
    exact A.orderFourPuncturedCollarToFilling_mk r y
  have hequiv (g : FiniteCyclic 4) (y : S.carrier) :
      sourceMap (g • y) = g • sourceMap y := by
    apply Subtype.ext
    rfl
  let _ : PathConnectedSpace S.carrier :=
    A.orderFourAffinePuncturedCarrier_pathConnected hr hr1
  let _ : PathConnectedSpace (A.orderFourFillingOpen r) :=
    A.orderFourFillingOpen_pathConnected hr hr1
  have hsource : Function.Surjective (FundamentalGroup.map sourceMap q) := by
    simpa [sourceMap, q, S] using
      A.orderFourPuncturedSourceToFillingSource_fundamentalGroup_surjective
        hr hr1 x hx
  have hmapOfEq := quotientCovering_equivariant_map_fundamentalGroup_surjective
    hfS hfV sourceMap targetMap hcomm hequiv q hsource
  exact fundamentalGroup_map_surjective_of_mapOfEq_surjective
    targetMap (Quotient.mk _ q) (Quotient.mk _ (sourceMap q)) (hcomm q) hmapOfEq

/-- Basepoint-free form of the order-three collar surjectivity theorem. -/
public theorem orderThreePuncturedCollarToFilling_fundamentalGroup_surjective_at
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (q : Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
      (orderThreeAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r))) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderThreePuncturedCollarToFilling r,
          A.orderThreePuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderThreeAffineFamilyAction A.periods)
              (orderThreeAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderThreeVaryingFilling r)) q) := by
  induction q using Quotient.inductionOn with
  | _ y =>
      rcases y with ⟨z, hz⟩
      induction z using Quotient.inductionOn with
      | _ x =>
          exact A.orderThreePuncturedCollarToFilling_fundamentalGroup_surjective
            hr hr1 x hz

/-- Basepoint-free form of the order-four collar surjectivity theorem. -/
public theorem orderFourPuncturedCollarToFilling_fundamentalGroup_surjective_at
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (q : Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
      (orderFourAffinePuncturedCarrier A.periods
        A.modular.modularParameter.toTriangleUniformization_sourceAction r))) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨A.orderFourPuncturedCollarToFilling r,
          A.orderFourPuncturedCollarToFilling_continuous r⟩ :
          C(Quotient (restrictedOrbitRel (orderFourAffineFamilyAction A.periods)
              (orderFourAffinePuncturedCarrier A.periods
                A.modular.modularParameter.toTriangleUniformization_sourceAction r)),
            A.OrderFourVaryingFilling r)) q) := by
  induction q using Quotient.inductionOn with
  | _ y =>
      rcases y with ⟨z, hz⟩
      induction z using Quotient.inductionOn with
      | _ x =>
          exact A.orderFourPuncturedCollarToFilling_fundamentalGroup_surjective
            hr hr1 x hz

end PaperAnalyticData

end SphereSixComplex.Geometry
