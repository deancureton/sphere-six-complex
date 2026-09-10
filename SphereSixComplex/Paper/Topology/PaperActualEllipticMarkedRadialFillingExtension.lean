module

public import SphereSixComplex.Paper.Topology.PaperActualEllipticRadialFillingDeckAction

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization
open SphereSixComplex.LatticeData
open SphereSixComplex.Topology
open SphereSixComplex.TriangleGroup
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology
open _root_.SphereSixComplex.AffineCyclicQuotientHomology

variable (A : PaperAnalyticData)

private theorem pullbackMulActionHomeomorph_apply
    {G E E' : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace E']
    (action : MulAction G E) (e : E' ≃ₜ E) (g : G) (x : E') :
    e (@SMul.smul _ _ (pullbackMulActionHomeomorph action e).toSMul g x) =
      @SMul.smul _ _ action.toSMul g (e x) := by
  exact e.apply_symm_apply _

private theorem standardMultiplier_zmodVal_mul_angleMap
    (m : ℕ) [NeZero m] (k : ℤ) (theta : ℝ) :
    standardMultiplier m ^ ((k : ZMod m).val) *
        ((angleMap m theta : Circle) : ℂ) =
      ((angleMap m (theta - k) : Circle) : ℂ) := by
  rw [standardMultiplier_pow_mul_angleMap]
  apply congrArg (fun z : Circle => (z : ℂ))
  apply (angleMap_eq_iff (m := m)
    (theta - (((k : ZMod m).val : ℕ) : ℝ)) (theta - (k : ℝ))).mpr
  have hd : (m : ℤ) ∣ k - ((k : ZMod m).val : ℤ) := by
    rw [ZMod.val_intCast]
    exact Int.dvd_self_sub_of_emod_eq rfl
  obtain ⟨l, hl⟩ := hd
  refine ⟨l, ?_⟩
  have hlR : (k : ℝ) - ((k : ZMod m).val : ℝ) =
      (m : ℝ) * (l : ℝ) := by
    exact_mod_cast hl
  rw [show (l : ℝ) * (m : ℝ) = (m : ℝ) * (l : ℝ) by ring, ← hlR]
  ring

/-- In canonical fixed radial coordinates, the order-three collar lift is the rescaled angular
cover together with its original fixed vector coordinate. -/
public theorem ellipticThreeCoverToCanonicalRadialHomeomorph_radialFillingLift
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    A.ellipticThreeCoverToCanonicalRadialHomeomorph
        (A.ellipticThreeRadialFillingLift q) =
      (⟨((angularCover (T := ComplexTwoSpace) 3
          A.starSeparation.orderThree.radius_lt_one.le q).1.1 : ℂ) /
            (A.starSeparation.orderThree.radius : ℂ), by
          rw [norm_div, Complex.norm_real,
            Real.norm_of_nonneg A.starSeparation.orderThree.radius_pos.le]
          exact (div_lt_one A.starSeparation.orderThree.radius_pos).mpr
            (angularCover (T := ComplexTwoSpace) 3
              A.starSeparation.orderThree.radius_lt_one.le q).2.2⟩,
        q.2.2) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · change
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (orderThreeCayleyHomeomorph.symm
          (angularCover (T := ComplexTwoSpace) 3
            A.starSeparation.orderThree.radius_lt_one.le q).1.1,
          (fixedToMovingCover A.periods
            A.modular.modularParameter.toTriangleUniformization.zOne
            (orderThreeCayleyHomeomorph.symm
              (angularCover (T := ComplexTwoSpace) 3
                A.starSeparation.orderThree.radius_lt_one.le q).1.1,
              (angularCover (T := ComplexTwoSpace) 3
                A.starSeparation.orderThree.radius_lt_one.le q).1.2)).2)).2 = q.2.2
    rw [show
      (orderThreeCayleyHomeomorph.symm
          (angularCover (T := ComplexTwoSpace) 3
            A.starSeparation.orderThree.radius_lt_one.le q).1.1,
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne
          (orderThreeCayleyHomeomorph.symm
            (angularCover (T := ComplexTwoSpace) 3
              A.starSeparation.orderThree.radius_lt_one.le q).1.1,
            (angularCover (T := ComplexTwoSpace) 3
              A.starSeparation.orderThree.radius_lt_one.le q).1.2)).2) =
        fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne
          (orderThreeCayleyHomeomorph.symm
            (angularCover (T := ComplexTwoSpace) 3
              A.starSeparation.orderThree.radius_lt_one.le q).1.1,
            (angularCover (T := ComplexTwoSpace) 3
              A.starSeparation.orderThree.radius_lt_one.le q).1.2) by
        apply Prod.ext <;> rfl,
      movingToFixedCover_fixedToMovingCover]
    rfl

/-- In canonical fixed radial coordinates, the order-four collar lift is the rescaled angular
cover together with its original fixed vector coordinate. -/
public theorem ellipticFourCoverToCanonicalRadialHomeomorph_radialFillingLift
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    A.ellipticFourCoverToCanonicalRadialHomeomorph
        (A.ellipticFourRadialFillingLift q) =
      (⟨((angularCover (T := ComplexTwoSpace) 4
          A.starSeparation.orderFour.radius_lt_one.le q).1.1 : ℂ) /
            (A.starSeparation.orderFour.radius : ℂ), by
          rw [norm_div, Complex.norm_real,
            Real.norm_of_nonneg A.starSeparation.orderFour.radius_pos.le]
          exact (div_lt_one A.starSeparation.orderFour.radius_pos).mpr
            (angularCover (T := ComplexTwoSpace) 4
              A.starSeparation.orderFour.radius_lt_one.le q).2.2⟩,
        q.2.2) := by
  apply Prod.ext
  · apply Subtype.ext
    rfl

  · change
      (movingToFixedCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo
        (orderFourCayleyHomeomorph.symm
          (angularCover (T := ComplexTwoSpace) 4
            A.starSeparation.orderFour.radius_lt_one.le q).1.1,
          (fixedToMovingCover A.periods
            A.modular.modularParameter.toTriangleUniformization.zTwo
            (orderFourCayleyHomeomorph.symm
              (angularCover (T := ComplexTwoSpace) 4
                A.starSeparation.orderFour.radius_lt_one.le q).1.1,
              (angularCover (T := ComplexTwoSpace) 4
                A.starSeparation.orderFour.radius_lt_one.le q).1.2)).2)).2 = q.2.2
    rw [show
      (orderFourCayleyHomeomorph.symm
          (angularCover (T := ComplexTwoSpace) 4
            A.starSeparation.orderFour.radius_lt_one.le q).1.1,
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo
          (orderFourCayleyHomeomorph.symm
            (angularCover (T := ComplexTwoSpace) 4
              A.starSeparation.orderFour.radius_lt_one.le q).1.1,
            (angularCover (T := ComplexTwoSpace) 4
              A.starSeparation.orderFour.radius_lt_one.le q).1.2)).2) =
        fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo
          (orderFourCayleyHomeomorph.symm
            (angularCover (T := ComplexTwoSpace) 4
              A.starSeparation.orderFour.radius_lt_one.le q).1.1,
            (angularCover (T := ComplexTwoSpace) 4
              A.starSeparation.orderFour.radius_lt_one.le q).1.2) by
        apply Prod.ext <;> rfl,
      movingToFixedCover_fixedToMovingCover]
    rfl

private theorem orderThreeActualEllipticBoundaryAction_snd
    (g : OrderThreeAffineMappingTorusDeck A.periods)
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.ellipticThreeBoundaryAction
    (g • q).2.2 =
      affineCyclicBoundaryDeckTransform (orderThreeCentralFiberPresentationData A.periods)
        (A.ellipticThreeToCentralBoundaryDeckEquiv g) q.2.2 := by
  let _ := A.ellipticThreeBoundaryAction
  change periodVector _ g.left.toAdd +
        (affineEquiv (orderThreeDescendedAffineTorusAutomorphism A.periods).lift
          ((3 : ℂ)⁻¹ • periodVector _ epsilon) ^ g.right.toAdd) q.2.2 =
      periodVector _ g.left.toAdd +
        (affineEquiv (orderThreeCentralFiberPresentationData A.periods).affine.lift
          (orderThreeCentralFiberPresentationData A.periods).liftTranslation ^
            g.right.toAdd) q.2.2
  rw [A.orderThreeCentralFiberPresentationData_affine_eq]
  have hb : ((3 : ℂ)⁻¹ • periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon) =
      (3 : ℝ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).1 epsilon := by
    ext i
    norm_num
  change _ + (affineEquiv _ ((3 : ℂ)⁻¹ • periodVector _ epsilon) ^ _) _ =
    _ + (affineEquiv _ ((3 : ℝ)⁻¹ • periodVector _ epsilon) ^ _) _
  rw [hb]

private theorem orderFourActualEllipticBoundaryAction_snd
    (g : OrderFourAffineMappingTorusDeck A.periods)
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.ellipticFourBoundaryAction
    (g • q).2.2 =
      affineCyclicBoundaryDeckTransform (orderFourCentralFiberPresentationData A.periods)
        (A.ellipticFourToCentralBoundaryDeckEquiv g) q.2.2 := by
  let _ := A.ellipticFourBoundaryAction
  change periodVector _ g.left.toAdd +
        (affineEquiv (orderFourDescendedAffineTorusAutomorphism A.periods).lift
          ((4 : ℂ)⁻¹ • periodVector _ (-epsilon')) ^ g.right.toAdd) q.2.2 =
      periodVector _ g.left.toAdd +
        (affineEquiv (orderFourCentralFiberPresentationData A.periods).affine.lift
          (orderFourCentralFiberPresentationData A.periods).liftTranslation ^
            g.right.toAdd) q.2.2
  rw [A.orderFourCentralFiberPresentationData_affine_eq]
  have hb : ((4 : ℂ)⁻¹ • periodVector
      (parameterMap A.periods
        A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon')) =
      (4 : ℝ)⁻¹ • periodVector
        (parameterMap A.periods
          A.modular.modularParameter.toTriangleUniformization.zTwo).1 (-epsilon') := by
    ext i
    norm_num
  change _ + (affineEquiv _ ((4 : ℂ)⁻¹ • periodVector _ (-epsilon')) ^ _) _ =
    _ + (affineEquiv _ ((4 : ℝ)⁻¹ • periodVector _ (-epsilon')) ^ _) _
  rw [hb]

/-- The actual order-three collar action and the transported filling action agree under the
canonical radial lift. -/
public theorem ellipticThreeRadialFillingLift_equivariant
    (g : OrderThreeAffineMappingTorusDeck A.periods)
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.ellipticThreeBoundaryAction
    letI := A.ellipticThreeRadialFillingDeckAction
    A.ellipticThreeRadialFillingLift (g • q) =
      A.ellipticThreeBoundaryDeckData.fillingDeckMap g •
        A.ellipticThreeRadialFillingLift q := by
  let _ := A.ellipticThreeBoundaryAction
  let _ := A.ellipticThreeRadialFillingDeckAction
  apply A.ellipticThreeCoverToCanonicalRadialHomeomorph.injective
  rw [A.ellipticThreeCoverToCanonicalRadialHomeomorph_radialFillingLift]
  change _ = A.ellipticThreeCoverToCanonicalRadialHomeomorph
    (@SMul.smul _ _
      (pullbackMulActionHomeomorph A.ellipticThreeUnitRadialFillingDeckAction
        A.ellipticThreeCoverToCanonicalRadialHomeomorph).toSMul
      (A.ellipticThreeBoundaryDeckData.fillingDeckMap g)
      (A.ellipticThreeRadialFillingLift q))
  rw [pullbackMulActionHomeomorph_apply]
  rw [A.ellipticThreeCoverToCanonicalRadialHomeomorph_radialFillingLift]
  apply Prod.ext
  · apply Subtype.ext
    let P := orderThreeCentralFiberPresentationData A.periods
    let d := A.ellipticThreeToCentralBoundaryDeckEquiv g
    change
      ((angularCover (T := ComplexTwoSpace) 3
          A.starSeparation.orderThree.radius_lt_one.le
          (q.1, q.2.1 - g.right.toAdd,
            affineCyclicBoundaryDeckTransform P d q.2.2)).1.1 : ℂ) /
          (A.starSeparation.orderThree.radius : ℂ) =
        ((affineCyclicFillingDiscRepresentation P
          ((affineCyclicBoundaryDeckData P).fillingDeckMap d)
          ⟨((angularCover (T := ComplexTwoSpace) 3
            A.starSeparation.orderThree.radius_lt_one.le q).1.1 : ℂ) /
              (A.starSeparation.orderThree.radius : ℂ), by
            rw [norm_div, Complex.norm_real,
              Real.norm_of_nonneg A.starSeparation.orderThree.radius_pos.le]
            exact (div_lt_one A.starSeparation.orderThree.radius_pos).mpr
              (angularCover (T := ComplexTwoSpace) 3
                A.starSeparation.orderThree.radius_lt_one.le q).2.2⟩ :
            ComplexUnitDisc) : ℂ)
    rw [affineCyclicFillingDiscRepresentation_apply_eq_pow,
      affineCyclicFillingDegree_fillingDeckMap]
    change _ =
      (((orderThreeDiscRotation ^ ((g.right.toAdd : ZMod 3).val))
        ⟨((angularCover (T := ComplexTwoSpace) 3
          A.starSeparation.orderThree.radius_lt_one.le q).1.1 : ℂ) /
            (A.starSeparation.orderThree.radius : ℂ), by
          rw [norm_div, Complex.norm_real,
            Real.norm_of_nonneg A.starSeparation.orderThree.radius_pos.le]
          exact (div_lt_one A.starSeparation.orderThree.radius_pos).mpr
            (angularCover (T := ComplexTwoSpace) 3
              A.starSeparation.orderThree.radius_lt_one.le q).2.2⟩ :
          ComplexUnitDisc) : ℂ)
    have hrotation : orderThreeDiscRotation =
        ComplexUnitDisc.rotation (standardMultiplier 3) (norm_standardMultiplier 3) := by
      apply Equiv.ext
      intro u
      apply Subtype.ext
      change orderThreeMultiplier * (u : ℂ) = standardMultiplier 3 * (u : ℂ)
      rw [orderThreeMultiplier_eq_standardMultiplier]
    rw [hrotation, ComplexUnitDisc.coe_rotation_pow_apply]
    change (((q.1 : ℝ) : ℂ) *
          ((angleMap 3 (q.2.1 - g.right.toAdd) : Circle) : ℂ)) /
          (A.starSeparation.orderThree.radius : ℂ) =
      standardMultiplier 3 ^ ((g.right.toAdd : ZMod 3).val) *
        ((((q.1 : ℝ) : ℂ) * ((angleMap 3 q.2.1 : Circle) : ℂ)) /
          (A.starSeparation.orderThree.radius : ℂ))
    rw [← standardMultiplier_zmodVal_mul_angleMap]
    ring
  · let P := orderThreeCentralFiberPresentationData A.periods
    let d := A.ellipticThreeToCentralBoundaryDeckEquiv g
    rw [A.orderThreeActualEllipticBoundaryAction_snd]
    change affineCyclicBoundaryDeckTransform P d q.2.2 =
      @SMul.smul _ _ (affineCyclicFillingDeckAction P).toSMul
        (A.ellipticThreeToCanonicalFillingDeckEquiv
          (A.ellipticThreeBoundaryDeckData.fillingDeckMap g)) q.2.2
    rw [A.ellipticThreeToCanonicalFillingDeckEquiv_fillingDeckMap]
    exact (affineCyclicFillingDeckMap_smul P d q.2.2).symm

/-- The actual order-four collar action and the transported filling action agree under the
canonical radial lift. -/
public theorem ellipticFourRadialFillingLift_equivariant
    (g : OrderFourAffineMappingTorusDeck A.periods)
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.ellipticFourBoundaryAction
    letI := A.ellipticFourRadialFillingDeckAction
    A.ellipticFourRadialFillingLift (g • q) =
      A.ellipticFourBoundaryDeckData.fillingDeckMap g •
        A.ellipticFourRadialFillingLift q := by
  let _ := A.ellipticFourBoundaryAction
  let _ := A.ellipticFourRadialFillingDeckAction
  apply A.ellipticFourCoverToCanonicalRadialHomeomorph.injective
  rw [A.ellipticFourCoverToCanonicalRadialHomeomorph_radialFillingLift]
  change _ = A.ellipticFourCoverToCanonicalRadialHomeomorph
    (@SMul.smul _ _
      (pullbackMulActionHomeomorph A.ellipticFourUnitRadialFillingDeckAction
        A.ellipticFourCoverToCanonicalRadialHomeomorph).toSMul
      (A.ellipticFourBoundaryDeckData.fillingDeckMap g)
      (A.ellipticFourRadialFillingLift q))
  rw [pullbackMulActionHomeomorph_apply]
  rw [A.ellipticFourCoverToCanonicalRadialHomeomorph_radialFillingLift]
  apply Prod.ext
  · apply Subtype.ext
    let P := orderFourCentralFiberPresentationData A.periods
    let d := A.ellipticFourToCentralBoundaryDeckEquiv g
    change
      ((angularCover (T := ComplexTwoSpace) 4
          A.starSeparation.orderFour.radius_lt_one.le
          (q.1, q.2.1 - g.right.toAdd,
            affineCyclicBoundaryDeckTransform P d q.2.2)).1.1 : ℂ) /
          (A.starSeparation.orderFour.radius : ℂ) =
        ((affineCyclicFillingDiscRepresentation P
          ((affineCyclicBoundaryDeckData P).fillingDeckMap d)
          ⟨((angularCover (T := ComplexTwoSpace) 4
            A.starSeparation.orderFour.radius_lt_one.le q).1.1 : ℂ) /
              (A.starSeparation.orderFour.radius : ℂ), by
            rw [norm_div, Complex.norm_real,
              Real.norm_of_nonneg A.starSeparation.orderFour.radius_pos.le]
            exact (div_lt_one A.starSeparation.orderFour.radius_pos).mpr
              (angularCover (T := ComplexTwoSpace) 4
                A.starSeparation.orderFour.radius_lt_one.le q).2.2⟩ :
            ComplexUnitDisc) : ℂ)
    rw [affineCyclicFillingDiscRepresentation_apply_eq_pow,
      affineCyclicFillingDegree_fillingDeckMap]
    change _ =
      (((orderFourDiscRotation ^ ((g.right.toAdd : ZMod 4).val))
        ⟨((angularCover (T := ComplexTwoSpace) 4
          A.starSeparation.orderFour.radius_lt_one.le q).1.1 : ℂ) /
            (A.starSeparation.orderFour.radius : ℂ), by
          rw [norm_div, Complex.norm_real,
            Real.norm_of_nonneg A.starSeparation.orderFour.radius_pos.le]
          exact (div_lt_one A.starSeparation.orderFour.radius_pos).mpr
            (angularCover (T := ComplexTwoSpace) 4
              A.starSeparation.orderFour.radius_lt_one.le q).2.2⟩ :
          ComplexUnitDisc) : ℂ)
    have hrotation : orderFourDiscRotation =
        ComplexUnitDisc.rotation (standardMultiplier 4) (norm_standardMultiplier 4) := by
      apply Equiv.ext
      intro u
      apply Subtype.ext
      change orderFourMultiplier * (u : ℂ) = standardMultiplier 4 * (u : ℂ)
      rw [orderFourMultiplier_eq_standardMultiplier]
    rw [hrotation, ComplexUnitDisc.coe_rotation_pow_apply]
    change (((q.1 : ℝ) : ℂ) *
          ((angleMap 4 (q.2.1 - g.right.toAdd) : Circle) : ℂ)) /
          (A.starSeparation.orderFour.radius : ℂ) =
      standardMultiplier 4 ^ ((g.right.toAdd : ZMod 4).val) *
        ((((q.1 : ℝ) : ℂ) * ((angleMap 4 q.2.1 : Circle) : ℂ)) /
          (A.starSeparation.orderFour.radius : ℂ))
    rw [← standardMultiplier_zmodVal_mul_angleMap]
    ring
  · let P := orderFourCentralFiberPresentationData A.periods
    let d := A.ellipticFourToCentralBoundaryDeckEquiv g
    rw [A.orderFourActualEllipticBoundaryAction_snd]
    change affineCyclicBoundaryDeckTransform P d q.2.2 =
      @SMul.smul _ _ (affineCyclicFillingDeckAction P).toSMul
        (A.ellipticFourToCanonicalFillingDeckEquiv
          (A.ellipticFourBoundaryDeckData.fillingDeckMap g)) q.2.2
    rw [A.ellipticFourToCanonicalFillingDeckEquiv_fillingDeckMap]
    exact (affineCyclicFillingDeckMap_smul P d q.2.2).symm

/-- The explicit transported action supplies the order-three filling quotient data. -/
public noncomputable def ellipticThreeFillingQuotientData :
    A.OrderThreeActualEllipticFillingQuotientData where
  fillingAction := A.ellipticThreeRadialFillingDeckAction
  fillingQuotient := A.ellipticThreeFillingProjection_isQuotientCoveringMap

/-- The canonical order-three lift has the prescribed deck marking, in fact at every point of
the collar cover. -/
public noncomputable def ellipticThreeFillingMarkedDeckData :
    A.OrderThreeActualEllipticFillingMarkedDeckData where
  toOrderThreeActualEllipticFillingQuotientData :=
    A.ellipticThreeFillingQuotientData
  equivariant_at_boundaryBase := fun g ↦
    A.ellipticThreeRadialFillingLift_equivariant g
      A.ellipticThreeBoundaryBase

/-- The explicit order-four radial lift and transported action give the complete marked-base
filling extension. -/
public noncomputable def ellipticFourFillingExtensionAtBase :
    A.OrderFourActualEllipticFillingExtensionAtBase where
  fillingAction := A.ellipticFourRadialFillingDeckAction
  fillingQuotient := A.ellipticFourFillingProjection_isQuotientCoveringMap
  lift := A.ellipticFourRadialFillingLift
  commutes := A.ellipticFourRadialFillingLift_commutes
  equivariant_at_boundaryBase := fun g ↦
    A.ellipticFourRadialFillingLift_equivariant g
      A.ellipticFourBoundaryBase

end SphereSixComplex.Geometry.PaperAnalyticData
