module

public import SphereSixComplex.Topology.PaperActualEllipticRadialFillingDeckAction

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
open SphereSixComplex.Topology.PaperMultipleFiberHOneTopology.EstablishedAffineCyclicQuotientHomology

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
public theorem orderThreeActualCoverToCanonicalRadialHomeomorph_radialFillingLift
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    A.orderThreeActualCoverToCanonicalRadialHomeomorph
        (A.orderThreeActualEllipticRadialFillingLift q) =
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
public theorem orderFourActualCoverToCanonicalRadialHomeomorph_radialFillingLift
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    A.orderFourActualCoverToCanonicalRadialHomeomorph
        (A.orderFourActualEllipticRadialFillingLift q) =
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
    letI := A.orderThreeActualEllipticBoundaryAction
    (g • q).2.2 =
      affineCyclicBoundaryDeckTransform (orderThreeCentralFiberPresentationData A.periods)
        (A.orderThreeActualToCentralBoundaryDeckEquiv g) q.2.2 := by
  let _ := A.orderThreeActualEllipticBoundaryAction
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
    letI := A.orderFourActualEllipticBoundaryAction
    (g • q).2.2 =
      affineCyclicBoundaryDeckTransform (orderFourCentralFiberPresentationData A.periods)
        (A.orderFourActualToCentralBoundaryDeckEquiv g) q.2.2 := by
  let _ := A.orderFourActualEllipticBoundaryAction
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
public theorem orderThreeActualEllipticRadialFillingLift_equivariant
    (g : OrderThreeAffineMappingTorusDeck A.periods)
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderThreeActualEllipticBoundaryAction
    letI := A.orderThreeActualRadialFillingDeckAction
    A.orderThreeActualEllipticRadialFillingLift (g • q) =
      A.orderThreeActualEllipticBoundaryDeckData.fillingDeckMap g •
        A.orderThreeActualEllipticRadialFillingLift q := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  let _ := A.orderThreeActualRadialFillingDeckAction
  apply A.orderThreeActualCoverToCanonicalRadialHomeomorph.injective
  rw [A.orderThreeActualCoverToCanonicalRadialHomeomorph_radialFillingLift]
  change _ = A.orderThreeActualCoverToCanonicalRadialHomeomorph
    (@SMul.smul _ _
      (pullbackMulActionHomeomorph A.orderThreeActualUnitRadialFillingDeckAction
        A.orderThreeActualCoverToCanonicalRadialHomeomorph).toSMul
      (A.orderThreeActualEllipticBoundaryDeckData.fillingDeckMap g)
      (A.orderThreeActualEllipticRadialFillingLift q))
  rw [pullbackMulActionHomeomorph_apply]
  rw [A.orderThreeActualCoverToCanonicalRadialHomeomorph_radialFillingLift]
  apply Prod.ext
  · apply Subtype.ext
    let P := orderThreeCentralFiberPresentationData A.periods
    let d := A.orderThreeActualToCentralBoundaryDeckEquiv g
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
        discScalarEquiv (standardMultiplier 3) (norm_standardMultiplier 3) := by
      apply Equiv.ext
      intro u
      apply Subtype.ext
      change orderThreeMultiplier * (u : ℂ) = standardMultiplier 3 * (u : ℂ)
      rw [orderThreeMultiplier_eq_standardMultiplier]
    rw [hrotation, discScalarEquiv_pow_apply_val]
    change (((q.1 : ℝ) : ℂ) *
          ((angleMap 3 (q.2.1 - g.right.toAdd) : Circle) : ℂ)) /
          (A.starSeparation.orderThree.radius : ℂ) =
      standardMultiplier 3 ^ ((g.right.toAdd : ZMod 3).val) *
        ((((q.1 : ℝ) : ℂ) * ((angleMap 3 q.2.1 : Circle) : ℂ)) /
          (A.starSeparation.orderThree.radius : ℂ))
    rw [← standardMultiplier_zmodVal_mul_angleMap]
    ring
  · let P := orderThreeCentralFiberPresentationData A.periods
    let d := A.orderThreeActualToCentralBoundaryDeckEquiv g
    rw [A.orderThreeActualEllipticBoundaryAction_snd]
    change affineCyclicBoundaryDeckTransform P d q.2.2 =
      @SMul.smul _ _ (affineCyclicFillingDeckAction P).toSMul
        (A.orderThreeActualToCanonicalFillingDeckEquiv
          (A.orderThreeActualEllipticBoundaryDeckData.fillingDeckMap g)) q.2.2
    rw [A.orderThreeActualToCanonicalFillingDeckEquiv_fillingDeckMap]
    exact (affineCyclicFillingDeckMap_smul P d q.2.2).symm

/-- The actual order-four collar action and the transported filling action agree under the
canonical radial lift. -/
public theorem orderFourActualEllipticRadialFillingLift_equivariant
    (g : OrderFourAffineMappingTorusDeck A.periods)
    (q : OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace)) :
    letI := A.orderFourActualEllipticBoundaryAction
    letI := A.orderFourActualRadialFillingDeckAction
    A.orderFourActualEllipticRadialFillingLift (g • q) =
      A.orderFourActualEllipticBoundaryDeckData.fillingDeckMap g •
        A.orderFourActualEllipticRadialFillingLift q := by
  let _ := A.orderFourActualEllipticBoundaryAction
  let _ := A.orderFourActualRadialFillingDeckAction
  apply A.orderFourActualCoverToCanonicalRadialHomeomorph.injective
  rw [A.orderFourActualCoverToCanonicalRadialHomeomorph_radialFillingLift]
  change _ = A.orderFourActualCoverToCanonicalRadialHomeomorph
    (@SMul.smul _ _
      (pullbackMulActionHomeomorph A.orderFourActualUnitRadialFillingDeckAction
        A.orderFourActualCoverToCanonicalRadialHomeomorph).toSMul
      (A.orderFourActualEllipticBoundaryDeckData.fillingDeckMap g)
      (A.orderFourActualEllipticRadialFillingLift q))
  rw [pullbackMulActionHomeomorph_apply]
  rw [A.orderFourActualCoverToCanonicalRadialHomeomorph_radialFillingLift]
  apply Prod.ext
  · apply Subtype.ext
    let P := orderFourCentralFiberPresentationData A.periods
    let d := A.orderFourActualToCentralBoundaryDeckEquiv g
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
        discScalarEquiv (standardMultiplier 4) (norm_standardMultiplier 4) := by
      apply Equiv.ext
      intro u
      apply Subtype.ext
      change orderFourMultiplier * (u : ℂ) = standardMultiplier 4 * (u : ℂ)
      rw [orderFourMultiplier_eq_standardMultiplier]
    rw [hrotation, discScalarEquiv_pow_apply_val]
    change (((q.1 : ℝ) : ℂ) *
          ((angleMap 4 (q.2.1 - g.right.toAdd) : Circle) : ℂ)) /
          (A.starSeparation.orderFour.radius : ℂ) =
      standardMultiplier 4 ^ ((g.right.toAdd : ZMod 4).val) *
        ((((q.1 : ℝ) : ℂ) * ((angleMap 4 q.2.1 : Circle) : ℂ)) /
          (A.starSeparation.orderFour.radius : ℂ))
    rw [← standardMultiplier_zmodVal_mul_angleMap]
    ring
  · let P := orderFourCentralFiberPresentationData A.periods
    let d := A.orderFourActualToCentralBoundaryDeckEquiv g
    rw [A.orderFourActualEllipticBoundaryAction_snd]
    change affineCyclicBoundaryDeckTransform P d q.2.2 =
      @SMul.smul _ _ (affineCyclicFillingDeckAction P).toSMul
        (A.orderFourActualToCanonicalFillingDeckEquiv
          (A.orderFourActualEllipticBoundaryDeckData.fillingDeckMap g)) q.2.2
    rw [A.orderFourActualToCanonicalFillingDeckEquiv_fillingDeckMap]
    exact (affineCyclicFillingDeckMap_smul P d q.2.2).symm

/-- The explicit transported action supplies the order-three filling quotient data. -/
public noncomputable def orderThreeActualEllipticFillingQuotientData :
    A.OrderThreeActualEllipticFillingQuotientData where
  fillingAction := A.orderThreeActualRadialFillingDeckAction
  fillingQuotient := A.orderThreeActualEllipticFillingProjection_isQuotientCoveringMap

/-- The canonical order-three lift has the prescribed deck marking, in fact at every point of
the collar cover. -/
public noncomputable def orderThreeActualEllipticFillingMarkedDeckData :
    A.OrderThreeActualEllipticFillingMarkedDeckData where
  toOrderThreeActualEllipticFillingQuotientData :=
    A.orderThreeActualEllipticFillingQuotientData
  equivariant_at_boundaryBase := fun g ↦
    A.orderThreeActualEllipticRadialFillingLift_equivariant g
      A.orderThreeActualEllipticBoundaryBase

/-- The explicit order-four radial lift and transported action give the complete marked-base
filling extension. -/
public noncomputable def orderFourActualEllipticFillingExtensionAtBase :
    A.OrderFourActualEllipticFillingExtensionAtBase where
  fillingAction := A.orderFourActualRadialFillingDeckAction
  fillingQuotient := A.orderFourActualEllipticFillingProjection_isQuotientCoveringMap
  lift := A.orderFourActualEllipticRadialFillingLift
  commutes := A.orderFourActualEllipticRadialFillingLift_commutes
  equivariant_at_boundaryBase := fun g ↦
    A.orderFourActualEllipticRadialFillingLift_equivariant g
      A.orderFourActualEllipticBoundaryBase

end SphereSixComplex.Geometry.PaperAnalyticData
