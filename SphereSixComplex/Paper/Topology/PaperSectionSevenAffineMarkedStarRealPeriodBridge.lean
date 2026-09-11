module

public import SphereSixComplex.Paper.Topology.PaperSectionSevenAffineRealPeriodTransport

/-!
# Finite-orbit invariance of the marked elliptic real-period coordinate

The fixed real-period product charts intertwine the affine collar actions with the diagonal
finite cyclic actions.  Consequently, equality in an affine collar quotient implies equality
after the reduced central-fibre projection.  This is the representative-independence needed by
the marked Section Seven endpoint calculation.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Geometry

namespace EllipticActionData

variable {m : ℕ} [NeZero m] {Base Torus : Type*} [AddCommGroup Torus]
    (D : EllipticActionData m Base Torus)

public theorem representation_snd (g : FiniteCyclic m) (p : Base × Torus) :
    (D.representation g p).2 =
      (D.fiberGenerator ^ (Multiplicative.toAdd g).val) p.2 := by
  conv_lhs => rw [cyclic_eq_generator_pow g]
  rw [map_pow, D.representation_generator, D.diagonalGenerator_pow_apply]

public theorem representation_center_fst (g : FiniteCyclic m) (x : Torus) :
    (D.representation g (D.center, x)).1 = D.center := by
  conv_lhs => rw [cyclic_eq_generator_pow g]
  rw [map_pow, D.representation_generator, D.diagonalGenerator_pow_apply]
  by_cases hk : (Multiplicative.toAdd g).val = 0
  · simp [hk]
  · exact (D.rotation_fixed_iff _ (Nat.pos_of_ne_zero hk)
      (ZMod.val_lt _) D.center).mpr rfl

end EllipticActionData

namespace PaperAnalyticData

open TorusFamily AnalyticTorusFamily
open EllipticFixedPointCriterion EllipticVaryingFamilyQuotient
open EquivariantQuotientHomeomorph EllipticRealPeriodProductTrivialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

public theorem orderThreeRealPeriodCentralProjection_action
    (A : PaperAnalyticData) (g : FiniteCyclic 3)
    (q : TotalSpace (parameterMap A.periods)) :
    RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)).symm
            (orderThreeRealPeriodProductHomeomorph A.periods
              (actionMap (orderThreeAffineFamilyAction A.periods) g q)).2) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)).symm
            (orderThreeRealPeriodProductHomeomorph A.periods q).2) := by
  let D := orderThreeRadialActionData A.periods
  let E := EllipticFixedPointCriterion.orderThreeActionData A.periods
  have he := orderThreeRealPeriodProductHomeomorph_equivariant A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction g q
  apply Subtype.ext
  apply Quotient.sound
  refine ⟨g, ?_⟩
  change D.actionData.representation g
      (D.actionData.center, (orderThreeRealPeriodProductHomeomorph A.periods q).2) =
    (D.actionData.center,
      (orderThreeRealPeriodProductHomeomorph A.periods
        (actionMap (orderThreeAffineFamilyAction A.periods) g q)).2)
  apply Prod.ext
  · exact D.actionData.representation_center_fst g _
  · have hs := congrArg Prod.snd he
    calc
      (D.actionData.representation g
        (D.actionData.center, (orderThreeRealPeriodProductHomeomorph A.periods q).2)).2 =
          (D.actionData.fiberGenerator ^ (Multiplicative.toAdd g).val)
            (orderThreeRealPeriodProductHomeomorph A.periods q).2 :=
        D.actionData.representation_snd g _
      _ = (E.representation g
            (orderThreeRealPeriodProductHomeomorph A.periods q)).2 :=
        (E.representation_snd g _).symm
      _ = _ := hs.symm

public theorem orderFourRealPeriodCentralProjection_action
    (A : PaperAnalyticData) (g : FiniteCyclic 4)
    (q : TotalSpace (parameterMap A.periods)) :
    RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData A.periods)).symm
            (orderFourRealPeriodProductHomeomorph A.periods
              (actionMap (orderFourAffineFamilyAction A.periods) g q)).2) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData A.periods)).symm
            (orderFourRealPeriodProductHomeomorph A.periods q).2) := by
  let D := orderFourRadialActionData A.periods
  let E := EllipticFixedPointCriterion.orderFourActionData A.periods
  have he := orderFourRealPeriodProductHomeomorph_equivariant A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction g q
  apply Subtype.ext
  apply Quotient.sound
  refine ⟨g, ?_⟩
  change D.actionData.representation g
      (D.actionData.center, (orderFourRealPeriodProductHomeomorph A.periods q).2) =
    (D.actionData.center,
      (orderFourRealPeriodProductHomeomorph A.periods
        (actionMap (orderFourAffineFamilyAction A.periods) g q)).2)
  apply Prod.ext
  · exact D.actionData.representation_center_fst g _
  · have hs := congrArg Prod.snd he
    calc
      (D.actionData.representation g
        (D.actionData.center, (orderFourRealPeriodProductHomeomorph A.periods q).2)).2 =
          (D.actionData.fiberGenerator ^ (Multiplicative.toAdd g).val)
            (orderFourRealPeriodProductHomeomorph A.periods q).2 :=
        D.actionData.representation_snd g _
      _ = (E.representation g
            (orderFourRealPeriodProductHomeomorph A.periods q)).2 :=
        (E.representation_snd g _).symm
      _ = _ := hs.symm

public theorem orderThreeRealPeriodCentralProjection_eq_of_quotient_mk_eq
    (A : PaperAnalyticData) (q q' : TotalSpace (parameterMap A.periods))
    (h : (Quotient.mk _ q :
        Quotient (orbitRelOf (orderThreeAffineFamilyAction A.periods))) =
      Quotient.mk _ q') :
    RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)).symm
            (orderThreeRealPeriodProductHomeomorph A.periods q).2) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderThreeRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderThreeRadialActionData A.periods)).symm
            (orderThreeRealPeriodProductHomeomorph A.periods q').2) := by
  let _ := orderThreeAffineFamilyAction A.periods
  rw [Quotient.eq] at h
  change MulAction.orbitRel (FiniteCyclic 3) _ q q' at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  rw [← hg]
  exact A.orderThreeRealPeriodCentralProjection_action g q'

public theorem orderFourRealPeriodCentralProjection_eq_of_quotient_mk_eq
    (A : PaperAnalyticData) (q q' : TotalSpace (parameterMap A.periods))
    (h : (Quotient.mk _ q :
        Quotient (orbitRelOf (orderFourAffineFamilyAction A.periods))) =
      Quotient.mk _ q') :
    RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData A.periods)).symm
            (orderFourRealPeriodProductHomeomorph A.periods q).2) =
      RadialEllipticActionData.centralFiberCoverProjection
        (orderFourRadialActionData A.periods)
        ((RadialEllipticActionData.centralFiberCoverSourceHomeomorph
          (orderFourRadialActionData A.periods)).symm
            (orderFourRealPeriodProductHomeomorph A.periods q').2) := by
  let _ := orderFourAffineFamilyAction A.periods
  rw [Quotient.eq] at h
  change MulAction.orbitRel (FiniteCyclic 4) _ q q' at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨g, hg⟩ := h
  rw [← hg]
  exact A.orderFourRealPeriodCentralProjection_action g q'

end PaperAnalyticData

end SphereSixComplex.Geometry

open scoped ContinuousMap

namespace SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

open SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction

variable {m : ℕ} [NeZero m] {p : SphereSixComplex.Periods.Parameters}
  {D : RadialEllipticActionData m (AdditiveTorus p)}
  {X : Type*} [TopologicalSpace X]





/-- A translation depending through a contractible parameter space is nullhomotopic before
composition with any continuous map out of the period torus. -/
public theorem continuousMap_comp_add_homotopic_of_contractible
    {B Y : Type*} [TopologicalSpace B] [ContractibleSpace B] [TopologicalSpace Y]
    (k : C(AdditiveTorus p, Y)) (f : C(X, AdditiveTorus p))
    (b : C(X, B)) (g : C(B, AdditiveTorus p)) :
    (k.comp f).Homotopic
      (k.comp
        ⟨fun x ↦ g (b x) + f x,
          continuous_add.comp
            ((g.continuous.comp b.continuous).prodMk f.continuous)⟩) := by
  have hnull : (g.comp b).Nullhomotopic :=
    ((id_nullhomotopic B).comp_right g).comp_left b
  obtain ⟨y, hy⟩ := hnull
  let _ : PathConnectedSpace (AdditiveTorus p) :=
    Function.Surjective.pathConnectedSpace (f := torusProjection p)
      Quotient.mk_surjective continuous_quot_mk
  have hy0 : (ContinuousMap.const X y).Homotopic
      (ContinuousMap.const X (0 : AdditiveTorus p)) :=
    ⟨(PathConnectedSpace.joined y 0).some.toHomotopyConst⟩
  obtain ⟨H⟩ := (hy.trans hy0).symm
  exact ⟨{
    toFun := fun tx ↦ k (H tx + f tx.2)
    continuous_toFun := k.continuous.comp
      (continuous_add.comp
        (H.continuous.prodMk (f.continuous.comp continuous_snd)))
    map_zero_left := by
      intro x
      change k (H (0, x) + f x) = k (f x)
      have hH : H (0, x) = (0 : AdditiveTorus p) := H.map_zero_left x
      rw [hH, zero_add]
    map_one_left := by
      intro x
      change k (H (1, x) + f x) = k (g (b x) + f x)
      have hH : H (1, x) = g (b x) := H.map_one_left x
      rw [hH] }⟩

end SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

namespace SphereSixComplex.Geometry.PaperAnalyticData

open AnalyticTorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Topology.PaperEllipticFillingRadialRetraction
open SphereSixComplex.Topology.PaperEllipticFillingRealPeriodRadial
open SphereSixComplex.Topology.PaperEllipticReducedCentralFiberCoverModels

/-- The strip coordinate of the marked affine band. -/
public noncomputable def affineBandStripCoordinate (A : PaperAnalyticData) :
    C(A.affineMarkedBand, affineVerticalStrip) :=
  ⟨fun x ↦
      (A.affineCentralBandMarkedProductHomeomorph
        A.affineCentralSeparation
          (A.actualAffineHeightSplit.sidesIntersectionHomeomorph x)).1,
    continuous_fst.comp
      ((A.affineCentralBandMarkedProductHomeomorph
        A.affineCentralSeparation).continuous.comp
          A.actualAffineHeightSplit.sidesIntersectionHomeomorph.continuous)⟩

/-- Translate the marked order-three torus coordinate by a gauge depending on the strip
coordinate, then pass to the reduced central fibre. -/
public noncomputable def affineOrderThreeGaugeTranslatedProjection
    (A : PaperAnalyticData)
    (g : C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.affineMarkedBand, orderThreeReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.affineBandStripCoordinate x) +
          affineBandFiberCoordinate A x,
        continuous_add.comp
          ((g.continuous.comp A.affineBandStripCoordinate.continuous).prodMk
            (affineBandFiberCoordinate A).continuous)⟩

/-- Translate the marked order-four torus coordinate by a gauge depending on the strip
coordinate, then pass to the reduced central fibre. -/
public noncomputable def affineOrderFourGaugeTranslatedProjection
    (A : PaperAnalyticData)
    (g : C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.affineMarkedBand, orderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.affineBandStripCoordinate x) +
          affineBandFiberCoordinate A x,
        continuous_add.comp
          ((g.continuous.comp A.affineBandStripCoordinate.continuous).prodMk
            (affineBandFiberCoordinate A).continuous)⟩

/-- The honest point-set residue of the logarithmic-gauge calculation.  It says that, in fixed
real-period coordinates, each selected-filling endpoint differs from the marked band coordinate
by a torus translation depending only on the strip coordinate. -/
public structure AffineMarkedEndpointGaugeTranslation
    (A : PaperAnalyticData) where
  orderThreeGauge :
    C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderThreeFormula :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderThreeStarEndpoint =
      A.affineOrderThreeGaugeTranslatedProjection orderThreeGauge
  orderFourGauge :
    C(affineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderFourFormula :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderFourStarEndpoint =
      A.affineOrderFourGaugeTranslatedProjection orderFourGauge

/-- The endpoint-level homotopy statement left after removing the logarithmic gauge. -/
public structure AffineMarkedDiscEndpointHomotopyCompatibility
    (A : PaperAnalyticData) where
  orderThree :
    ((A.orderThreeFillingImageHomotopyEquiv.toFun.comp
      A.affineOrderThreeDiscFillingEndpoint)).Homotopic
        (affineBandOrderThreeMarkedProjection A)
  orderFour :
    ((A.orderFourFillingImageHomotopyEquiv.toFun.comp
      A.affineOrderFourDiscFillingEndpoint)).Homotopic
        (affineBandOrderFourMarkedProjection A)

/-- Homotopic disc endpoints suffice for the original marked-band compatibility; literal
endpoint equality is unnecessary. -/
public theorem AffineMarkedDiscEndpointHomotopyCompatibility.toBandCompatibility
    {A : PaperAnalyticData}
    (H : A.AffineMarkedDiscEndpointHomotopyCompatibility) :
    A.AffineOverlapBandCompatibility := by
  apply markedBandHomotopies_of_sideContractions A
  refine { orderThree := ?_, orderFour := ?_ }
  · let q := A.affineOrderThreeDiscFillingEndpoint
    let g := A.orderThreeFillingImageHomotopyEquiv
    let p := affineBandOrderThreeMarkedProjection A
    have hleft : (g.invFun.comp (g.toFun.comp q)).Homotopic q := by
      simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
        ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hright : (g.invFun.comp (g.toFun.comp q)).Homotopic
        (g.invFun.comp p) :=
      ContinuousMap.Homotopic.comp (.refl g.invFun) H.orderThree
    have hfill : q.Homotopic (g.invFun.comp p) := hleft.symm.trans hright
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.affineOrderThreeFillingImageToSide) hfill
    have hendpoint :
        A.affineOrderThreeFillingImageToSide.comp (g.invFun.comp p) =
          (affineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.affineOrderThreeFillingImageToSide.comp
              (A.orderThreeFillingImageHomotopyEquiv.invFun.comp
                (affineBandOrderThreeMarkedProjection A)) =
            (orderThreeOverlapIsHomotopyEquivalence_inclusion
                A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.actualAffineHeightSplit.allocation.orderThreeSide
                A.orderThreeFillingImage
                A.actualAffineHeightSplit.orderThreeFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.orderThreeFillingImageHomotopyEquiv.invFun.comp
                    (affineBandOrderThreeMarkedProjection A))) := by
        rw [(orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv_invFun]
        ext x
        rfl
      exact hraw.trans (affineOrderThreeSideInverse_markedProjection A).symm
    rw [hendpoint] at hside
    exact A.orderThreeBandInclusion_homotopic_discFillingEndpoint.trans hside
  · let q := A.affineOrderFourDiscFillingEndpoint
    let g := A.orderFourFillingImageHomotopyEquiv
    let p := affineBandOrderFourMarkedProjection A
    have hleft : (g.invFun.comp (g.toFun.comp q)).Homotopic q := by
      simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
        ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hright : (g.invFun.comp (g.toFun.comp q)).Homotopic
        (g.invFun.comp p) :=
      ContinuousMap.Homotopic.comp (.refl g.invFun) H.orderFour
    have hfill : q.Homotopic (g.invFun.comp p) := hleft.symm.trans hright
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.affineOrderFourFillingImageToSide) hfill
    have hendpoint :
        A.affineOrderFourFillingImageToSide.comp (g.invFun.comp p) =
          (affineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.affineOrderFourFillingImageToSide.comp
              (A.orderFourFillingImageHomotopyEquiv.invFun.comp
                (affineBandOrderFourMarkedProjection A)) =
            (orderFourOverlapIsHomotopyEquivalence_inclusion
                A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.actualAffineHeightSplit.allocation.orderFourSide
                A.orderFourFillingImage
                A.actualAffineHeightSplit.orderFourFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.orderFourFillingImageHomotopyEquiv.invFun.comp
                    (affineBandOrderFourMarkedProjection A))) := by
        rw [(orderFourOverlapIsHomotopyEquivalence_inclusion
          A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv_invFun]
        ext x
        rfl
      exact hraw.trans (affineOrderFourSideInverse_markedProjection A).symm
    rw [hendpoint] at hside
    exact A.orderFourBandInclusion_homotopic_discFillingEndpoint.trans hside

/-- Reading the order-three disc endpoint in the filling retraction is exactly the same map as
reading its selected star endpoint. -/
public theorem affineOrderThreeDiscEndpoint_toFun_eq_starEndpoint
    (A : PaperAnalyticData) :
    A.orderThreeFillingImageHomotopyEquiv.toFun.comp
        A.affineOrderThreeDiscFillingEndpoint =
      (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderThreeStarEndpoint := by
  apply ContinuousMap.ext
  intro x
  let u := A.affineOrderThreeDiscOverlapEndpoint x
  have hfill : A.affineOrderThreeDiscFillingEndpoint x =
      ⟨u.1, u.2.1⟩ := rfl
  change (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.orderThreePieceHomeomorph.symm
        (A.orderThreeFillingImageToPiece
          (A.affineOrderThreeDiscFillingEndpoint x))) =
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u))
  rw [hfill]
  exact congrArg (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
    (A.orderThreeFillingImageToPiece_symm_overlap u)

/-- Reading the order-four disc endpoint in the filling retraction is exactly the same map as
reading its selected star endpoint. -/
public theorem affineOrderFourDiscEndpoint_toFun_eq_starEndpoint
    (A : PaperAnalyticData) :
    A.orderFourFillingImageHomotopyEquiv.toFun.comp
        A.affineOrderFourDiscFillingEndpoint =
      (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderFourStarEndpoint := by
  apply ContinuousMap.ext
  intro x
  let u := A.affineOrderFourDiscOverlapEndpoint x
  have hfill : A.affineOrderFourDiscFillingEndpoint x =
      ⟨u.1, u.2.1⟩ := rfl
  change (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.orderFourPieceHomeomorph.symm
        (A.orderFourFillingImageToPiece
          (A.affineOrderFourDiscFillingEndpoint x))) =
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u))
  rw [hfill]
  exact congrArg (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
    (A.orderFourFillingImageToPiece_symm_overlap u)

/-- A base-dependent gauge translation gives the order-three selected-filling endpoint
homotopy. -/
public theorem AffineMarkedEndpointGaugeTranslation.orderThreeEndpointHomotopy
    {A : PaperAnalyticData} (G : A.AffineMarkedEndpointGaugeTranslation) :
    ((orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderThreeStarEndpoint).Homotopic
        (affineBandOrderThreeMarkedProjection A) := by
  let _ : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  rw [G.orderThreeFormula]
  change (A.affineOrderThreeGaugeTranslatedProjection
    G.orderThreeGauge).Homotopic _
  unfold affineOrderThreeGaugeTranslatedProjection
  exact (continuousMap_comp_add_homotopic_of_contractible
    ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
          A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩)
    (affineBandFiberCoordinate A)
    A.affineBandStripCoordinate G.orderThreeGauge).symm

/-- A base-dependent gauge translation gives the order-four selected-filling endpoint
homotopy. -/
public theorem AffineMarkedEndpointGaugeTranslation.orderFourEndpointHomotopy
    {A : PaperAnalyticData} (G : A.AffineMarkedEndpointGaugeTranslation) :
    ((orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.affineOrderFourStarEndpoint).Homotopic
        (affineBandOrderFourMarkedProjection A) := by
  let _ : ContractibleSpace affineVerticalStrip :=
    affineVerticalStrip_contractibleSpace
  rw [G.orderFourFormula]
  change (A.affineOrderFourGaugeTranslatedProjection
    G.orderFourGauge).Homotopic _
  unfold affineOrderFourGaugeTranslatedProjection
  exact (continuousMap_comp_add_homotopic_of_contractible
    ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
          A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩)
    (affineBandFiberCoordinate A)
    A.affineBandStripCoordinate G.orderFourGauge).symm

/-- The base-dependent logarithmic-gauge formula implies the original Section Seven marked-band
compatibility. -/
public theorem AffineMarkedEndpointGaugeTranslation.toBandCompatibility
    {A : PaperAnalyticData} (G : A.AffineMarkedEndpointGaugeTranslation) :
    A.AffineOverlapBandCompatibility := by
  apply AffineMarkedDiscEndpointHomotopyCompatibility.toBandCompatibility
  refine { orderThree := ?_, orderFour := ?_ }
  · rw [affineOrderThreeDiscEndpoint_toFun_eq_starEndpoint]
    exact G.orderThreeEndpointHomotopy
  · rw [affineOrderFourDiscEndpoint_toFun_eq_starEndpoint]
    exact G.orderFourEndpointHomotopy

end SphereSixComplex.Geometry.PaperAnalyticData

end
