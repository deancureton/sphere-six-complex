module

public import SphereSixComplex.Topology.PaperSectionSevenAffineRealPeriodTransport
public import SphereSixComplex.Geometry.AdditiveTorusTopology

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

/-- The reduced central-fibre projection, with its canonical period torus used as source. -/
public def reducedCentralFiberTorusProjection :
    C(AdditiveTorus p, D.reducedCentralFiber) :=
  (RadialEllipticActionData.centralFiberCoverProjection D).comp
    ⟨(RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm,
      (RadialEllipticActionData.centralFiberCoverSourceHomeomorph D).symm.continuous⟩

/-- Adding a continuously varying vector before projecting to a period torus changes the
reduced-central-fibre map only by the straight-line homotopy of that vector. -/
public def reducedCentralFiberTorusProjection_addHomotopy
    (f : C(X, AdditiveTorus p)) (v : C(X, ComplexTwoSpace)) :
    ContinuousMap.Homotopy
      ((reducedCentralFiberTorusProjection (D := D)).comp f)
      ((reducedCentralFiberTorusProjection (D := D)).comp
        ⟨fun x ↦ torusProjection p (v x) + f x,
          by
            have hv : Continuous (fun x ↦
                (torusProjection p (v x) : AdditiveTorus p)) :=
              (continuous_quot_mk : Continuous (torusProjection p)).comp v.continuous
            exact continuous_add.comp (hv.prodMk f.continuous)⟩) where
  toFun tx := reducedCentralFiberTorusProjection (D := D)
    (torusProjection p ((tx.1 : ℝ) • v tx.2) + f tx.2)
  continuous_toFun := by
    apply (reducedCentralFiberTorusProjection (D := D)).continuous.comp
    have hv : Continuous (fun tx : unitInterval × X ↦
        (torusProjection p ((tx.1 : ℝ) • v tx.2) : AdditiveTorus p)) :=
      (continuous_quot_mk : Continuous (torusProjection p)).comp
        ((continuous_subtype_val.comp continuous_fst).smul
          (v.continuous.comp continuous_snd))
    exact continuous_add.comp
      (hv.prodMk (f.continuous.comp continuous_snd))
  map_zero_left x := by
    change (reducedCentralFiberTorusProjection (D := D))
        (torusProjection p ((0 : ℝ) • v x) + f x) =
      (reducedCentralFiberTorusProjection (D := D)) (f x)
    rw [zero_smul]
    have hz : torusProjection p (0 : ComplexTwoSpace) =
        (0 : AdditiveTorus p) := additiveTorus_mk_zero p
    rw [hz, zero_add]
  map_one_left x := by
    change (reducedCentralFiberTorusProjection (D := D))
        (torusProjection p ((1 : ℝ) • v x) + f x) =
      (reducedCentralFiberTorusProjection (D := D))
        (torusProjection p (v x) + f x)
    rw [one_smul]

/-- A nullhomotopic torus-valued translation does not change the reduced-central-fibre map up
to homotopy. -/
public theorem reducedCentralFiberTorusProjection_add_homotopic
    (f g : C(X, AdditiveTorus p))
    (hg : g.Homotopic (ContinuousMap.const X 0)) :
    ((reducedCentralFiberTorusProjection (D := D)).comp f).Homotopic
      ((reducedCentralFiberTorusProjection (D := D)).comp
        ⟨fun x ↦ g x + f x,
          by
            exact continuous_add.comp
              (g.continuous.prodMk f.continuous)⟩) := by
  obtain ⟨H⟩ := hg.symm
  refine ⟨{
    toFun := fun tx ↦ (reducedCentralFiberTorusProjection (D := D))
      (H tx + f tx.2)
    continuous_toFun := (reducedCentralFiberTorusProjection (D := D)).continuous.comp
      (continuous_add.comp
        (H.continuous.prodMk (f.continuous.comp continuous_snd)))
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro x
    change (reducedCentralFiberTorusProjection (D := D))
        (H (0, x) + f x) =
      (reducedCentralFiberTorusProjection (D := D)) (f x)
    have hH : H (0, x) = (0 : AdditiveTorus p) := H.map_zero_left x
    rw [hH]
    change (reducedCentralFiberTorusProjection (D := D)) (0 + f x) =
      (reducedCentralFiberTorusProjection (D := D)) (f x)
    rw [zero_add]
  · intro x
    change (reducedCentralFiberTorusProjection (D := D))
        (H (1, x) + f x) =
      (reducedCentralFiberTorusProjection (D := D)) (g x + f x)
    have hH : H (1, x) = g x := H.map_one_left x
    rw [hH]

/-- A torus translation depending through a contractible parameter space is nullhomotopic and
hence invisible up to homotopy after the reduced central projection. -/
public theorem reducedCentralFiberTorusProjection_add_homotopic_of_contractible
    {B : Type*} [TopologicalSpace B] [ContractibleSpace B]
    (f : C(X, AdditiveTorus p)) (b : C(X, B)) (g : C(B, AdditiveTorus p)) :
    ((reducedCentralFiberTorusProjection (D := D)).comp f).Homotopic
      ((reducedCentralFiberTorusProjection (D := D)).comp
        ⟨fun x ↦ g (b x) + f x,
          by
            exact continuous_add.comp
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
  exact reducedCentralFiberTorusProjection_add_homotopic f (g.comp b)
    (hy.trans hy0)

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
public noncomputable def sectionSevenAffineBandStripCoordinate (A : PaperAnalyticData) :
    C(A.SectionSevenAffineMarkedBand, sectionSevenAffineVerticalStrip) :=
  ⟨fun x ↦
      (A.sectionSevenAffineCentralBandMarkedProductHomeomorph
        A.sectionSevenAffineCentralSeparation
          (A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph x)).1,
    continuous_fst.comp
      ((A.sectionSevenAffineCentralBandMarkedProductHomeomorph
        A.sectionSevenAffineCentralSeparation).continuous.comp
          A.sectionSevenActualAffineSplit.sidesIntersectionHomeomorph.continuous)⟩

/-- Translate the marked order-three torus coordinate by a gauge depending on the strip
coordinate, then pass to the reduced central fibre. -/
public noncomputable def sectionSevenAffineOrderThreeGaugeTranslatedProjection
    (A : PaperAnalyticData)
    (g : C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.SectionSevenAffineMarkedBand, OrderThreeReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
      A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.sectionSevenAffineBandStripCoordinate x) +
          sectionSevenAffineBandFiberCoordinate A x,
        continuous_add.comp
          ((g.continuous.comp A.sectionSevenAffineBandStripCoordinate.continuous).prodMk
            (sectionSevenAffineBandFiberCoordinate A).continuous)⟩

/-- Translate the marked order-four torus coordinate by a gauge depending on the strip
coordinate, then pass to the reduced central fibre. -/
public noncomputable def sectionSevenAffineOrderFourGaugeTranslatedProjection
    (A : PaperAnalyticData)
    (g : C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)) :
    C(A.SectionSevenAffineMarkedBand, OrderFourReducedCentralFiber A.periods) :=
  ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
    ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
      A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩).comp
      ⟨fun x ↦ g (A.sectionSevenAffineBandStripCoordinate x) +
          sectionSevenAffineBandFiberCoordinate A x,
        continuous_add.comp
          ((g.continuous.comp A.sectionSevenAffineBandStripCoordinate.continuous).prodMk
            (sectionSevenAffineBandFiberCoordinate A).continuous)⟩

/-- The honest point-set residue of the logarithmic-gauge calculation.  It says that, in fixed
real-period coordinates, each selected-filling endpoint differs from the marked band coordinate
by a torus translation depending only on the strip coordinate. -/
public structure SectionSevenAffineMarkedEndpointGaugeTranslation
    (A : PaperAnalyticData) where
  orderThreeGauge :
    C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderThreeFormula :
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderThreeStarEndpoint =
      A.sectionSevenAffineOrderThreeGaugeTranslatedProjection orderThreeGauge
  orderFourGauge :
    C(sectionSevenAffineVerticalStrip,
      AdditiveTorus A.duplicatedSectionSevenBandParameter)
  orderFourFormula :
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderFourStarEndpoint =
      A.sectionSevenAffineOrderFourGaugeTranslatedProjection orderFourGauge

/-- The endpoint-level homotopy statement left after removing the logarithmic gauge. -/
public structure SectionSevenAffineMarkedDiscEndpointHomotopyCompatibility
    (A : PaperAnalyticData) where
  orderThree :
    ((A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
      A.sectionSevenAffineOrderThreeDiscFillingEndpoint)).Homotopic
        (sectionSevenAffineBandOrderThreeMarkedProjection A)
  orderFour :
    ((A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
      A.sectionSevenAffineOrderFourDiscFillingEndpoint)).Homotopic
        (sectionSevenAffineBandOrderFourMarkedProjection A)

/-- Homotopic disc endpoints suffice for the original marked-band compatibility; literal
endpoint equality is unnecessary. -/
public theorem SectionSevenAffineMarkedDiscEndpointHomotopyCompatibility.toBandCompatibility
    {A : PaperAnalyticData}
    (H : A.SectionSevenAffineMarkedDiscEndpointHomotopyCompatibility) :
    A.SectionSevenAffineOverlapBandCompatibility := by
  apply markedBandHomotopies_of_sideContractions A
  refine { orderThree := ?_, orderFour := ?_ }
  · let q := A.sectionSevenAffineOrderThreeDiscFillingEndpoint
    let g := A.sectionSevenOrderThreeFillingImageHomotopyEquiv
    let p := sectionSevenAffineBandOrderThreeMarkedProjection A
    have hleft : (g.invFun.comp (g.toFun.comp q)).Homotopic q := by
      simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
        ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hright : (g.invFun.comp (g.toFun.comp q)).Homotopic
        (g.invFun.comp p) :=
      ContinuousMap.Homotopic.comp (.refl g.invFun) H.orderThree
    have hfill : q.Homotopic (g.invFun.comp p) := hleft.symm.trans hright
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.sectionSevenAffineOrderThreeFillingImageToSide) hfill
    have hendpoint :
        A.sectionSevenAffineOrderThreeFillingImageToSide.comp (g.invFun.comp p) =
          (sectionSevenAffineOrderThreeSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.sectionSevenAffineOrderThreeFillingImageToSide.comp
              (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.invFun.comp
                (sectionSevenAffineBandOrderThreeMarkedProjection A)) =
            (orderThreeOverlapIsHomotopyEquivalence_inclusion
                A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.sectionSevenActualAffineSplit.allocation.orderThreeSide
                A.sectionSevenOrderThreeFillingImage
                A.sectionSevenActualAffineSplit.orderThreeFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.sectionSevenOrderThreeFillingImageHomotopyEquiv.invFun.comp
                    (sectionSevenAffineBandOrderThreeMarkedProjection A))) := by
        rw [(orderThreeOverlapIsHomotopyEquivalence_inclusion
          A.orderThreeOverlapIsHomotopyEquivalence).toHomotopyEquiv_invFun]
        ext x
        rfl
      exact hraw.trans (sectionSevenAffineOrderThreeSideInverse_markedProjection A).symm
    rw [hendpoint] at hside
    exact A.orderThreeBandInclusion_homotopic_discFillingEndpoint.trans hside
  · let q := A.sectionSevenAffineOrderFourDiscFillingEndpoint
    let g := A.sectionSevenOrderFourFillingImageHomotopyEquiv
    let p := sectionSevenAffineBandOrderFourMarkedProjection A
    have hleft : (g.invFun.comp (g.toFun.comp q)).Homotopic q := by
      simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
        ContinuousMap.Homotopic.comp g.left_inv (.refl q)
    have hright : (g.invFun.comp (g.toFun.comp q)).Homotopic
        (g.invFun.comp p) :=
      ContinuousMap.Homotopic.comp (.refl g.invFun) H.orderFour
    have hfill : q.Homotopic (g.invFun.comp p) := hleft.symm.trans hright
    have hside := ContinuousMap.Homotopic.comp
      (.refl A.sectionSevenAffineOrderFourFillingImageToSide) hfill
    have hendpoint :
        A.sectionSevenAffineOrderFourFillingImageToSide.comp (g.invFun.comp p) =
          (sectionSevenAffineOrderFourSideToReducedFiberHomotopyEquiv A).invFun.comp p := by
      dsimp [g, p]
      have hraw :
          A.sectionSevenAffineOrderFourFillingImageToSide.comp
              (A.sectionSevenOrderFourFillingImageHomotopyEquiv.invFun.comp
                (sectionSevenAffineBandOrderFourMarkedProjection A)) =
            (orderFourOverlapIsHomotopyEquivalence_inclusion
                A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv.invFun.comp
              ((nestedSubtypeHomeomorph
                A.sectionSevenActualAffineSplit.allocation.orderFourSide
                A.sectionSevenOrderFourFillingImage
                A.sectionSevenActualAffineSplit.orderFourFillingImage_subset_side)
                |>.toHomotopyEquiv.invFun.comp
                  (A.sectionSevenOrderFourFillingImageHomotopyEquiv.invFun.comp
                    (sectionSevenAffineBandOrderFourMarkedProjection A))) := by
        rw [(orderFourOverlapIsHomotopyEquivalence_inclusion
          A.orderFourOverlapIsHomotopyEquivalence).toHomotopyEquiv_invFun]
        ext x
        rfl
      exact hraw.trans (sectionSevenAffineOrderFourSideInverse_markedProjection A).symm
    rw [hendpoint] at hside
    exact A.orderFourBandInclusion_homotopic_discFillingEndpoint.trans hside

/-- Reading the order-three disc endpoint in the filling retraction is exactly the same map as
reading its selected star endpoint. -/
public theorem sectionSevenAffineOrderThreeDiscEndpoint_toFun_eq_starEndpoint
    (A : PaperAnalyticData) :
    A.sectionSevenOrderThreeFillingImageHomotopyEquiv.toFun.comp
        A.sectionSevenAffineOrderThreeDiscFillingEndpoint =
      (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderThreeStarEndpoint := by
  apply ContinuousMap.ext
  intro x
  let u := A.sectionSevenAffineOrderThreeDiscOverlapEndpoint x
  have hfill : A.sectionSevenAffineOrderThreeDiscFillingEndpoint x =
      ⟨u.1, u.2.1⟩ := rfl
  change (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.sectionSevenOrderThreePieceHomeomorph.symm
        (A.sectionSevenOrderThreeFillingImageToPiece
          (A.sectionSevenAffineOrderThreeDiscFillingEndpoint x))) =
    (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.starToFilling 1 (A.orderThreeOverlapCollarHomeomorph u))
  rw [hfill]
  exact congrArg (orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun
    (A.sectionSevenOrderThreeFillingImageToPiece_symm_overlap u)

/-- Reading the order-four disc endpoint in the filling retraction is exactly the same map as
reading its selected star endpoint. -/
public theorem sectionSevenAffineOrderFourDiscEndpoint_toFun_eq_starEndpoint
    (A : PaperAnalyticData) :
    A.sectionSevenOrderFourFillingImageHomotopyEquiv.toFun.comp
        A.sectionSevenAffineOrderFourDiscFillingEndpoint =
      (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderFourStarEndpoint := by
  apply ContinuousMap.ext
  intro x
  let u := A.sectionSevenAffineOrderFourDiscOverlapEndpoint x
  have hfill : A.sectionSevenAffineOrderFourDiscFillingEndpoint x =
      ⟨u.1, u.2.1⟩ := rfl
  change (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.sectionSevenOrderFourPieceHomeomorph.symm
        (A.sectionSevenOrderFourFillingImageToPiece
          (A.sectionSevenAffineOrderFourDiscFillingEndpoint x))) =
    (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
      (A.starToFilling 2 (A.orderFourOverlapCollarHomeomorph u))
  rw [hfill]
  exact congrArg (orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun
    (A.sectionSevenOrderFourFillingImageToPiece_symm_overlap u)

/-- A base-dependent gauge translation gives the order-three selected-filling endpoint
homotopy. -/
public theorem SectionSevenAffineMarkedEndpointGaugeTranslation.orderThreeEndpointHomotopy
    {A : PaperAnalyticData} (G : A.SectionSevenAffineMarkedEndpointGaugeTranslation) :
    ((orderThreeSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderThreeStarEndpoint).Homotopic
        (sectionSevenAffineBandOrderThreeMarkedProjection A) := by
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  rw [G.orderThreeFormula]
  change (A.sectionSevenAffineOrderThreeGaugeTranslatedProjection
    G.orderThreeGauge).Homotopic _
  unfold sectionSevenAffineOrderThreeGaugeTranslatedProjection
  exact (continuousMap_comp_add_homotopic_of_contractible
    ((RadialEllipticActionData.centralFiberCoverProjection
      (orderThreeRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderThreeCoverSource,
          A.duplicatedSectionSevenBandToOrderThreeCoverSource.continuous⟩)
    (sectionSevenAffineBandFiberCoordinate A)
    A.sectionSevenAffineBandStripCoordinate G.orderThreeGauge).symm

/-- A base-dependent gauge translation gives the order-four selected-filling endpoint
homotopy. -/
public theorem SectionSevenAffineMarkedEndpointGaugeTranslation.orderFourEndpointHomotopy
    {A : PaperAnalyticData} (G : A.SectionSevenAffineMarkedEndpointGaugeTranslation) :
    ((orderFourSelectedFillingHomotopyEquivCentralFiber A).toFun.comp
        A.sectionSevenAffineOrderFourStarEndpoint).Homotopic
        (sectionSevenAffineBandOrderFourMarkedProjection A) := by
  let _ : ContractibleSpace sectionSevenAffineVerticalStrip :=
    sectionSevenAffineVerticalStripContractible
  rw [G.orderFourFormula]
  change (A.sectionSevenAffineOrderFourGaugeTranslatedProjection
    G.orderFourGauge).Homotopic _
  unfold sectionSevenAffineOrderFourGaugeTranslatedProjection
  exact (continuousMap_comp_add_homotopic_of_contractible
    ((RadialEllipticActionData.centralFiberCoverProjection
      (orderFourRadialActionData A.periods)).comp
        ⟨A.duplicatedSectionSevenBandToOrderFourCoverSource,
          A.duplicatedSectionSevenBandToOrderFourCoverSource.continuous⟩)
    (sectionSevenAffineBandFiberCoordinate A)
    A.sectionSevenAffineBandStripCoordinate G.orderFourGauge).symm

/-- The base-dependent logarithmic-gauge formula implies the original Section Seven marked-band
compatibility. -/
public theorem SectionSevenAffineMarkedEndpointGaugeTranslation.toBandCompatibility
    {A : PaperAnalyticData} (G : A.SectionSevenAffineMarkedEndpointGaugeTranslation) :
    A.SectionSevenAffineOverlapBandCompatibility := by
  apply SectionSevenAffineMarkedDiscEndpointHomotopyCompatibility.toBandCompatibility
  refine { orderThree := ?_, orderFour := ?_ }
  · rw [sectionSevenAffineOrderThreeDiscEndpoint_toFun_eq_starEndpoint]
    exact G.orderThreeEndpointHomotopy
  · rw [sectionSevenAffineOrderFourDiscEndpoint_toFun_eq_starEndpoint]
    exact G.orderFourEndpointHomotopy

end SphereSixComplex.Geometry.PaperAnalyticData

end
