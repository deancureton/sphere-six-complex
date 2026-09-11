module

public import SphereSixComplex.Paper.Geometry.EllipticPuncturedCollarGaugeHomeomorph
import all SphereSixComplex.Prerequisites.Geometry.Quotient
import all SphereSixComplex.Paper.Geometry.TorusFamily

@[expose] public section

noncomputable section

open Set
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.EllipticAnalyticCollarDescent

open SphereSixComplex LatticeData Periods TriangleGroup
open ComplexTorus TorusFamily GlobalTorusFamily AnalyticTorusFamily
open EllipticLocalCoordinates EllipticLocalTrivialization EllipticCayleyHomeomorph
open EllipticWholeFiberCompactCover
open EllipticVaryingFamilyQuotient EllipticLogarithmicGauge
open EllipticLogarithmicGaugeDescent
open EllipticHolomorphicLogCover EllipticPuncturedCollarGaugeHomeomorph
open EquivariantQuotientHomeomorph

universe u v w

variable {G X Y : Type u} [Group G] [TopologicalSpace X] [TopologicalSpace Y]
variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)


variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem logarithmicGaugeSection_contMDiffAt
    (cayley : UpperHalfPlane ≃ₘ^ω⟮(modelWithCornersSelf ℂ ℂ),
      (modelWithCornersSelf ℂ ℂ)⟯ ComplexUnitDisc)
    (v : Lattice) (B : HolomorphicLogBranch) (z : UpperHalfPlane)
    (hz : (cayley z : ℂ) ∈ B.carrier) :
    ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ComplexTwoSpace) ω
      (logarithmicGaugeSection F cayley v (fun w => B.log w)) z := by
  have hlog : ContDiffAt ℂ ω B.log (cayley z : ℂ) := by
    rw [← contDiffWithinAt_iff_contDiffAt (B.isOpen_carrier.mem_nhds hz)]
    exact B.differentiableOn_log.contDiffOn B.isOpen_carrier _ hz
  have hlogm : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ω B.log (cayley z : ℂ) :=
    contMDiffAt_iff_contDiffAt.mpr hlog
  have hcayley : ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ω
      (fun x : UpperHalfPlane => (cayley x : ℂ)) :=
    (contMDiff_isOpenEmbedding discValIsOpenEmbedding).comp cayley.contMDiff
  have hcomp : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ω
      (fun x : UpperHalfPlane => B.log (cayley x : ℂ)) z :=
    hlogm.comp z hcayley.contMDiffAt
  have hscalar : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ω
      (fun x : UpperHalfPlane =>
        logarithmicGaugeScalar (B.log (cayley x : ℂ))) z :=
    contMDiffAt_const.mul hcomp
  change ContMDiffAt (modelWithCornersSelf ℂ ℂ)
    (modelWithCornersSelf ℂ ComplexTwoSpace) ω
    (fun x : UpperHalfPlane =>
      logarithmicGaugeScalar (B.log (cayley x : ℂ)) •
        periodVector (parameterMap F x).1 v) z
  exact hscalar.smul (periodSection_contMDiff F v ω).contMDiffAt

public theorem familyTranslationMap_contMDiffAt_of_section
    (s : UpperHalfPlane → ComplexTwoSpace) (q : TotalSpace (parameterMap F))
    (hs : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ComplexTwoSpace) ω s (familyTotalSpaceBase F q))
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) :
    ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
      (familyTranslationMap F s) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
      projection (parameterMap F)
    let loc := (hprojection p).localInverse
    have hs' : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ComplexTwoSpace) ω s p.1 := by
      simpa only [familyTotalSpaceBase_mk] using hs
    have hlocal : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω loc (π p) :=
      (hprojection p).localInverse_contMDiffAt
    have hlocalp : loc (π p) = p :=
      (hprojection p).localInverse_left_inv (hprojection p).localInverse_mem_target
    have htranslation : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
        (familyTranslationCover s) p :=
      contMDiffAt_fst.prodMk ((hs'.comp p contMDiffAt_fst).add contMDiffAt_snd)
    have hcover : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
        (familyTranslationCover s ∘ loc) (π p) :=
      htranslation.comp_of_eq hlocal hlocalp
    have hrhs : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
        (π ∘ familyTranslationCover s ∘ loc) (π p) :=
      (hprojection (familyTranslationCover s p)).contMDiffAt.comp_of_eq hcover (by
        simp [hlocalp])
    have hevent : familyTranslationMap F s =ᶠ[nhds (π p)]
        (π ∘ familyTranslationCover s ∘ loc) := by
      filter_upwards [(hprojection p).localInverse_eventuallyEq_right] with x hx
      calc
        familyTranslationMap F s x = familyTranslationMap F s (π (loc x)) :=
          congrArg _ hx.symm
        _ = π (familyTranslationCover s (loc x)) :=
          familyTranslationMap_mk F s (loc x)
    exact hrhs.congr_of_eventuallyEq hevent

public theorem orderThreePrincipalGauge_contMDiffAt
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderThreePuncturedFamilyCollar F r) :
    ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
      (orderThreePrincipalGaugeEquiv F) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderThreeCayleyHomeomorph p.1
    have hw : w ≠ ComplexUnitDisc.center := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    let B := (orderThreeBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderThreeBranchesAt w hw
    have hbranch : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
        (orderThreeLogarithmicGaugeMap F (fun u => B.log u)) (Quotient.mk _ p) := by
      apply familyTranslationMap_contMDiffAt_of_section F _ (Quotient.mk _ p) _ hprojection
      exact logarithmicGaugeSection_contMDiffAt F
        (orderThreeCayleyDiffeomorph ω) epsilon B p.1 hwB
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderThreeCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier :=
      hopen.mem_nhds hwB
    have hcollar : ∀ᶠ x in nhds (Quotient.mk _ p),
        x ∈ orderThreePuncturedFamilyCollar F r :=
      (orderThreePuncturedFamilyCollar_isOpen F r).mem_nhds hq
    have heq : orderThreePrincipalGaugeEquiv F =ᶠ[nhds (Quotient.mk _ p)]
        orderThreeLogarithmicGaugeMap F (fun u => B.log u) := by
      filter_upwards [hnear, hcollar] with x hxB hx
      apply orderThreePrincipalGauge_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderThreeCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    exact hbranch.congr_of_eventuallyEq heq

public theorem orderFourPrincipalGauge_contMDiffAt
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderFourPuncturedFamilyCollar F r) :
    ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
      (orderFourPrincipalGaugeEquiv F) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderFourCayleyHomeomorph p.1
    have hw : w ≠ ComplexUnitDisc.center := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    let B := (orderFourBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderFourBranchesAt w hw
    have hbranch : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
        (orderFourLogarithmicGaugeMap F (fun u => B.log u)) (Quotient.mk _ p) := by
      apply familyTranslationMap_contMDiffAt_of_section F _ (Quotient.mk _ p) _ hprojection
      exact logarithmicGaugeSection_contMDiffAt F
        (orderFourCayleyDiffeomorph ω) (-epsilon') B p.1 hwB
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderFourCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier :=
      hopen.mem_nhds hwB
    have hcollar : ∀ᶠ x in nhds (Quotient.mk _ p),
        x ∈ orderFourPuncturedFamilyCollar F r :=
      (orderFourPuncturedFamilyCollar_isOpen F r).mem_nhds hq
    have heq : orderFourPrincipalGaugeEquiv F =ᶠ[nhds (Quotient.mk _ p)]
        orderFourLogarithmicGaugeMap F (fun u => B.log u) := by
      filter_upwards [hnear, hcollar] with x hxB hx
      apply orderFourPrincipalGauge_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderFourCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    exact hbranch.congr_of_eventuallyEq heq

public theorem orderThreePrincipalGauge_symm_contMDiffAt
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderThreePuncturedFamilyCollar F r) :
    ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
      (orderThreePrincipalGaugeEquiv F).symm q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderThreeCayleyHomeomorph p.1
    have hw : w ≠ ComplexUnitDisc.center := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    let B := (orderThreeBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderThreeBranchesAt w hw
    let localMap := familyTranslationMap F
      (-logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
        (fun u => B.log u))
    have hbranch : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
        localMap (Quotient.mk _ p) := by
      apply familyTranslationMap_contMDiffAt_of_section F _ (Quotient.mk _ p) _ hprojection
      exact (logarithmicGaugeSection_contMDiffAt F
        (orderThreeCayleyDiffeomorph ω) epsilon B p.1 hwB).neg
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderThreeCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderThreeCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier :=
      hopen.mem_nhds hwB
    have hcollar : ∀ᶠ x in nhds (Quotient.mk _ p),
        x ∈ orderThreePuncturedFamilyCollar F r :=
      (orderThreePuncturedFamilyCollar_isOpen F r).mem_nhds hq
    have heq : (orderThreePrincipalGaugeEquiv F).symm =ᶠ[nhds (Quotient.mk _ p)]
        localMap := by
      filter_upwards [hnear, hcollar] with x hxB hx
      apply orderThreePrincipalGauge_symm_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderThreeCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    exact hbranch.congr_of_eventuallyEq heq

public theorem orderFourPrincipalGauge_symm_contMDiffAt
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderFourPuncturedFamilyCollar F r) :
    ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
      (orderFourPrincipalGaugeEquiv F).symm q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderFourCayleyHomeomorph p.1
    have hw : w ≠ ComplexUnitDisc.center := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    let B := (orderFourBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderFourBranchesAt w hw
    let localMap := familyTranslationMap F
      (-logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
        (fun u => B.log u))
    have hbranch : ContMDiffAt globalDeckTotalModel globalDeckTotalModel ω
        localMap (Quotient.mk _ p) := by
      apply familyTranslationMap_contMDiffAt_of_section F _ (Quotient.mk _ p) _ hprojection
      exact (logarithmicGaugeSection_contMDiffAt F
        (orderFourCayleyDiffeomorph ω) (-epsilon') B p.1 hwB).neg
    have hopen : IsOpen
        {x : TotalSpace (parameterMap F) |
          (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier} :=
      B.isOpen_carrier.preimage
        (continuous_subtype_val.comp
          (orderFourCayleyHomeomorph.continuous.comp
            (familyTotalSpaceBase_continuous F)))
    have hnear : ∀ᶠ x in nhds (Quotient.mk _ p),
        (orderFourCayleyHomeomorph (familyTotalSpaceBase F x) : ℂ) ∈ B.carrier :=
      hopen.mem_nhds hwB
    have hcollar : ∀ᶠ x in nhds (Quotient.mk _ p),
        x ∈ orderFourPuncturedFamilyCollar F r :=
      (orderFourPuncturedFamilyCollar_isOpen F r).mem_nhds hq
    have heq : (orderFourPrincipalGaugeEquiv F).symm =ᶠ[nhds (Quotient.mk _ p)]
        localMap := by
      filter_upwards [hnear, hcollar] with x hxB hx
      apply orderFourPrincipalGauge_symm_eq_branch F B x hxB
      intro hcenter
      have hpos := hx.1
      change 0 < ‖(orderFourCayleyHomeomorph
        (familyTotalSpaceBase F x) : ℂ)‖ at hpos
      rw [hcenter] at hpos
      norm_num [ComplexUnitDisc.center] at hpos
    exact hbranch.congr_of_eventuallyEq heq

public noncomputable instance orderThreePuncturedCollarCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (r : ℝ) : ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (orderThreePuncturedFamilyCollar F r) := by
  let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨orderThreePuncturedFamilyCollar F r,
      orderThreePuncturedFamilyCollar_isOpen F r⟩
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace) S
  infer_instance

public noncomputable instance orderFourPuncturedCollarCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (r : ℝ) : ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (orderFourPuncturedFamilyCollar F r) := by
  let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
    ⟨orderFourPuncturedFamilyCollar F r,
      orderFourPuncturedFamilyCollar_isOpen F r⟩
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace) S
  infer_instance

public noncomputable instance orderThreeAffinePuncturedCarrierCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (orderThreeAffinePuncturedCarrier F hsource r).carrier := by
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace)
    (orderThreePuncturedFamilyCollar F r)
  infer_instance


public noncomputable instance orderFourAffinePuncturedCarrierCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (orderFourAffinePuncturedCarrier F hsource r).carrier := by
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace)
    (orderFourPuncturedFamilyCollar F r)
  infer_instance


public noncomputable def orderThreePuncturedCollarGaugeDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ) :
    orderThreePuncturedFamilyCollar F r ≃ₘ^∞⟮globalDeckTotalModel,
      globalDeckTotalModel⟯ orderThreePuncturedFamilyCollar F r where
  toEquiv := orderThreePuncturedCollarGaugeEquiv F r
  contMDiff_toFun := by
    let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨orderThreePuncturedFamilyCollar F r,
        orderThreePuncturedFamilyCollar_isOpen F r⟩
    have hcharts : orderThreePuncturedCollarCharts F r = S.instChartedSpace := rfl
    rw [hcharts]
    intro q
    apply (ContMDiffAt.subtypeVal_comp_iff S _ q).mp
    change ContMDiffAt globalDeckTotalModel globalDeckTotalModel ∞
      (fun x : S => orderThreePrincipalGaugeEquiv F x.1) q
    rw [contMDiffAt_subtype_iff]
    exact (orderThreePrincipalGauge_contMDiffAt F hprojection r q q.property).of_le (by simp)
  contMDiff_invFun := by
    let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨orderThreePuncturedFamilyCollar F r,
        orderThreePuncturedFamilyCollar_isOpen F r⟩
    have hcharts : orderThreePuncturedCollarCharts F r = S.instChartedSpace := rfl
    rw [hcharts]
    intro q
    apply (ContMDiffAt.subtypeVal_comp_iff S _ q).mp
    change ContMDiffAt globalDeckTotalModel globalDeckTotalModel ∞
      (fun x : S => (orderThreePrincipalGaugeEquiv F).symm x.1) q
    rw [contMDiffAt_subtype_iff]
    exact (orderThreePrincipalGauge_symm_contMDiffAt F hprojection r q q.property).of_le (by simp)

public noncomputable def orderFourPuncturedCollarGaugeDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold globalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph globalDeckTotalModel globalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ) :
    orderFourPuncturedFamilyCollar F r ≃ₘ^∞⟮globalDeckTotalModel,
      globalDeckTotalModel⟯ orderFourPuncturedFamilyCollar F r where
  toEquiv := orderFourPuncturedCollarGaugeEquiv F r
  contMDiff_toFun := by
    let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨orderFourPuncturedFamilyCollar F r,
        orderFourPuncturedFamilyCollar_isOpen F r⟩
    have hcharts : orderFourPuncturedCollarCharts F r = S.instChartedSpace := rfl
    rw [hcharts]
    intro q
    apply (ContMDiffAt.subtypeVal_comp_iff S _ q).mp
    change ContMDiffAt globalDeckTotalModel globalDeckTotalModel ∞
      (fun x : S => orderFourPrincipalGaugeEquiv F x.1) q
    rw [contMDiffAt_subtype_iff]
    exact (orderFourPrincipalGauge_contMDiffAt F hprojection r q q.property).of_le (by simp)
  contMDiff_invFun := by
    let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨orderFourPuncturedFamilyCollar F r,
        orderFourPuncturedFamilyCollar_isOpen F r⟩
    have hcharts : orderFourPuncturedCollarCharts F r = S.instChartedSpace := rfl
    rw [hcharts]
    intro q
    apply (ContMDiffAt.subtypeVal_comp_iff S _ q).mp
    change ContMDiffAt globalDeckTotalModel globalDeckTotalModel ∞
      (fun x : S => (orderFourPrincipalGaugeEquiv F).symm x.1) q
    rw [contMDiffAt_subtype_iff]
    exact (orderFourPrincipalGauge_symm_contMDiffAt F hprojection r q q.property).of_le (by simp)





end SphereSixComplex.Geometry.EllipticAnalyticCollarDescent
