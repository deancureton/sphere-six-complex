module

public import SphereSixComplex.Geometry.EllipticPuncturedCollarGaugeHomeomorph
public import SphereSixComplex.Geometry.EllipticLocalTrivialization
import all SphereSixComplex.Geometry.Quotient
import all SphereSixComplex.Geometry.TorusFamily

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

public structure EquivariantOpenDiffeomorphOfActions
    (AX : MulAction G X) (AY : MulAction G Y)
    (S : InvariantOpenCarrier AX) (T : InvariantOpenCarrier AY)
    [ChartedSpace H S.carrier] [ChartedSpace H T.carrier] where
  toDiffeomorph : S.carrier ≃ₘ^∞⟮I, I⟯ T.carrier
  equivariant : ∀ (g : G) (x : S.carrier),
    toDiffeomorph (restrictedActionMap S g x) =
      restrictedActionMap T g (toDiffeomorph x)

namespace EquivariantOpenDiffeomorphOfActions

variable {I} {AX : MulAction G X} {AY : MulAction G Y}
variable {S : InvariantOpenCarrier AX} {T : InvariantOpenCarrier AY}
variable [ChartedSpace H S.carrier] [ChartedSpace H T.carrier]

public noncomputable def toEquivariantHomeomorph
    (e : EquivariantOpenDiffeomorphOfActions I AX AY S T) :
    EquivariantOpenHomeomorphOfActions AX AY S T where
  toHomeomorph := e.toDiffeomorph.toHomeomorph
  equivariant := e.equivariant

public theorem restrictedOrbitQuotientHomeomorph_mk
    (e : EquivariantOpenDiffeomorphOfActions I AX AY S T) (x : S.carrier) :
    restrictedOrbitQuotientHomeomorph e.toEquivariantHomeomorph (Quotient.mk _ x) =
      Quotient.mk _ (e.toDiffeomorph x) :=
  rfl

public noncomputable def restrictedOrbitQuotientDiffeomorph
    (e : EquivariantOpenDiffeomorphOfActions I AX AY S T)
    [ChartedSpace H (Quotient (restrictedOrbitRel AX S))]
    [ChartedSpace H (Quotient (restrictedOrbitRel AY T))]
    (hsource : IsLocalDiffeomorph I I ∞
      (Quotient.mk (restrictedOrbitRel AX S)))
    (htarget : IsLocalDiffeomorph I I ∞
      (Quotient.mk (restrictedOrbitRel AY T))) :
    Quotient (restrictedOrbitRel AX S) ≃ₘ^∞⟮I, I⟯
      Quotient (restrictedOrbitRel AY T) where
  toEquiv := (restrictedOrbitQuotientHomeomorph e.toEquivariantHomeomorph).toEquiv
  contMDiff_toFun := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x =>
      let πS := Quotient.mk (restrictedOrbitRel AX S)
      let πT := Quotient.mk (restrictedOrbitRel AY T)
      let loc := (hsource x).localInverse
      have hlocal : ContMDiffAt I I ∞ loc (πS x) :=
        (hsource x).localInverse_contMDiffAt
      have hlocalx : loc (πS x) = x :=
        (hsource x).localInverse_left_inv (hsource x).localInverse_mem_target
      have hmiddle : ContMDiffAt I I ∞ (e.toDiffeomorph ∘ loc) (πS x) :=
        e.toDiffeomorph.contMDiff.contMDiffAt.comp_of_eq hlocal hlocalx
      have hrhs : ContMDiffAt I I ∞ (πT ∘ e.toDiffeomorph ∘ loc) (πS x) :=
        (htarget (e.toDiffeomorph x)).contMDiffAt.comp_of_eq hmiddle (by
          simp [hlocalx])
      have hevent : restrictedOrbitQuotientHomeomorph e.toEquivariantHomeomorph =ᶠ[
          nhds (πS x)] (πT ∘ e.toDiffeomorph ∘ loc) := by
        filter_upwards [(hsource x).localInverse_eventuallyEq_right] with y hy
        calc
          restrictedOrbitQuotientHomeomorph e.toEquivariantHomeomorph y =
              restrictedOrbitQuotientHomeomorph e.toEquivariantHomeomorph (πS (loc y)) :=
            congrArg _ hy.symm
          _ = πT (e.toDiffeomorph (loc y)) :=
            restrictedOrbitQuotientHomeomorph_mk e (loc y)
      exact hrhs.congr_of_eventuallyEq hevent

  contMDiff_invFun := by
    intro q
    induction q using Quotient.inductionOn with
    | _ y =>
      let πS := Quotient.mk (restrictedOrbitRel AX S)
      let πT := Quotient.mk (restrictedOrbitRel AY T)
      let loc := (htarget y).localInverse
      have hlocal : ContMDiffAt I I ∞ loc (πT y) :=
        (htarget y).localInverse_contMDiffAt
      have hlocaly : loc (πT y) = y :=
        (htarget y).localInverse_left_inv (htarget y).localInverse_mem_target
      have hmiddle : ContMDiffAt I I ∞ (e.toDiffeomorph.symm ∘ loc) (πT y) :=
        e.toDiffeomorph.contMDiff_invFun.contMDiffAt.comp_of_eq hlocal hlocaly
      have hrhs : ContMDiffAt I I ∞ (πS ∘ e.toDiffeomorph.symm ∘ loc) (πT y) :=
        (hsource (e.toDiffeomorph.symm y)).contMDiffAt.comp_of_eq hmiddle (by
          simp [hlocaly])
      have hevent : (restrictedOrbitQuotientHomeomorph
          e.toEquivariantHomeomorph).symm =ᶠ[nhds (πT y)]
          (πS ∘ e.toDiffeomorph.symm ∘ loc) := by
        filter_upwards [(htarget y).localInverse_eventuallyEq_right] with z hz
        calc
          (restrictedOrbitQuotientHomeomorph e.toEquivariantHomeomorph).symm z =
              (restrictedOrbitQuotientHomeomorph
                e.toEquivariantHomeomorph).symm (πT (loc z)) := congrArg _ hz.symm
          _ = πS (e.toDiffeomorph.symm (loc z)) := by
            apply (restrictedOrbitQuotientHomeomorph
              e.toEquivariantHomeomorph).injective
            rw [Homeomorph.apply_symm_apply,
              restrictedOrbitQuotientHomeomorph_mk]
            rw [e.toDiffeomorph.apply_symm_apply]
      exact hrhs.congr_of_eventuallyEq hevent

@[simp]
public theorem restrictedOrbitQuotientDiffeomorph_mk
    (e : EquivariantOpenDiffeomorphOfActions I AX AY S T)
    [ChartedSpace H (Quotient (restrictedOrbitRel AX S))]
    [ChartedSpace H (Quotient (restrictedOrbitRel AY T))]
    (hsource : IsLocalDiffeomorph I I ∞
      (Quotient.mk (restrictedOrbitRel AX S)))
    (htarget : IsLocalDiffeomorph I I ∞
      (Quotient.mk (restrictedOrbitRel AY T))) (x : S.carrier) :
    restrictedOrbitQuotientDiffeomorph e hsource htarget (Quotient.mk _ x) =
      Quotient.mk _ (e.toDiffeomorph x) :=
  rfl

end EquivariantOpenDiffeomorphOfActions

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
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) :
    ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
      (familyTranslationMap F s) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
      projection (parameterMap F)
    let loc := (hprojection p).localInverse
    have hs' : ContMDiffAt (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ComplexTwoSpace) ω s p.1 := by
      simpa only [familyTotalSpaceBase_mk] using hs
    have hlocal : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω loc (π p) :=
      (hprojection p).localInverse_contMDiffAt
    have hlocalp : loc (π p) = p :=
      (hprojection p).localInverse_left_inv (hprojection p).localInverse_mem_target
    have htranslation : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
        (familyTranslationCover s) p :=
      contMDiffAt_fst.prodMk ((hs'.comp p contMDiffAt_fst).add contMDiffAt_snd)
    have hcover : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
        (familyTranslationCover s ∘ loc) (π p) :=
      htranslation.comp_of_eq hlocal hlocalp
    have hrhs : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
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
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderThreePuncturedFamilyCollar F r) :
    ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
      (orderThreePrincipalGaugeEquiv F) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderThreeCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderThreeBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderThreeBranchesAt w hw
    have hbranch : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
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
      norm_num [discCenter] at hpos
    exact hbranch.congr_of_eventuallyEq heq

public theorem orderFourPrincipalGauge_contMDiffAt
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderFourPuncturedFamilyCollar F r) :
    ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
      (orderFourPrincipalGaugeEquiv F) q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderFourCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderFourBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderFourBranchesAt w hw
    have hbranch : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
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
      norm_num [discCenter] at hpos
    exact hbranch.congr_of_eventuallyEq heq

public theorem orderThreePrincipalGauge_symm_contMDiffAt
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderThreePuncturedFamilyCollar F r) :
    ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
      (orderThreePrincipalGaugeEquiv F).symm q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderThreeCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderThreeBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderThreeBranchesAt w hw
    let localMap := familyTranslationMap F
      (-logarithmicGaugeSection F orderThreeCayleyHomeomorph epsilon
        (fun u => B.log u))
    have hbranch : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
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
      norm_num [discCenter] at hpos
    exact hbranch.congr_of_eventuallyEq heq

public theorem orderFourPrincipalGauge_symm_contMDiffAt
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : TotalSpace (parameterMap F)) (hq : q ∈ orderFourPuncturedFamilyCollar F r) :
    ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
      (orderFourPrincipalGaugeEquiv F).symm q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    let w := orderFourCayleyHomeomorph p.1
    have hw : w ≠ discCenter := by
      intro h
      have hpos := hq.1
      change 0 < ‖(w : ℂ)‖ at hpos
      rw [h] at hpos
      norm_num [discCenter] at hpos
    let B := (orderFourBranchesAt w hw).source
    have hwB : (w : ℂ) ∈ B.carrier := mem_orderFourBranchesAt w hw
    let localMap := familyTranslationMap F
      (-logarithmicGaugeSection F orderFourCayleyHomeomorph (-epsilon')
        (fun u => B.log u))
    have hbranch : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ω
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
      norm_num [discCenter] at hpos
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

public noncomputable instance orderThreeLinearPuncturedCarrierCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (orderThreeLinearPuncturedCarrier F hsource r).carrier := by
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

public noncomputable instance orderFourLinearPuncturedCarrierCharts
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    ChartedSpace (ModelProd ℂ ComplexTwoSpace)
      (orderFourLinearPuncturedCarrier F hsource r).carrier := by
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace)
    (orderFourPuncturedFamilyCollar F r)
  infer_instance

public noncomputable def orderThreePuncturedCollarGaugeDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ) :
    orderThreePuncturedFamilyCollar F r ≃ₘ^∞⟮GlobalDeckTotalModel,
      GlobalDeckTotalModel⟯ orderThreePuncturedFamilyCollar F r where
  toEquiv := orderThreePuncturedCollarGaugeEquiv F r
  contMDiff_toFun := by
    let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨orderThreePuncturedFamilyCollar F r,
        orderThreePuncturedFamilyCollar_isOpen F r⟩
    have hcharts : orderThreePuncturedCollarCharts F r = S.instChartedSpace := rfl
    rw [hcharts]
    intro q
    apply (ContMDiffAt.subtypeVal_comp_iff S _ q).mp
    change ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
    change ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (fun x : S => (orderThreePrincipalGaugeEquiv F).symm x.1) q
    rw [contMDiffAt_subtype_iff]
    exact (orderThreePrincipalGauge_symm_contMDiffAt F hprojection r q q.property).of_le (by simp)

public noncomputable def orderFourPuncturedCollarGaugeDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ) :
    orderFourPuncturedFamilyCollar F r ≃ₘ^∞⟮GlobalDeckTotalModel,
      GlobalDeckTotalModel⟯ orderFourPuncturedFamilyCollar F r where
  toEquiv := orderFourPuncturedCollarGaugeEquiv F r
  contMDiff_toFun := by
    let S : TopologicalSpace.Opens (TotalSpace (parameterMap F)) :=
      ⟨orderFourPuncturedFamilyCollar F r,
        orderFourPuncturedFamilyCollar_isOpen F r⟩
    have hcharts : orderFourPuncturedCollarCharts F r = S.instChartedSpace := rfl
    rw [hcharts]
    intro q
    apply (ContMDiffAt.subtypeVal_comp_iff S _ q).mp
    change ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ∞
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
    change ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel ∞
      (fun x : S => (orderFourPrincipalGaugeEquiv F).symm x.1) q
    rw [contMDiffAt_subtype_iff]
    exact (orderFourPrincipalGauge_symm_contMDiffAt F hprojection r q q.property).of_le (by simp)

@[simp]
public theorem orderThreePuncturedCollarGaugeDiffeomorph_apply
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : orderThreePuncturedFamilyCollar F r) :
    orderThreePuncturedCollarGaugeDiffeomorph F hprojection r q =
      ⟨orderThreePrincipalGaugeEquiv F q, by
        simpa [orderThreePuncturedFamilyCollar.eq_def,
          orderThreeFamilyRadius_principalGauge F] using q.property⟩ :=
  rfl

@[simp]
public theorem orderFourPuncturedCollarGaugeDiffeomorph_apply
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F))) (r : ℝ)
    (q : orderFourPuncturedFamilyCollar F r) :
    orderFourPuncturedCollarGaugeDiffeomorph F hprojection r q =
      ⟨orderFourPrincipalGaugeEquiv F q, by
        simpa [orderFourPuncturedFamilyCollar.eq_def,
          orderFourFamilyRadius_principalGauge F] using q.property⟩ :=
  rfl

public noncomputable def orderThreePuncturedGaugeEquivariantDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    EquivariantOpenDiffeomorphOfActions GlobalDeckTotalModel
      (orderThreeAffineFamilyAction F) (orderThreeLinearFamilyAction F)
      (orderThreeAffinePuncturedCarrier F hsource r)
      (orderThreeLinearPuncturedCarrier F hsource r) where
  toDiffeomorph := orderThreePuncturedCollarGaugeDiffeomorph F hprojection r
  equivariant :=
    (orderThreePuncturedGaugeEquivariantHomeomorph F hprojection hsource r).equivariant

public noncomputable def orderFourPuncturedGaugeEquivariantDiffeomorph
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
      (projection (parameterMap F)))
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    EquivariantOpenDiffeomorphOfActions GlobalDeckTotalModel
      (orderFourAffineFamilyAction F) (orderFourLinearFamilyAction F)
      (orderFourAffinePuncturedCarrier F hsource r)
      (orderFourLinearPuncturedCarrier F hsource r) where
  toDiffeomorph := orderFourPuncturedCollarGaugeDiffeomorph F hprojection r
  equivariant :=
    (orderFourPuncturedGaugeEquivariantHomeomorph F hprojection hsource r).equivariant

end SphereSixComplex.Geometry.EllipticAnalyticCollarDescent
