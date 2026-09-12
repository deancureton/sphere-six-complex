module

public import SphereSixComplex.Paper.Topology.AffineVanKampenTransport
public import SphereSixComplex.Paper.Topology.EstablishedBasedVanKampen
public import SphereSixComplex.Paper.Topology.PaperActualAffineCoreData
public import SphereSixComplex.Paper.Topology.PaperActualVanKampenNiceness
public import SphereSixComplex.Paper.Topology.PaperCuspAffineFillingBridge
public import SphereSixComplex.Paper.Topology.AffineRealMappingTorusUniversalCover
public import SphereSixComplex.Paper.Geometry.PaperAnalyticFillingPieces
public import SphereSixComplex.Paper.Geometry.GlobalTorusFiberFundamentalGroup
public import SphereSixComplex.Prerequisites.Topology.QuotientCoverEquivarianceExtension

/-!
# Reduction of the actual affine filling-cover squares to the two elliptic inputs

`ActualAffineFillingCoverSquares` bundles the three regular cover squares of the four-piece star
together with the based affine filling bridge.  The cusp square, its marked central naturality
and the whole cusp half of the bridge are already available:
`PaperCuspChosenAffineFilling` and `PaperCuspAffineFillingBridge`.

This module supplies the two purely formal pieces that were still missing on the elliptic side —
the based gluing squares of the two elliptic overlaps, and the transported cyclic filling
relations — and isolates the remaining geometric content in a single structure,
`ActualEllipticCentralNaturality`.  That structure is the exact elliptic counterpart of
`CuspCentralNaturality`, extended by the two chosen cyclic regular-cover models.

The reduction theorem, `nonempty_actualAffineFillingCoverSquares_of_ellipticNaturality`, shows
that any marked cusp naturality together with such an elliptic package produces
`Nonempty A.ActualAffineFillingCoverSquares`.  It uses no van Kampen conclusion and, in
particular, not `establishedActualAffineFillingCoverSquares`.

The two naturalities are then bundled as `ActualStarPeripheralNaturality`, and the single
remaining geometric input is `establishedActualStarPeripheralNaturality`.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace SphereSixComplex.Topology
namespace PaperVanKampenFourPieceCover

variable {Y : Type*} [TopologicalSpace Y] {base : Y}

/-- The based gluing square for an arbitrary overlap of the core with a piece, transported to the
base point along a connector that stays inside the core. -/
public theorem coreSquare_apply
    (D : PaperVanKampenFourPieceCover base) (P : Set Y) {pt : Y}
    (hpt : pt ∈ D.core ∩ P) (conn : Path base pt) (hconn : ∀ t, conn t ∈ D.core)
    (γ : FundamentalGroup (D.core ∩ P : Set Y) ⟨pt, hpt⟩) :
    D.coreFundamentalGroupMap
        ((FundamentalGroup.fundamentalGroupMulEquivOfPath
            (D.connectorInCore conn hconn hpt.1).symm)
          (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ γ)) =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm)
        (FundamentalGroup.map (CoveringSpace.subsetInclusion P) ⟨pt, hpt.2⟩
          (FundamentalGroup.map
            (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z.1, z.2.2⟩ : P), by fun_prop⟩ :
              C((D.core ∩ P : Set Y), P)) ⟨pt, hpt⟩ γ)) := by
  set connCore := D.connectorInCore conn hconn hpt.1
  have hnat := CoveringSpace.map_fundamentalGroupMulEquivOfPath (CoveringSpace.subsetInclusion D.core) connCore.symm
    (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ γ)
  have hpath : connCore.symm.map (CoveringSpace.subsetInclusion D.core).continuous = conn.symm := by
    ext t
    rfl
  change FundamentalGroup.map (CoveringSpace.subsetInclusion D.core) _
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm) _) =
    (FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm) _
  apply Eq.trans hnat
  rw [hpath]
  congr 1
  have h1 := CoveringSpace.map_map (D.overlapToCore P) (CoveringSpace.subsetInclusion D.core) ⟨pt, hpt⟩ γ
  have h2 := CoveringSpace.map_map
    (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z.1, z.2.2⟩ : P), by fun_prop⟩ :
      C((D.core ∩ P : Set Y), P)) (CoveringSpace.subsetInclusion P) ⟨pt, hpt⟩ γ
  apply Eq.trans h1
  apply Eq.trans ?_ h2.symm
  rfl

end PaperVanKampenFourPieceCover
end SphereSixComplex.Topology

namespace SphereSixComplex

/-- The action on a product which leaves the first coordinate fixed. -/
@[instance_reducible] public def passiveProdAction
    (G R E : Type*) [Group G] [MulAction G E] : MulAction G (R × E) where
  smul g p := (p.1, g • p.2)
  one_smul p := Prod.ext rfl (one_smul G p.2)
  mul_smul g h p := Prod.ext rfl (mul_smul g h p.2)

/-- A regular quotient cover remains one after adjoining a passive product coordinate. -/
public theorem passiveProd_isQuotientCoveringMap
    {G R E B : Type*} [Group G] [TopologicalSpace R]
    [TopologicalSpace E] [TopologicalSpace B] [MulAction G E]
    {f : E → B} (hf : IsQuotientCoveringMap f G) :
    letI := passiveProdAction G R E
    IsQuotientCoveringMap (fun p : R × E ↦ (p.1, f p.2)) G := by
  let _ : MulAction G (R × E) := passiveProdAction G R E
  refine
    { toIsQuotientMap := ?_
      continuous_const_smul := ?_
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · exact ((IsOpenMap.id.prodMap hf.isCoveringMap.isOpenMap).isQuotientMap
      (continuous_id.prodMap hf.toIsQuotientMap.continuous)
      (Function.Surjective.prodMap Function.surjective_id
        hf.toIsQuotientMap.surjective))
  · intro g
    exact continuous_fst.prodMk
      ((hf.continuous_const_smul g).comp continuous_snd)
  · intro p q
    rw [Prod.ext_iff, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨hr, he⟩
      obtain ⟨g, hg⟩ := hf.apply_eq_iff_mem_orbit.mp he
      exact ⟨g, Prod.ext hr.symm hg⟩
    · rintro ⟨g, hg⟩
      have hr := congrArg Prod.fst hg
      have he := congrArg Prod.snd hg
      exact ⟨hr.symm, hf.apply_eq_iff_mem_orbit.mpr ⟨g, he⟩⟩
  · intro p
    obtain ⟨U, hU, hdisj⟩ := hf.disjoint p.2
    refine ⟨Set.univ ×ˢ U, prod_mem_nhds Filter.univ_mem hU, ?_⟩
    intro g hg
    apply hdisj g
    rcases hg with ⟨q, ⟨w, hw, hgwq⟩, hq⟩
    exact ⟨q.2, ⟨w.2, hw.2, congrArg Prod.snd hgwq⟩, hq.2⟩

/-- The canonical cyclic affine relation is killed by the transported filling inclusion. -/
public theorem chosenCyclicRelation_killed
    {m : ℕ} {Λ B N : Type*} [NeZero m] [AddCommGroup Λ]
    [TopologicalSpace B] [TopologicalSpace N]
    (D : ChosenCyclicAffineFillingCoverModel m Λ B N) {b : B} {n : N}
    (hb : D.boundaryBase = b) (hn : D.fillingBase = n) {tw : Λ} (htw : D.twist = tw) :
    fundamentalGroupHomOfBaseEq hb hn D.fundamentalGroupMap
        ((fundamentalGroupElementOfBaseEq hb D.meridian) ^ m *
          (Additive.toMul
            ((fundamentalGroupAddHomOfBaseEq hb D.translation) tw))⁻¹) = 1 := by
  subst hb
  subst hn
  subst htw
  exact D.fundamentalGroupMap_relation

/-- Transporting the source and target base points of a map does not change its induced
fundamental-group homomorphism. -/
public theorem fundamentalGroupHomOfBaseEq_map_transport
    {B N : Type*} [TopologicalSpace B] [TopologicalSpace N]
    (f : C(B, N)) {b b' : B} (hb : b = b') (hn : f b = f b') :
    fundamentalGroupHomOfBaseEq hb hn (FundamentalGroup.map f b) =
      FundamentalGroup.map f b' := by
  subst b'
  rfl

end SphereSixComplex

namespace SphereSixComplex.Geometry.AnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.RealPeriodTrivialization
open SphereSixComplex.EllipticFilling

variable (A : AnalyticData)

/-- The analytic order-three collar source, identified with the exact overlap in the actual
four-piece cover. -/
public noncomputable def orderThreeCollarToActualOverlapHomeomorph :
    A.StarCollarSource 1 ≃ₜ
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace) := by
  refine
    (A.openEmbeddingStarData.centralFillingIntersectionHomeomorph 1).trans
      (Homeomorph.setCongr ?_)
  symm
  ext x
  simp [actualVanKampenFourPieceCover, vanKampenOpenCover,
    finiteCoverIntersection]

/-- The analytic order-four collar source, identified with the exact overlap in the actual
four-piece cover. -/
public noncomputable def orderFourCollarToActualOverlapHomeomorph :
    A.StarCollarSource 2 ≃ₜ
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace) := by
  refine
    (A.openEmbeddingStarData.centralFillingIntersectionHomeomorph 2).trans
      (Homeomorph.setCongr ?_)
  symm
  ext x
  simp [actualVanKampenFourPieceCover, vanKampenOpenCover,
    finiteCoverIntersection]

/-- The radial mapping-torus presentation of the exact actual order-three overlap. -/
public noncomputable def orderThreeRadialMappingTorusToActualOverlapHomeomorph :
    OpenRadialInterval A.starSeparation.orderThree.radius ×
        CircleMappingTorus (orderThreeAffineClutchingHomeomorph A.periods) ≃ₜ
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace) :=
  A.orderThreeCollarRadialMappingTorusHomeomorph.symm.trans
    A.orderThreeCollarToActualOverlapHomeomorph

/-- The radial mapping-torus presentation of the exact actual order-four overlap. -/
public noncomputable def orderFourRadialMappingTorusToActualOverlapHomeomorph :
    OpenRadialInterval A.starSeparation.orderFour.radius ×
        CircleMappingTorus (orderFourAffineClutchingHomeomorph A.periods) ≃ₜ
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace) :=
  A.orderFourCollarRadialMappingTorusHomeomorph.symm.trans
    A.orderFourCollarToActualOverlapHomeomorph

/-- The explicit simply connected cover projection of the exact actual order-three overlap. -/
public noncomputable def ellipticThreeBoundaryProjection :
    C(OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace),
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)) where
  toFun q := A.orderThreeRadialMappingTorusToActualOverlapHomeomorph
    (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2)
  continuous_toFun :=
    A.orderThreeRadialMappingTorusToActualOverlapHomeomorph.continuous.comp
      (continuous_fst.prodMk
        ((orderThreeAffineMappingTorusLiftProjection A.periods).continuous.comp continuous_snd))

/-- The explicit simply connected cover projection of the exact actual order-four overlap. -/
public noncomputable def ellipticFourBoundaryProjection :
    C(OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace),
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)) where
  toFun q := A.orderFourRadialMappingTorusToActualOverlapHomeomorph
    (q.1, orderFourAffineMappingTorusLiftProjection A.periods q.2)
  continuous_toFun :=
    A.orderFourRadialMappingTorusToActualOverlapHomeomorph.continuous.comp
      (continuous_fst.prodMk
        ((orderFourAffineMappingTorusLiftProjection A.periods).continuous.comp continuous_snd))

/-- The analytic order-three filling is the exact order-three piece of the actual cover. -/
public noncomputable def orderThreeFillingToActualPieceHomeomorph :
    A.OrderThreeVaryingFilling A.starSeparation.orderThree.radius ≃ₜ
      A.actualVanKampenFourPieceCover.ellipticThree := by
  change A.openEmbeddingStarData.filling 1 ≃ₜ
    (A.openEmbeddingStarData.sectionSevenEulerCover).piece 2
  exact
    A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 1

/-- The analytic order-four filling is the exact order-four piece of the actual cover. -/
public noncomputable def orderFourFillingToActualPieceHomeomorph :
    A.OrderFourVaryingFilling A.starSeparation.orderFour.radius ≃ₜ
      A.actualVanKampenFourPieceCover.ellipticFour := by
  change A.openEmbeddingStarData.filling 2 ≃ₜ
    (A.openEmbeddingStarData.sectionSevenEulerCover).piece 3
  exact
    A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 2

/-- Inclusion of the actual order-three overlap into its filling piece is the original star
collar-to-filling map in the canonical source and target coordinates. -/
public theorem orderThreeCollarToActualOverlap_toPiece
    (x : A.openEmbeddingStarData.collarSource 1) :
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
        (A.orderThreeCollarToActualOverlapHomeomorph x) =
      A.orderThreeFillingToActualPieceHomeomorph (A.starToFilling 1 x) := by
  apply Subtype.ext
  change
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      none (A.openEmbeddingStarData.toCentral 1 x) =
    A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι
      (some 1) (A.openEmbeddingStarData.toFilling 1 x)
  symm
  apply (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
    (some 1) none (A.openEmbeddingStarData.toFilling 1 x)
      (A.openEmbeddingStarData.toCentral 1 x)).mpr
  exact ⟨A.openEmbeddingStarData.fillingCollarPoint 1 x, rfl, by
    change ((A.openEmbeddingStarData.collarEquiv 1).symm
      (A.openEmbeddingStarData.fillingCollarPoint 1 x)).1 =
        A.openEmbeddingStarData.toCentral 1 x
    rw [A.openEmbeddingStarData.collarEquiv_symm_toFilling]
    rfl⟩

/-- The explicit candidate universal-cover projection of the actual order-three filling. -/
public noncomputable def ellipticThreeFillingProjection :
    C(ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace,
      A.actualVanKampenFourPieceCover.ellipticThree) where
  toFun q := A.orderThreeFillingToActualPieceHomeomorph
    (A.ellipticThreeFillingCoverProjection A.starSeparation.orderThree.radius q)
  continuous_toFun := A.orderThreeFillingToActualPieceHomeomorph.continuous.comp
    (A.ellipticThreeFillingCoverProjection A.starSeparation.orderThree.radius).continuous

/-- The explicit candidate universal-cover projection of the actual order-four filling. -/
public noncomputable def ellipticFourFillingProjection :
    C(ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace,
      A.actualVanKampenFourPieceCover.ellipticFour) where
  toFun q := A.orderFourFillingToActualPieceHomeomorph
    (A.ellipticFourFillingCoverProjection A.starSeparation.orderFour.radius q)
  continuous_toFun := A.orderFourFillingToActualPieceHomeomorph.continuous.comp
    (A.ellipticFourFillingCoverProjection A.starSeparation.orderFour.radius).continuous



/-- The explicit order-three lift from radial universal-cover coordinates to the vector-bundle
cover of the filling.  The fixed-to-moving real-period gauge converts the constant fibre
coordinate used by the mapping torus into the varying period coordinate used by the filling. -/
public noncomputable def ellipticThreeRadialFillingLift :
    C(OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace),
      ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace) where
  toFun q :=
    let u := angularCover (T := ComplexTwoSpace) 3
      A.starSeparation.orderThree.radius_lt_one.le q
    (⟨u.1.1, u.2.2⟩,
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (orderThreeCayleyHomeomorph.symm u.1.1, u.1.2)).2)
  continuous_toFun := by
    let hangular := continuous_angularCover (T := ComplexTwoSpace) 3
      A.starSeparation.orderThree.radius_lt_one.le
    let d : OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace) →
        ComplexDiscBall A.starSeparation.orderThree.radius := fun q =>
      let u := angularCover (T := ComplexTwoSpace) 3
        A.starSeparation.orderThree.radius_lt_one.le q
      ⟨u.1.1, u.2.2⟩
    have hd : Continuous d :=
      Continuous.subtype_mk
        ((continuous_subtype_val.comp hangular).fst) _
    let v : OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace) → UpperHalfPlane × ComplexTwoSpace := fun q =>
      let u := angularCover (T := ComplexTwoSpace) 3
        A.starSeparation.orderThree.radius_lt_one.le q
      (orderThreeCayleyHomeomorph.symm u.1.1, u.1.2)
    have hv : Continuous v :=
      (orderThreeCayleyHomeomorph.symm.continuous.comp
        ((continuous_subtype_val.comp hangular).fst)).prodMk
          ((continuous_subtype_val.comp hangular).snd)
    have hmoving : Continuous (fun q =>
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne (v q)).2) :=
      continuous_snd.comp
        ((fixedToMovingCover_continuous A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne).comp hv)
    exact hd.prodMk hmoving

@[simp]
public theorem ellipticThreeRadialFillingLift_fst
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    (A.ellipticThreeRadialFillingLift q).1.1 =
      (angularCover (T := ComplexTwoSpace) 3
        A.starSeparation.orderThree.radius_lt_one.le q).1.1 :=
  rfl

@[simp]
public theorem ellipticThreeRadialFillingLift_snd
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    (A.ellipticThreeRadialFillingLift q).2 =
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne
        (orderThreeCayleyHomeomorph.symm
          (angularCover (T := ComplexTwoSpace) 3
            A.starSeparation.orderThree.radius_lt_one.le q).1.1,
          (angularCover (T := ComplexTwoSpace) 3
            A.starSeparation.orderThree.radius_lt_one.le q).1.2)).2 :=
  rfl

/-- In the fixed real-period product chart, the explicit lift is exactly the angular cover and
the original vector-cover coordinate. -/
public theorem orderThreeFillingProductMap_actualEllipticRadialFillingLift
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    orderThreeFillingProductMap A A.starSeparation.orderThree.radius
        (A.orderThreeFillingCoverMap A.starSeparation.orderThree.radius
          (A.ellipticThreeRadialFillingLift q)) =
      ((angularCover (T := ComplexTwoSpace) 3
          A.starSeparation.orderThree.radius_lt_one.le q).1.1,
        Quotient.mk _ q.2.2) := by
  rw [orderThreeFillingProductMap]
  rw [orderThreeFillingCoverMap.eq_def]
  rw [orderThreeRealPeriodProductHomeomorph_mk]
  rw [A.ellipticThreeRadialFillingLift_fst,
    A.ellipticThreeRadialFillingLift_snd]
  rw [orderThreeCayleyHomeomorph.apply_symm_apply]
  let u := angularCover (T := ComplexTwoSpace) 3
    A.starSeparation.orderThree.radius_lt_one.le q
  let p : UpperHalfPlane × ComplexTwoSpace :=
    (orderThreeCayleyHomeomorph.symm u.1.1, u.1.2)
  have hp : (orderThreeCayleyHomeomorph.symm u.1.1,
      (fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne p).2) =
      fixedToMovingCover A.periods
        A.modular.modularParameter.toTriangleUniformization.zOne p := by
    apply Prod.ext <;> rfl
  change (u.1.1, Quotient.mk _ (movingToFixedCover A.periods
    A.modular.modularParameter.toTriangleUniformization.zOne
      (orderThreeCayleyHomeomorph.symm u.1.1,
        (fixedToMovingCover A.periods
          A.modular.modularParameter.toTriangleUniformization.zOne p).2)).2) =
    (u.1.1, Quotient.mk _ q.2.2)
  rw [hp, movingToFixedCover_fixedToMovingCover]
  rfl

/-- The angular quotient homeomorphism sends the explicit angular lift to the affine
mapping-torus projection of the same real/vector coordinate. -/
public theorem orderThreeAngularQuotientHomeomorph_apply
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    let D := orderThreeCyclicPuncturedProductData A.periods
      A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one
    let w : OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × A.OrderThreeTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  CyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
        CyclicAngularFundamentalDomain.orderThreeMultiplier_eq_standardMultiplier
        (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) =
      (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2) := by
  dsimp only
  let D := orderThreeCyclicPuncturedProductData A.periods
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let w : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × A.OrderThreeTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  let hgen := CyclicAngularFundamentalDomain.isStandardGenerator_of_multiplier_eq
    D.action D.clutching D.multiplier D.multiplier_norm
      CyclicAngularFundamentalDomain.orderThreeMultiplier_eq_standardMultiplier
      D.generator_formula
  let hf := isQuotientMap_angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl
    D.action_continuous
  let hg := isQuotientMap_radialTorusMap
    (r := A.starSeparation.orderThree.radius) D.clutching
  let heq := angularQuotientMap_eq_iff D.action D.clutching D.radius_lt_one.le D.carrier
    rfl hgen
  change ((Homeomorph.refl (OpenRadialInterval A.starSeparation.orderThree.radius)).prodCongr
      (realMappingTorusHomeomorph _))
    (CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
      hf hg heq
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w)) = _
  have happly : CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps hf hg heq
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) =
      radialTorusMap D.clutching w :=
    (heq _ _).mp
      (Function.surjInv_eq hf.surjective
        (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w))
  rw [happly]
  rfl

/-- The explicit order-three radial lift commutes with the collar inclusion into the actual
filling piece. -/
public theorem ellipticThreeRadialFillingLift_commutes
    (q : OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace)) :
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
        (A.ellipticThreeBoundaryProjection q) =
      A.ellipticThreeFillingProjection
        (A.ellipticThreeRadialFillingLift q) := by
  rw [ellipticThreeBoundaryProjection]
  rw [ellipticThreeFillingProjection]
  let x : A.openEmbeddingStarData.collarSource 1 :=
    A.orderThreeCollarRadialMappingTorusHomeomorph.symm
      (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2)
  change A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
      (A.orderThreeCollarToActualOverlapHomeomorph x) =
    A.orderThreeFillingToActualPieceHomeomorph
      (A.ellipticThreeFillingCoverProjection A.starSeparation.orderThree.radius
        (A.ellipticThreeRadialFillingLift q))
  rw [A.orderThreeCollarToActualOverlap_toPiece x]
  apply congrArg A.orderThreeFillingToActualPieceHomeomorph
  let xq : A.StarCollarSource 1 :=
    A.orderThreeCollarRadialMappingTorusHomeomorph.symm
      (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2)
  change A.starToFilling 1 xq =
    A.ellipticThreeFillingCoverProjection A.starSeparation.orderThree.radius
      (A.ellipticThreeRadialFillingLift q)
  let D := orderThreeCyclicPuncturedProductData A.periods
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let e := orderThreePuncturedProductEquivariantHomeomorph A.periods
    A.modular.modularParameter.toTriangleUniformization_sourceAction
    A.starSeparation.orderThree.radius A.starSeparation.orderThree.radius_pos
    A.starSeparation.orderThree.radius_lt_one
  let hprod := EquivariantQuotientHomeomorph.restrictedOrbitQuotientHomeomorph e
  let hang := CyclicAngularFundamentalDomain.quotientHomeomorphRadialMappingTorus D
    CyclicAngularFundamentalDomain.orderThreeMultiplier_eq_standardMultiplier
  let w : OpenRadialInterval A.starSeparation.orderThree.radius ×
      (ℝ × A.OrderThreeTorus) := (q.1, q.2.1, Quotient.mk _ q.2.2)
  have hxprod : hprod xq =
      angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w := by
    apply hang.injective
    change A.orderThreeCollarRadialMappingTorusHomeomorph xq =
      hang (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w)
    rw [show A.orderThreeCollarRadialMappingTorusHomeomorph xq =
        (q.1, orderThreeAffineMappingTorusLiftProjection A.periods q.2) from
      A.orderThreeCollarRadialMappingTorusHomeomorph.apply_symm_apply _,
      A.orderThreeAngularQuotientHomeomorph_apply q]
  have hxx : xq = hprod.symm
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) := by
    rw [← hxprod]
    exact (hprod.symm_apply_apply xq).symm
  rw [hxx]
  let y : D.carrier.carrier :=
    (Homeomorph.setCongr (show D.carrier.carrier =
      puncturedProduct A.OrderThreeTorus A.starSeparation.orderThree.radius from rfl)).symm
      (angularCover (T := A.OrderThreeTorus) 3 D.radius_lt_one.le w)
  let s := e.toHomeomorph.symm y
  have hinv : hprod.symm
      (angularQuotientMap D.action D.radius_lt_one.le D.carrier rfl w) =
      Quotient.mk _ s := by
    apply hprod.injective
    rw [hprod.apply_symm_apply]
    change Quotient.mk _ y = hprod (Quotient.mk _ s)
    rw [EquivariantQuotientHomeomorph.restrictedOrbitQuotientHomeomorph_mk]
    rw [show e.toHomeomorph s = y from e.toHomeomorph.apply_symm_apply y]
  rw [hinv]
  change A.orderThreePuncturedCollarToFilling A.starSeparation.orderThree.radius
      (Quotient.mk _ s) =
    A.ellipticThreeFillingCoverProjection A.starSeparation.orderThree.radius
      (A.ellipticThreeRadialFillingLift q)
  rw [A.orderThreePuncturedCollarToFilling_mk]
  rw [ellipticThreeFillingCoverProjection]
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply (orderThreeRealPeriodProductHomeomorph A.periods).injective
  change (e.toHomeomorph s).1 =
    orderThreeFillingProductMap A A.starSeparation.orderThree.radius
      (A.orderThreeFillingCoverMap A.starSeparation.orderThree.radius
        (A.ellipticThreeRadialFillingLift q))
  rw [show e.toHomeomorph s = y from e.toHomeomorph.apply_symm_apply y]
  rw [A.orderThreeFillingProductMap_actualEllipticRadialFillingLift q]
  rfl

/-- The semidirect deck action on the explicit radial cover of the actual order-three overlap. -/
@[instance_reducible] public noncomputable def ellipticThreeBoundaryAction :
    MulAction (OrderThreeAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  exact passiveProdAction _ _ _

/-- The semidirect deck action on the explicit radial cover of the actual order-four overlap. -/
@[instance_reducible] public noncomputable def ellipticFourBoundaryAction :
    MulAction (OrderFourAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  exact passiveProdAction _ _ _

/-- The exact actual order-three overlap is the quotient by its explicit semidirect deck action. -/
public theorem ellipticThreeBoundaryProjection_isQuotientCoveringMap :
    letI := A.ellipticThreeBoundaryAction
    IsQuotientCoveringMap A.ellipticThreeBoundaryProjection
      (OrderThreeAffineMappingTorusDeck A.periods) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticThreeBoundaryAction
  have hprod := passiveProd_isQuotientCoveringMap
    (R := OpenRadialInterval A.starSeparation.orderThree.radius)
    (orderThreeAffineMappingTorusLiftProjection_isQuotientCoveringMap A.periods)
  have h := hprod.homeomorph_comp
    A.orderThreeRadialMappingTorusToActualOverlapHomeomorph
  exact h

/-- The exact actual order-four overlap is the quotient by its explicit semidirect deck action. -/
public theorem ellipticFourBoundaryProjection_isQuotientCoveringMap :
    letI := A.ellipticFourBoundaryAction
    IsQuotientCoveringMap A.ellipticFourBoundaryProjection
      (OrderFourAffineMappingTorusDeck A.periods) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.ellipticFourBoundaryAction
  have hprod := passiveProd_isQuotientCoveringMap
    (R := OpenRadialInterval A.starSeparation.orderFour.radius)
    (orderFourAffineMappingTorusLiftProjection_isQuotientCoveringMap A.periods)
  have h := hprod.homeomorph_comp
    A.orderFourRadialMappingTorusToActualOverlapHomeomorph
  exact h

/-- A canonical choice of lift of the marked order-three overlap point to the explicit radial
cover. -/
public noncomputable def ellipticThreeBoundaryBase :
    OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace) := by
  let _ := A.ellipticThreeBoundaryAction
  exact Classical.choose
    (A.ellipticThreeBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)

/-- The selected order-three radial base projects to the marked overlap point. -/
public theorem ellipticThreeBoundaryProjection_base :
    A.ellipticThreeBoundaryProjection A.ellipticThreeBoundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ := by
  let _ := A.ellipticThreeBoundaryAction
  exact Classical.choose_spec
    (A.ellipticThreeBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)

/-- A canonical choice of lift of the marked order-four overlap point to the explicit radial
cover. -/
public noncomputable def ellipticFourBoundaryBase :
    OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace) := by
  let _ := A.ellipticFourBoundaryAction
  exact Classical.choose
    (A.ellipticFourBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)

/-- The selected order-four radial base projects to the marked overlap point. -/
public theorem ellipticFourBoundaryProjection_base :
    A.ellipticFourBoundaryProjection A.ellipticFourBoundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ := by
  let _ := A.ellipticFourBoundaryAction
  exact Classical.choose_spec
    (A.ellipticFourBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)

/-- The explicit radial source of the actual order-three overlap cover is simply connected. -/
public theorem ellipticThreeBoundaryCover_simplyConnected :
    SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ : ContractibleSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius) :=
    (convex_Ioo (0 : ℝ) A.starSeparation.orderThree.radius).contractibleSpace
      (Set.nonempty_Ioo.mpr A.starSeparation.orderThree.radius_pos)
  infer_instance

/-- The explicit radial source of the actual order-four overlap cover is simply connected. -/
public theorem ellipticFourBoundaryCover_simplyConnected :
    SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ : ContractibleSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius) :=
    (convex_Ioo (0 : ℝ) A.starSeparation.orderFour.radius).contractibleSpace
      (Set.nonempty_Ioo.mpr A.starSeparation.orderFour.radius_pos)
  infer_instance

/-- Canonical inverse-meridian boundary deck data for the actual order-three collar. -/
@[expose] public noncomputable def ellipticThreeBoundaryDeckData :
    UnwrappedCyclicAffineBoundaryDeckData 3 Lattice
      (OrderThreeAffineMappingTorusDeck A.periods) where
  translation := affineTorusMappingTorusDeckTranslation
    (orderThreeDescendedAffineTorusAutomorphism A.periods)
  translation_injective := affineTorusMappingTorusDeckTranslation_injective _
  meridian := (affineTorusMappingTorusDeckMeridian
    (orderThreeDescendedAffineTorusAutomorphism A.periods))⁻¹
  monodromy := Multiplicative.ofAdd
    (orderThreeDescendedAffineTorusAutomorphism A.periods).latticeMap.symm.toAddEquiv
  conjugate := affineTorusMappingTorusDeck_inverseMeridian_conjugate _
  generators_generate :=
    affineTorusMappingTorusDeck_inverseMeridian_generators_generate _
  twist := -epsilon
  monodromy_pow := by
    change (Multiplicative.ofAdd (rhoLambda g₁).symm.toAddEquiv) ^ 3 = 1
    apply Multiplicative.toAdd.injective
    simp
    apply AddEquiv.ext
    intro x
    change a₁.symm (a₁.symm (a₁.symm x)) = x
    apply a₁.injective
    rw [a₁.apply_symm_apply]
    apply a₁.injective
    rw [a₁.apply_symm_apply]
    apply a₁.injective
    rw [a₁.apply_symm_apply]
    have h := congrArg (fun f : DualLattice ≃ₗ[ℤ] DualLattice ↦ f x) a₁_pow_three
    simpa [pow_succ] using h.symm
  twist_fixed := by
    change (rhoLambda g₁).symm (-epsilon) = -epsilon
    apply (rhoLambda g₁).injective
    rw [(rhoLambda g₁).apply_symm_apply, map_neg, rhoLambda_g₁_apply, A₁_epsilon]

/-- Canonical inverse-meridian boundary deck data for the actual order-four collar. -/
@[expose] public noncomputable def ellipticFourBoundaryDeckData :
    UnwrappedCyclicAffineBoundaryDeckData 4 Lattice
      (OrderFourAffineMappingTorusDeck A.periods) where
  translation := affineTorusMappingTorusDeckTranslation
    (orderFourDescendedAffineTorusAutomorphism A.periods)
  translation_injective := affineTorusMappingTorusDeckTranslation_injective _
  meridian := (affineTorusMappingTorusDeckMeridian
    (orderFourDescendedAffineTorusAutomorphism A.periods))⁻¹
  monodromy := Multiplicative.ofAdd
    (orderFourDescendedAffineTorusAutomorphism A.periods).latticeMap.symm.toAddEquiv
  conjugate := affineTorusMappingTorusDeck_inverseMeridian_conjugate _
  generators_generate :=
    affineTorusMappingTorusDeck_inverseMeridian_generators_generate _
  twist := epsilon'
  monodromy_pow := by
    change (Multiplicative.ofAdd (rhoLambda g₂).symm.toAddEquiv) ^ 4 = 1
    apply Multiplicative.toAdd.injective
    simp
    apply AddEquiv.ext
    intro x
    change a₂.symm (a₂.symm (a₂.symm (a₂.symm x))) = x
    apply a₂.injective
    rw [a₂.apply_symm_apply]
    apply a₂.injective
    rw [a₂.apply_symm_apply]
    apply a₂.injective
    rw [a₂.apply_symm_apply]
    apply a₂.injective
    rw [a₂.apply_symm_apply]
    have h := congrArg (fun f : DualLattice ≃ₗ[ℤ] DualLattice ↦ f x) a₂_pow_four
    simpa [pow_succ] using h.symm
  twist_fixed := by
    change (rhoLambda g₂).symm epsilon' = epsilon'
    apply (rhoLambda g₂).injective
    rw [(rhoLambda g₂).apply_symm_apply, rhoLambda_g₂_apply, A₂_epsilon']

/-- Order-three filling geometry with lift equivariance specified only at the marked lift. -/
public structure OrderThreeActualEllipticFillingExtensionAtBase where
  fillingAction : MulAction A.ellipticThreeBoundaryDeckData.FillingDeck
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
  fillingQuotient : @IsQuotientCoveringMap
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
    A.actualVanKampenFourPieceCover.ellipticThree _ _
    A.ellipticThreeFillingProjection
    A.ellipticThreeBoundaryDeckData.FillingDeck _ fillingAction
  lift : C(OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace),
    ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
  commutes : ∀ z,
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
        (A.ellipticThreeBoundaryProjection z) =
      A.ellipticThreeFillingProjection (lift z)
  equivariant_at_boundaryBase : ∀ g,
    lift (@SMul.smul _ _ A.ellipticThreeBoundaryAction.toSMul g
      A.ellipticThreeBoundaryBase) =
      @SMul.smul _ _ fillingAction.toSMul
        (A.ellipticThreeBoundaryDeckData.fillingDeckMap g)
        (lift A.ellipticThreeBoundaryBase)

/-- Order-four filling geometry with lift equivariance specified only at the marked lift. -/
public structure OrderFourActualEllipticFillingExtensionAtBase where
  fillingAction : MulAction A.ellipticFourBoundaryDeckData.FillingDeck
    (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
  fillingQuotient : @IsQuotientCoveringMap
    (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
    A.actualVanKampenFourPieceCover.ellipticFour _ _
    A.ellipticFourFillingProjection
    A.ellipticFourBoundaryDeckData.FillingDeck _ fillingAction
  lift : C(OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace),
    ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
  commutes : ∀ z,
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
        (A.ellipticFourBoundaryProjection z) =
      A.ellipticFourFillingProjection (lift z)
  equivariant_at_boundaryBase : ∀ g,
    lift (@SMul.smul _ _ A.ellipticFourBoundaryAction.toSMul g
      A.ellipticFourBoundaryBase) =
      @SMul.smul _ _ fillingAction.toSMul
        (A.ellipticFourBoundaryDeckData.fillingDeckMap g)
        (lift A.ellipticFourBoundaryBase)

/-- The order-three filling-deck action and the assertion that its orbit map is the already
defined actual filling projection. -/
public structure OrderThreeActualEllipticFillingQuotientData where
  fillingAction : MulAction A.ellipticThreeBoundaryDeckData.FillingDeck
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
  fillingQuotient : @IsQuotientCoveringMap
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
    A.actualVanKampenFourPieceCover.ellipticThree _ _
    A.ellipticThreeFillingProjection
    A.ellipticThreeBoundaryDeckData.FillingDeck _ fillingAction

/-- The unresolved order-three deck marking after fixing the canonical radial filling lift. -/
public structure OrderThreeActualEllipticFillingMarkedDeckData extends
    A.OrderThreeActualEllipticFillingQuotientData where
  equivariant_at_boundaryBase : ∀ g,
    A.ellipticThreeRadialFillingLift
        (@SMul.smul _ _ A.ellipticThreeBoundaryAction.toSMul g
          A.ellipticThreeBoundaryBase) =
      @SMul.smul _ _ fillingAction.toSMul
        (A.ellipticThreeBoundaryDeckData.fillingDeckMap g)
        (A.ellipticThreeRadialFillingLift
          A.ellipticThreeBoundaryBase)

namespace OrderThreeActualEllipticFillingMarkedDeckData

/-- The canonical radial lift and its proved commuting square complete the order-three marked
deck data to the former filling-extension interface. -/
public noncomputable def toExtensionAtBase
    (D : A.OrderThreeActualEllipticFillingMarkedDeckData) :
    A.OrderThreeActualEllipticFillingExtensionAtBase where
  fillingAction := D.fillingAction
  fillingQuotient := D.fillingQuotient
  lift := A.ellipticThreeRadialFillingLift
  commutes := A.ellipticThreeRadialFillingLift_commutes
  equivariant_at_boundaryBase := D.equivariant_at_boundaryBase

end OrderThreeActualEllipticFillingMarkedDeckData

namespace OrderThreeActualEllipticFillingExtensionAtBase

/-- Equivariance at the marked point extends over the connected collar cover. -/
public theorem lift_equivariant
    (E : A.OrderThreeActualEllipticFillingExtensionAtBase) :
    ∀ g z,
      E.lift (@SMul.smul _ _ A.ellipticThreeBoundaryAction.toSMul g z) =
        @SMul.smul _ _ E.fillingAction.toSMul
          (A.ellipticThreeBoundaryDeckData.fillingDeckMap g) (E.lift z) := by
  letI := A.ellipticThreeBoundaryAction
  letI := E.fillingAction
  letI := A.ellipticThreeBoundaryCover_simplyConnected
  exact SphereSixComplex.Topology.quotientCover_equivariant_of_eq_at
    A.ellipticThreeBoundaryProjection
    A.ellipticThreeFillingProjection
    A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
    E.fillingQuotient
    A.ellipticThreeBoundaryDeckData.fillingDeckMap
    E.lift
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
    E.commutes
    A.ellipticThreeBoundaryBase
    E.equivariant_at_boundaryBase

end OrderThreeActualEllipticFillingExtensionAtBase

namespace OrderFourActualEllipticFillingExtensionAtBase

/-- Equivariance at the marked point extends over the connected collar cover. -/
public theorem lift_equivariant
    (E : A.OrderFourActualEllipticFillingExtensionAtBase) :
    ∀ g z,
      E.lift (@SMul.smul _ _ A.ellipticFourBoundaryAction.toSMul g z) =
        @SMul.smul _ _ E.fillingAction.toSMul
          (A.ellipticFourBoundaryDeckData.fillingDeckMap g) (E.lift z) := by
  letI := A.ellipticFourBoundaryAction
  letI := E.fillingAction
  letI := A.ellipticFourBoundaryCover_simplyConnected
  exact SphereSixComplex.Topology.quotientCover_equivariant_of_eq_at
    A.ellipticFourBoundaryProjection
    A.ellipticFourFillingProjection
    A.ellipticFourBoundaryProjection_isQuotientCoveringMap
    E.fillingQuotient
    A.ellipticFourBoundaryDeckData.fillingDeckMap
    E.lift
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
    E.commutes
    A.ellipticFourBoundaryBase
    E.equivariant_at_boundaryBase

end OrderFourActualEllipticFillingExtensionAtBase

namespace OrderThreeActualEllipticFillingExtensionAtBase

/-- Assemble the complete chosen order-three filling-cover model from only the filling
extension. -/
public noncomputable def toChosenCover
    (E : A.OrderThreeActualEllipticFillingExtensionAtBase) :
    ChosenCyclicAffineFillingCoverModel 3 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree := by
  letI := A.ellipticThreeBoundaryAction
  letI := E.fillingAction
  let U : UnwrappedCyclicAffineFillingCover 3 Lattice
      (OrderThreeAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace))
      (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree
      A.ellipticThreeBoundaryDeckData := {
    boundaryProjection := A.ellipticThreeBoundaryProjection
    fillingProjection := A.ellipticThreeFillingProjection
    boundaryQuotient := A.ellipticThreeBoundaryProjection_isQuotientCoveringMap
    fillingQuotient := E.fillingQuotient
    boundarySimplyConnected := A.ellipticThreeBoundaryCover_simplyConnected
    fillingSimplyConnected := orderThreeFillingCoverSource_simplyConnected
      A.starSeparation.orderThree.radius_pos A.starSeparation.orderThree.radius_lt_one
    lift := E.lift
    baseMap := A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
    commutes := E.commutes
    equivariant := E.lift_equivariant
    base := A.ellipticThreeBoundaryBase }
  exact
    { BoundaryDeck := OrderThreeAffineMappingTorusDeck A.periods
      FillingDeck := A.ellipticThreeBoundaryDeckData.FillingDeck
      BoundaryCover := OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)
      FillingCover := ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace
      boundaryDeckGroup := inferInstance
      fillingDeckGroup := inferInstance
      boundaryCoverTopology := inferInstance
      fillingCoverTopology := inferInstance
      boundaryAction := A.ellipticThreeBoundaryAction
      fillingAction := E.fillingAction
      model := U.toCyclicAffineFillingCoverModel }

/-- The chosen order-three cover is based at the marked overlap point. -/
public theorem toChosenCover_boundaryBase_eq
    (E : A.OrderThreeActualEllipticFillingExtensionAtBase) :
    E.toChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  A.ellipticThreeBoundaryProjection_base

/-- The chosen order-three filling base is the marked filling point. -/
public theorem toChosenCover_fillingBase_eq
    (E : A.OrderThreeActualEllipticFillingExtensionAtBase) :
    E.toChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩ := by
  change A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
      (A.ellipticThreeBoundaryProjection
        A.ellipticThreeBoundaryBase) = _
  rw [A.ellipticThreeBoundaryProjection_base]
  rfl

end OrderThreeActualEllipticFillingExtensionAtBase

namespace OrderFourActualEllipticFillingExtensionAtBase

/-- Assemble the complete chosen order-four filling-cover model from only the filling
extension. -/
public noncomputable def toChosenCover
    (E : A.OrderFourActualEllipticFillingExtensionAtBase) :
    ChosenCyclicAffineFillingCoverModel 4 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour := by
  letI := A.ellipticFourBoundaryAction
  letI := E.fillingAction
  let U : UnwrappedCyclicAffineFillingCover 4 Lattice
      (OrderFourAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace))
      (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour
      A.ellipticFourBoundaryDeckData := {
    boundaryProjection := A.ellipticFourBoundaryProjection
    fillingProjection := A.ellipticFourFillingProjection
    boundaryQuotient := A.ellipticFourBoundaryProjection_isQuotientCoveringMap
    fillingQuotient := E.fillingQuotient
    boundarySimplyConnected := A.ellipticFourBoundaryCover_simplyConnected
    fillingSimplyConnected := orderFourFillingCoverSource_simplyConnected
      A.starSeparation.orderFour.radius_pos A.starSeparation.orderFour.radius_lt_one
    lift := E.lift
    baseMap := A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
    commutes := E.commutes
    equivariant := E.lift_equivariant
    base := A.ellipticFourBoundaryBase }
  exact
    { BoundaryDeck := OrderFourAffineMappingTorusDeck A.periods
      FillingDeck := A.ellipticFourBoundaryDeckData.FillingDeck
      BoundaryCover := OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)
      FillingCover := ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace
      boundaryDeckGroup := inferInstance
      fillingDeckGroup := inferInstance
      boundaryCoverTopology := inferInstance
      fillingCoverTopology := inferInstance
      boundaryAction := A.ellipticFourBoundaryAction
      fillingAction := E.fillingAction
      model := U.toCyclicAffineFillingCoverModel }

/-- The chosen order-four cover is based at the marked overlap point. -/
public theorem toChosenCover_boundaryBase_eq
    (E : A.OrderFourActualEllipticFillingExtensionAtBase) :
    E.toChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  A.ellipticFourBoundaryProjection_base

/-- The chosen order-four filling base is the marked filling point. -/
public theorem toChosenCover_fillingBase_eq
    (E : A.OrderFourActualEllipticFillingExtensionAtBase) :
    E.toChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩ := by
  change A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
      (A.ellipticFourBoundaryProjection
        A.ellipticFourBoundaryBase) = _
  rw [A.ellipticFourBoundaryProjection_base]
  rfl

end OrderFourActualEllipticFillingExtensionAtBase

/-- The actual order-three overlap included into the core and transported along the specified
connector to the base point of the four-piece cover. -/
public noncomputable def ellipticThreeOverlapToCore :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
          A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ →*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticThreeConnector
        A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.1).symm).toMonoidHom.comp
    (FundamentalGroup.map
      (A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticThree)
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)

/-- The actual order-four overlap included into the core and transported along the specified
connector to the base point of the four-piece cover. -/
public noncomputable def ellipticFourOverlapToCore :
    FundamentalGroup
        (A.actualVanKampenFourPieceCover.core ∩
          A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
        ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
          A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ →*
      FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩ :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (A.actualVanKampenFourPieceCover.connectorInCore
        A.actualVanKampenFourPieceCover.ellipticFourConnector
        A.actualVanKampenFourPieceCover.ellipticFourConnector_mem
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.1).symm).toMonoidHom.comp
    (FundamentalGroup.map
      (A.actualVanKampenFourPieceCover.overlapToCore
        A.actualVanKampenFourPieceCover.ellipticFour)
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)

/-- The actual overlap-to-core map gives the order-three square of the affine star bridge. -/
public theorem ellipticThreeAffineBridge_square :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.ellipticThreeOverlapToCore =
      A.actualVanKampenFourPieceCover.ellipticThreeFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  ext γ
  exact coreSquare_apply A.actualVanKampenFourPieceCover
    A.actualVanKampenFourPieceCover.ellipticThree
    A.actualVanKampenFourPieceCover.ellipticThreePoint_mem
    A.actualVanKampenFourPieceCover.ellipticThreeConnector
    A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem γ

/-- The actual overlap-to-core map gives the order-four square of the affine star bridge. -/
public theorem ellipticFourAffineBridge_square :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.ellipticFourOverlapToCore =
      A.actualVanKampenFourPieceCover.ellipticFourFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  ext γ
  exact coreSquare_apply A.actualVanKampenFourPieceCover
    A.actualVanKampenFourPieceCover.ellipticFour
    A.actualVanKampenFourPieceCover.ellipticFourPoint_mem
    A.actualVanKampenFourPieceCover.ellipticFourConnector
    A.actualVanKampenFourPieceCover.ellipticFourConnector_mem γ
/-- The central affine presentation transported through a marked cusp naturality equivalence. -/
public noncomputable def coreDataOf (N : A.CuspCentralNaturality) :
    AffineTorusCorePiOneData
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
      Lattice paperMonodromyOne paperMonodromyTwo :=
  A.centralAffineCorePiOneData.mapSurjective N.centralToCore.toMonoidHom
    N.centralToCore.surjective

/-- Every marked cusp translation maps to the corresponding transported core translation. -/
public theorem cuspBridge_translation_core (N : A.CuspCentralNaturality) (a : Lattice) :
    A.cuspOverlapToCore
        (Additive.toMul (A.cuspAffineBridgeTranslation a)) =
      Additive.toMul ((A.coreDataOf N).translation a) :=
  N.translation_core a

/-- At cusp twist zero, the marked cusp meridian maps to the product of the two core meridians. -/
public theorem cuspBridge_meridian_core (N : A.CuspCentralNaturality) :
    A.cuspOverlapToCore A.cuspAffineBridgeMeridian =
      (A.coreDataOf N).rhoOne * (A.coreDataOf N).rhoTwo *
        (Additive.toMul ((A.coreDataOf N).translation 0))⁻¹ := by
  apply Eq.trans N.meridian_core
  change
    N.centralToCore A.centralAffineCorePiOneData.rhoOne *
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo =
    N.centralToCore A.centralAffineCorePiOneData.rhoOne *
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo *
      (N.centralToCore
        (Additive.toMul (A.centralAffineCorePiOneData.translation 0)))⁻¹
  have hz : Additive.toMul (A.centralAffineCorePiOneData.translation 0) = 1 := by
    rw [map_zero]
    rfl
  rw [hz, map_one, inv_one, mul_one]











/-- The central-family translations, transported to the central core. -/
public noncomputable def actualCentralTranslationToCore
    (N : A.CuspCentralNaturality) :
    Lattice →+ Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :=
  N.centralToCore.toMonoidHom.toAdditive.comp A.centralAffineCorePiOneData.translation






end SphereSixComplex.Geometry.AnalyticData

end
