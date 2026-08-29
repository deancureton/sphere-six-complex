module

public import SphereSixComplex.Topology.PaperActualAffineFillingCoverModelsDefs
public import SphereSixComplex.Topology.PaperCuspAffineFillingBridge
public import SphereSixComplex.Topology.AffineRealMappingTorusUniversalCover
public import SphereSixComplex.Topology.PaperEllipticFundamentalGroupSurjectivity
public import SphereSixComplex.Topology.QuotientCoverEquivarianceExtension

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
`ActualCuspCentralNaturality`, extended by the two chosen cyclic regular-cover models.

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
        (FundamentalGroup.map (subsetInclusion P) ⟨pt, hpt.2⟩
          (FundamentalGroup.map
            (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z.1, z.2.2⟩ : P), by fun_prop⟩ :
              C((D.core ∩ P : Set Y), P)) ⟨pt, hpt⟩ γ)) := by
  set connCore := D.connectorInCore conn hconn hpt.1
  have hnat := map_fundamentalGroupMulEquivOfPath (subsetInclusion D.core) connCore.symm
    (FundamentalGroup.map (D.overlapToCore P) ⟨pt, hpt⟩ γ)
  have hpath : connCore.symm.map (subsetInclusion D.core).continuous = conn.symm := by
    ext t
    rfl
  change FundamentalGroup.map (subsetInclusion D.core) _
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath connCore.symm) _) =
    (FundamentalGroup.fundamentalGroupMulEquivOfPath conn.symm) _
  apply Eq.trans hnat
  rw [hpath]
  congr 1
  have h1 := map_map (D.overlapToCore P) (subsetInclusion D.core) ⟨pt, hpt⟩ γ
  have h2 := map_map
    (⟨fun z : (D.core ∩ P : Set Y) ↦ (⟨z.1, z.2.2⟩ : P), by fun_prop⟩ :
      C((D.core ∩ P : Set Y), P)) (subsetInclusion P) ⟨pt, hpt⟩ γ
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

namespace SphereSixComplex.Geometry.PaperAnalyticData

open SphereSixComplex.LatticeData SphereSixComplex.Topology
open SphereSixComplex.Topology.PaperVanKampenFourPieceCover
open SphereSixComplex.CyclicAngularFundamentalDomain
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.EllipticFamilySpecialization

variable (A : PaperAnalyticData)

/-- The analytic order-three collar source, identified with the exact overlap in the actual
four-piece cover. -/
public noncomputable def orderThreeCollarToActualOverlapHomeomorph :
    A.starCollarSourceType 1 ≃ₜ
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace) := by
  refine
    (A.openEmbeddingStarData.centralFillingIntersectionHomeomorph 1).trans
      (Homeomorph.setCongr ?_)
  symm
  ext x
  simp [actualVanKampenFourPieceCover, VanKampenOpenCover,
    finiteCoverIntersection]

/-- The analytic order-four collar source, identified with the exact overlap in the actual
four-piece cover. -/
public noncomputable def orderFourCollarToActualOverlapHomeomorph :
    A.starCollarSourceType 2 ≃ₜ
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace) := by
  refine
    (A.openEmbeddingStarData.centralFillingIntersectionHomeomorph 2).trans
      (Homeomorph.setCongr ?_)
  symm
  ext x
  simp [actualVanKampenFourPieceCover, VanKampenOpenCover,
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
public noncomputable def orderThreeActualEllipticBoundaryProjection :
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
public noncomputable def orderFourActualEllipticBoundaryProjection :
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
    (A.openEmbeddingStarData.SectionSevenEulerCover).piece 2
  exact
    A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 1

/-- The analytic order-four filling is the exact order-four piece of the actual cover. -/
public noncomputable def orderFourFillingToActualPieceHomeomorph :
    A.OrderFourVaryingFilling A.starSeparation.orderFour.radius ≃ₜ
      A.actualVanKampenFourPieceCover.ellipticFour := by
  change A.openEmbeddingStarData.filling 2 ≃ₜ
    (A.openEmbeddingStarData.SectionSevenEulerCover).piece 3
  exact
    A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 2

/-- The explicit candidate universal-cover projection of the actual order-three filling. -/
public noncomputable def orderThreeActualEllipticFillingProjection :
    C(ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace,
      A.actualVanKampenFourPieceCover.ellipticThree) where
  toFun q := A.orderThreeFillingToActualPieceHomeomorph
    (A.orderThreeActualFillingCoverProjection A.starSeparation.orderThree.radius q)
  continuous_toFun := A.orderThreeFillingToActualPieceHomeomorph.continuous.comp
    (A.orderThreeActualFillingCoverProjection A.starSeparation.orderThree.radius).continuous

/-- The explicit candidate universal-cover projection of the actual order-four filling. -/
public noncomputable def orderFourActualEllipticFillingProjection :
    C(ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace,
      A.actualVanKampenFourPieceCover.ellipticFour) where
  toFun q := A.orderFourFillingToActualPieceHomeomorph
    (A.orderFourActualFillingCoverProjection A.starSeparation.orderFour.radius q)
  continuous_toFun := A.orderFourFillingToActualPieceHomeomorph.continuous.comp
    (A.orderFourActualFillingCoverProjection A.starSeparation.orderFour.radius).continuous

/-- The actual order-three filling projection is onto. -/
public theorem orderThreeActualEllipticFillingProjection_surjective :
    Function.Surjective A.orderThreeActualEllipticFillingProjection :=
  A.orderThreeFillingToActualPieceHomeomorph.surjective.comp
    (A.orderThreeActualFillingCoverProjection_surjective
      A.starSeparation.orderThree.radius)

/-- The actual order-four filling projection is onto. -/
public theorem orderFourActualEllipticFillingProjection_surjective :
    Function.Surjective A.orderFourActualEllipticFillingProjection :=
  A.orderFourFillingToActualPieceHomeomorph.surjective.comp
    (A.orderFourActualFillingCoverProjection_surjective
      A.starSeparation.orderFour.radius)

/-- The semidirect deck action on the explicit radial cover of the actual order-three overlap. -/
@[instance_reducible] public noncomputable def orderThreeActualEllipticBoundaryAction :
    MulAction (OrderThreeAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  exact passiveProdAction _ _ _

/-- The semidirect deck action on the explicit radial cover of the actual order-four overlap. -/
@[instance_reducible] public noncomputable def orderFourActualEllipticBoundaryAction :
    MulAction (OrderFourAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  exact passiveProdAction _ _ _

/-- The exact actual order-three overlap is the quotient by its explicit semidirect deck action. -/
public theorem orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap :
    letI := A.orderThreeActualEllipticBoundaryAction
    IsQuotientCoveringMap A.orderThreeActualEllipticBoundaryProjection
      (OrderThreeAffineMappingTorusDeck A.periods) := by
  let _ := orderThreeAffineMappingTorusDeckAction A.periods
  let _ := A.orderThreeActualEllipticBoundaryAction
  have hprod := passiveProd_isQuotientCoveringMap
    (R := OpenRadialInterval A.starSeparation.orderThree.radius)
    (orderThreeAffineMappingTorusLiftProjection_isQuotientCoveringMap A.periods)
  have h := hprod.homeomorph_comp
    A.orderThreeRadialMappingTorusToActualOverlapHomeomorph
  exact h

/-- The exact actual order-four overlap is the quotient by its explicit semidirect deck action. -/
public theorem orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap :
    letI := A.orderFourActualEllipticBoundaryAction
    IsQuotientCoveringMap A.orderFourActualEllipticBoundaryProjection
      (OrderFourAffineMappingTorusDeck A.periods) := by
  let _ := orderFourAffineMappingTorusDeckAction A.periods
  let _ := A.orderFourActualEllipticBoundaryAction
  have hprod := passiveProd_isQuotientCoveringMap
    (R := OpenRadialInterval A.starSeparation.orderFour.radius)
    (orderFourAffineMappingTorusLiftProjection_isQuotientCoveringMap A.periods)
  have h := hprod.homeomorph_comp
    A.orderFourRadialMappingTorusToActualOverlapHomeomorph
  exact h

/-- A canonical choice of lift of the marked order-three overlap point to the explicit radial
cover. -/
public noncomputable def orderThreeActualEllipticBoundaryBase :
    OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace) := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact Classical.choose
    (A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)

/-- The selected order-three radial base projects to the marked overlap point. -/
public theorem orderThreeActualEllipticBoundaryProjection_base :
    A.orderThreeActualEllipticBoundaryProjection A.orderThreeActualEllipticBoundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ := by
  let _ := A.orderThreeActualEllipticBoundaryAction
  exact Classical.choose_spec
    (A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)

/-- A canonical choice of lift of the marked order-four overlap point to the explicit radial
cover. -/
public noncomputable def orderFourActualEllipticBoundaryBase :
    OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace) := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact Classical.choose
    (A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)

/-- The selected order-four radial base projects to the marked overlap point. -/
public theorem orderFourActualEllipticBoundaryProjection_base :
    A.orderFourActualEllipticBoundaryProjection A.orderFourActualEllipticBoundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ := by
  let _ := A.orderFourActualEllipticBoundaryAction
  exact Classical.choose_spec
    (A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap.toIsQuotientMap.surjective
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)

/-- The explicit radial source of the actual order-three overlap cover is simply connected. -/
public theorem orderThreeActualEllipticBoundaryCover_simplyConnected :
    SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ : ContractibleSpace
      (OpenRadialInterval A.starSeparation.orderThree.radius) :=
    (convex_Ioo (0 : ℝ) A.starSeparation.orderThree.radius).contractibleSpace
      (Set.nonempty_Ioo.mpr A.starSeparation.orderThree.radius_pos)
  infer_instance

/-- The explicit radial source of the actual order-four overlap cover is simply connected. -/
public theorem orderFourActualEllipticBoundaryCover_simplyConnected :
    SimplyConnectedSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)) := by
  let _ : ContractibleSpace
      (OpenRadialInterval A.starSeparation.orderFour.radius) :=
    (convex_Ioo (0 : ℝ) A.starSeparation.orderFour.radius).contractibleSpace
      (Set.nonempty_Ioo.mpr A.starSeparation.orderFour.radius_pos)
  infer_instance

/-- Canonical inverse-meridian boundary deck data for the actual order-three collar. -/
public noncomputable def orderThreeActualEllipticBoundaryDeckData :
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
  twist := epsilon
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
    change (rhoLambda g₁).symm epsilon = epsilon
    apply (rhoLambda g₁).injective
    rw [(rhoLambda g₁).apply_symm_apply, rhoLambda_g₁_apply, A₁_epsilon]

/-- Canonical inverse-meridian boundary deck data for the actual order-four collar. -/
public noncomputable def orderFourActualEllipticBoundaryDeckData :
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
  twist := -epsilon'
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
    change (rhoLambda g₂).symm (-epsilon') = -epsilon'
    apply (rhoLambda g₂).injective
    rw [(rhoLambda g₂).apply_symm_apply, map_neg, rhoLambda_g₂_apply,
      A₂_epsilon']

/-- The remaining order-three filling geometry after fixing the explicit collar cover and deck
presentation. -/
public structure OrderThreeActualEllipticFillingExtension where
  fillingAction : MulAction A.orderThreeActualEllipticBoundaryDeckData.FillingDeck
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
  fillingQuotient : @IsQuotientCoveringMap
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
    A.actualVanKampenFourPieceCover.ellipticThree _ _
    A.orderThreeActualEllipticFillingProjection
    A.orderThreeActualEllipticBoundaryDeckData.FillingDeck _ fillingAction
  lift : C(OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace),
    ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
  commutes : ∀ z,
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
        (A.orderThreeActualEllipticBoundaryProjection z) =
      A.orderThreeActualEllipticFillingProjection (lift z)
  equivariant : ∀ g z,
    lift (@SMul.smul _ _ A.orderThreeActualEllipticBoundaryAction.toSMul g z) =
      @SMul.smul _ _ fillingAction.toSMul
        (A.orderThreeActualEllipticBoundaryDeckData.fillingDeckMap g) (lift z)

/-- The remaining order-four filling geometry after fixing the explicit collar cover and deck
presentation. -/
public structure OrderFourActualEllipticFillingExtension where
  fillingAction : MulAction A.orderFourActualEllipticBoundaryDeckData.FillingDeck
    (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
  fillingQuotient : @IsQuotientCoveringMap
    (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
    A.actualVanKampenFourPieceCover.ellipticFour _ _
    A.orderFourActualEllipticFillingProjection
    A.orderFourActualEllipticBoundaryDeckData.FillingDeck _ fillingAction
  lift : C(OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace),
    ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
  commutes : ∀ z,
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
        (A.orderFourActualEllipticBoundaryProjection z) =
      A.orderFourActualEllipticFillingProjection (lift z)
  equivariant : ∀ g z,
    lift (@SMul.smul _ _ A.orderFourActualEllipticBoundaryAction.toSMul g z) =
      @SMul.smul _ _ fillingAction.toSMul
        (A.orderFourActualEllipticBoundaryDeckData.fillingDeckMap g) (lift z)

/-- Order-three filling geometry with lift equivariance specified only at the marked lift. -/
public structure OrderThreeActualEllipticFillingExtensionAtBase where
  fillingAction : MulAction A.orderThreeActualEllipticBoundaryDeckData.FillingDeck
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
  fillingQuotient : @IsQuotientCoveringMap
    (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
    A.actualVanKampenFourPieceCover.ellipticThree _ _
    A.orderThreeActualEllipticFillingProjection
    A.orderThreeActualEllipticBoundaryDeckData.FillingDeck _ fillingAction
  lift : C(OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace),
    ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
  commutes : ∀ z,
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
        (A.orderThreeActualEllipticBoundaryProjection z) =
      A.orderThreeActualEllipticFillingProjection (lift z)
  equivariant_at_boundaryBase : ∀ g,
    lift (@SMul.smul _ _ A.orderThreeActualEllipticBoundaryAction.toSMul g
      A.orderThreeActualEllipticBoundaryBase) =
      @SMul.smul _ _ fillingAction.toSMul
        (A.orderThreeActualEllipticBoundaryDeckData.fillingDeckMap g)
        (lift A.orderThreeActualEllipticBoundaryBase)

/-- Order-four filling geometry with lift equivariance specified only at the marked lift. -/
public structure OrderFourActualEllipticFillingExtensionAtBase where
  fillingAction : MulAction A.orderFourActualEllipticBoundaryDeckData.FillingDeck
    (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
  fillingQuotient : @IsQuotientCoveringMap
    (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
    A.actualVanKampenFourPieceCover.ellipticFour _ _
    A.orderFourActualEllipticFillingProjection
    A.orderFourActualEllipticBoundaryDeckData.FillingDeck _ fillingAction
  lift : C(OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace),
    ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
  commutes : ∀ z,
    A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
        (A.orderFourActualEllipticBoundaryProjection z) =
      A.orderFourActualEllipticFillingProjection (lift z)
  equivariant_at_boundaryBase : ∀ g,
    lift (@SMul.smul _ _ A.orderFourActualEllipticBoundaryAction.toSMul g
      A.orderFourActualEllipticBoundaryBase) =
      @SMul.smul _ _ fillingAction.toSMul
        (A.orderFourActualEllipticBoundaryDeckData.fillingDeckMap g)
        (lift A.orderFourActualEllipticBoundaryBase)

namespace OrderThreeActualEllipticFillingExtensionAtBase

/-- Extend marked-point equivariance over the connected order-three collar cover. -/
public noncomputable def toFillingExtension
    (E : A.OrderThreeActualEllipticFillingExtensionAtBase) :
    A.OrderThreeActualEllipticFillingExtension := by
  letI := A.orderThreeActualEllipticBoundaryAction
  letI := E.fillingAction
  letI := A.orderThreeActualEllipticBoundaryCover_simplyConnected
  exact
    { fillingAction := E.fillingAction
      fillingQuotient := E.fillingQuotient
      lift := E.lift
      commutes := E.commutes
      equivariant := SphereSixComplex.Topology.quotientCover_equivariant_of_eq_at
        A.orderThreeActualEllipticBoundaryProjection
        A.orderThreeActualEllipticFillingProjection
        A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
        E.fillingQuotient
        A.orderThreeActualEllipticBoundaryDeckData.fillingDeckMap
        E.lift
        A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
        E.commutes
        A.orderThreeActualEllipticBoundaryBase
        E.equivariant_at_boundaryBase }

end OrderThreeActualEllipticFillingExtensionAtBase

namespace OrderFourActualEllipticFillingExtensionAtBase

/-- Extend marked-point equivariance over the connected order-four collar cover. -/
public noncomputable def toFillingExtension
    (E : A.OrderFourActualEllipticFillingExtensionAtBase) :
    A.OrderFourActualEllipticFillingExtension := by
  letI := A.orderFourActualEllipticBoundaryAction
  letI := E.fillingAction
  letI := A.orderFourActualEllipticBoundaryCover_simplyConnected
  exact
    { fillingAction := E.fillingAction
      fillingQuotient := E.fillingQuotient
      lift := E.lift
      commutes := E.commutes
      equivariant := SphereSixComplex.Topology.quotientCover_equivariant_of_eq_at
        A.orderFourActualEllipticBoundaryProjection
        A.orderFourActualEllipticFillingProjection
        A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
        E.fillingQuotient
        A.orderFourActualEllipticBoundaryDeckData.fillingDeckMap
        E.lift
        A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
        E.commutes
        A.orderFourActualEllipticBoundaryBase
        E.equivariant_at_boundaryBase }

end OrderFourActualEllipticFillingExtensionAtBase

namespace OrderThreeActualEllipticFillingExtension

/-- Assemble the complete chosen order-three filling-cover model from only the filling
extension. -/
public noncomputable def toChosenCover
    (E : A.OrderThreeActualEllipticFillingExtension) :
    ChosenCyclicAffineFillingCoverModel 3 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree := by
  letI := A.orderThreeActualEllipticBoundaryAction
  letI := E.fillingAction
  let U : UnwrappedCyclicAffineFillingCover 3 Lattice
      (OrderThreeAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderThree.radius × (ℝ × ComplexTwoSpace))
      (ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace)
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree
      A.orderThreeActualEllipticBoundaryDeckData := {
    boundaryProjection := A.orderThreeActualEllipticBoundaryProjection
    fillingProjection := A.orderThreeActualEllipticFillingProjection
    boundaryQuotient := A.orderThreeActualEllipticBoundaryProjection_isQuotientCoveringMap
    fillingQuotient := E.fillingQuotient
    boundarySimplyConnected := A.orderThreeActualEllipticBoundaryCover_simplyConnected
    fillingSimplyConnected := orderThreeFillingCoverSource_simplyConnected
      A.starSeparation.orderThree.radius_pos A.starSeparation.orderThree.radius_lt_one
    lift := E.lift
    baseMap := A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
    commutes := E.commutes
    equivariant := E.equivariant
    base := A.orderThreeActualEllipticBoundaryBase }
  exact
    { BoundaryDeck := OrderThreeAffineMappingTorusDeck A.periods
      FillingDeck := A.orderThreeActualEllipticBoundaryDeckData.FillingDeck
      BoundaryCover := OpenRadialInterval A.starSeparation.orderThree.radius ×
        (ℝ × ComplexTwoSpace)
      FillingCover := ComplexDiscBall A.starSeparation.orderThree.radius × ComplexTwoSpace
      boundaryDeckGroup := inferInstance
      fillingDeckGroup := inferInstance
      boundaryCoverTopology := inferInstance
      fillingCoverTopology := inferInstance
      boundaryAction := A.orderThreeActualEllipticBoundaryAction
      fillingAction := E.fillingAction
      model := U.toCyclicAffineFillingCoverModel }

/-- The chosen order-three cover is based at the marked overlap point. -/
public theorem toChosenCover_boundaryBase_eq
    (E : A.OrderThreeActualEllipticFillingExtension) :
    E.toChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩ :=
  A.orderThreeActualEllipticBoundaryProjection_base

/-- The chosen order-three filling base is the marked filling point. -/
public theorem toChosenCover_fillingBase_eq
    (E : A.OrderThreeActualEllipticFillingExtension) :
    E.toChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩ := by
  change A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
      (A.orderThreeActualEllipticBoundaryProjection
        A.orderThreeActualEllipticBoundaryBase) = _
  rw [A.orderThreeActualEllipticBoundaryProjection_base]
  rfl

end OrderThreeActualEllipticFillingExtension

namespace OrderFourActualEllipticFillingExtension

/-- Assemble the complete chosen order-four filling-cover model from only the filling
extension. -/
public noncomputable def toChosenCover
    (E : A.OrderFourActualEllipticFillingExtension) :
    ChosenCyclicAffineFillingCoverModel 4 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour := by
  letI := A.orderFourActualEllipticBoundaryAction
  letI := E.fillingAction
  let U : UnwrappedCyclicAffineFillingCover 4 Lattice
      (OrderFourAffineMappingTorusDeck A.periods)
      (OpenRadialInterval A.starSeparation.orderFour.radius × (ℝ × ComplexTwoSpace))
      (ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace)
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour
      A.orderFourActualEllipticBoundaryDeckData := {
    boundaryProjection := A.orderFourActualEllipticBoundaryProjection
    fillingProjection := A.orderFourActualEllipticFillingProjection
    boundaryQuotient := A.orderFourActualEllipticBoundaryProjection_isQuotientCoveringMap
    fillingQuotient := E.fillingQuotient
    boundarySimplyConnected := A.orderFourActualEllipticBoundaryCover_simplyConnected
    fillingSimplyConnected := orderFourFillingCoverSource_simplyConnected
      A.starSeparation.orderFour.radius_pos A.starSeparation.orderFour.radius_lt_one
    lift := E.lift
    baseMap := A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
    commutes := E.commutes
    equivariant := E.equivariant
    base := A.orderFourActualEllipticBoundaryBase }
  exact
    { BoundaryDeck := OrderFourAffineMappingTorusDeck A.periods
      FillingDeck := A.orderFourActualEllipticBoundaryDeckData.FillingDeck
      BoundaryCover := OpenRadialInterval A.starSeparation.orderFour.radius ×
        (ℝ × ComplexTwoSpace)
      FillingCover := ComplexDiscBall A.starSeparation.orderFour.radius × ComplexTwoSpace
      boundaryDeckGroup := inferInstance
      fillingDeckGroup := inferInstance
      boundaryCoverTopology := inferInstance
      fillingCoverTopology := inferInstance
      boundaryAction := A.orderFourActualEllipticBoundaryAction
      fillingAction := E.fillingAction
      model := U.toCyclicAffineFillingCoverModel }

/-- The chosen order-four cover is based at the marked overlap point. -/
public theorem toChosenCover_boundaryBase_eq
    (E : A.OrderFourActualEllipticFillingExtension) :
    E.toChosenCover.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩ :=
  A.orderFourActualEllipticBoundaryProjection_base

/-- The chosen order-four filling base is the marked filling point. -/
public theorem toChosenCover_fillingBase_eq
    (E : A.OrderFourActualEllipticFillingExtension) :
    E.toChosenCover.fillingBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩ := by
  change A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
      (A.orderFourActualEllipticBoundaryProjection
        A.orderFourActualEllipticBoundaryBase) = _
  rw [A.orderFourActualEllipticBoundaryProjection_base]
  rfl

end OrderFourActualEllipticFillingExtension

/-- The actual order-three overlap included into the core and transported along the specified
connector to the base point of the four-piece cover. -/
public noncomputable def actualEllipticThreeOverlapToCore :
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
public noncomputable def actualEllipticFourOverlapToCore :
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
public theorem actualEllipticThreeAffineBridge_square :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.actualEllipticThreeOverlapToCore =
      A.actualVanKampenFourPieceCover.ellipticThreeFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  ext γ
  exact coreSquare_apply A.actualVanKampenFourPieceCover
    A.actualVanKampenFourPieceCover.ellipticThree
    A.actualVanKampenFourPieceCover.ellipticThreePoint_mem
    A.actualVanKampenFourPieceCover.ellipticThreeConnector
    A.actualVanKampenFourPieceCover.ellipticThreeConnector_mem γ

/-- The actual overlap-to-core map gives the order-four square of the affine star bridge. -/
public theorem actualEllipticFourAffineBridge_square :
    A.actualVanKampenFourPieceCover.coreFundamentalGroupMap.comp
        A.actualEllipticFourOverlapToCore =
      A.actualVanKampenFourPieceCover.ellipticFourFundamentalGroupMap.comp
        A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  ext γ
  exact coreSquare_apply A.actualVanKampenFourPieceCover
    A.actualVanKampenFourPieceCover.ellipticFour
    A.actualVanKampenFourPieceCover.ellipticFourPoint_mem
    A.actualVanKampenFourPieceCover.ellipticFourConnector
    A.actualVanKampenFourPieceCover.ellipticFourConnector_mem γ
/-- The central affine presentation transported through a marked cusp naturality equivalence. -/
public noncomputable def coreDataOf (N : A.ActualCuspCentralNaturality) :
    AffineTorusCorePiOneData
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩)
      Lattice paperMonodromyOne paperMonodromyTwo :=
  A.centralAffineCorePiOneData.mapSurjective N.centralToCore.toMonoidHom
    N.centralToCore.surjective

/-- Every marked cusp translation maps to the corresponding transported core translation. -/
public theorem cuspBridge_translation_core (N : A.ActualCuspCentralNaturality) (a : Lattice) :
    A.actualCuspOverlapToCore
        (Additive.toMul (A.actualCuspAffineBridgeTranslation a)) =
      Additive.toMul ((A.coreDataOf N).translation a) :=
  N.translation_core a

/-- At cusp twist zero, the marked cusp meridian maps to the product of the two core meridians. -/
public theorem cuspBridge_meridian_core (N : A.ActualCuspCentralNaturality) :
    A.actualCuspOverlapToCore A.actualCuspAffineBridgeMeridian =
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

/-- Marked peripheral naturality and chosen regular cover squares for the two actual elliptic
collars, relative to a marked cusp naturality equivalence `N`.

This is the exact elliptic counterpart of `ActualCuspCentralNaturality` together with the two
chosen cyclic filling-cover models.  Every remaining field of
`ActualAffineFillingCoverSquares` is derived from it and from the already established cusp
package. -/
public structure ActualEllipticCentralNaturality (N : A.ActualCuspCentralNaturality) where
  orderThreeCover : ChosenCyclicAffineFillingCoverModel 3 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticThree
  orderThreeBoundaryBase_eq : orderThreeCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩
  orderThreeFillingBase_eq : orderThreeCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩
  orderThreeMap_eq : fundamentalGroupHomOfBaseEq
    orderThreeBoundaryBase_eq orderThreeFillingBase_eq
    orderThreeCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
  orderThreeTwist_eq : orderThreeCover.twist = epsilon
  orderThreeTranslation_naturality : ∀ a : Lattice,
    A.actualEllipticThreeOverlapToCore
        (Additive.toMul
          (fundamentalGroupAddHomOfBaseEq orderThreeBoundaryBase_eq
            orderThreeCover.translation a)) =
      N.centralToCore (Additive.toMul (A.centralAffineCorePiOneData.translation a))
  orderThreeMeridian_naturality :
    A.actualEllipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq orderThreeBoundaryBase_eq
          orderThreeCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourCover : ChosenCyclicAffineFillingCoverModel 4 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticFour
  orderFourBoundaryBase_eq : orderFourCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩
  orderFourFillingBase_eq : orderFourCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩
  orderFourMap_eq : fundamentalGroupHomOfBaseEq
    orderFourBoundaryBase_eq orderFourFillingBase_eq
    orderFourCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
  orderFourTwist_eq : orderFourCover.twist = -epsilon'
  orderFourTranslation_naturality : ∀ a : Lattice,
    A.actualEllipticFourOverlapToCore
        (Additive.toMul
          (fundamentalGroupAddHomOfBaseEq orderFourBoundaryBase_eq
            orderFourCover.translation a)) =
      N.centralToCore (Additive.toMul (A.centralAffineCorePiOneData.translation a))
  orderFourMeridian_naturality :
    A.actualEllipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq orderFourBoundaryBase_eq
          orderFourCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

/-- Two additive homomorphisms out of the rank-four paper lattice agree when they agree on the
standard integral basis.  The codomain need not be commutative. -/
public theorem latticeAddHom_ext_integralBasis
    {G : Type*} [AddGroup G] (f g : Lattice →+ G)
    (h : ∀ i : Fin 4,
      f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector i) =
        g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector i)) :
    f = g := by
  ext a
  have ha : a =
      a 0 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0 +
      a 1 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1 +
      a 2 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2 +
      a 3 • SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3 := by
    ext i
    fin_cases i <;>
      simp [SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single]
  rw [ha]
  simp only [map_add, map_zsmul]
  rw [h 0, h 1, h 2, h 3]

/-- The order-three monodromy sends the second basis vector to the difference of the fourth and
third basis vectors. -/
public theorem paperMonodromyOne_integralBasisVector_one :
    paperMonodromyOne
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      -SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2 +
        SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3 := by
  ext i
  fin_cases i <;>
    simp [paperMonodromyOne, A₁, dotProduct,
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single,
      Fin.sum_univ_succ]

/-- The order-four monodromy sends the second basis vector to the third. -/
public theorem paperMonodromyTwo_integralBasisVector_one :
    paperMonodromyTwo
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2 := by
  ext i
  fin_cases i <;>
    simp [paperMonodromyTwo, A₂, dotProduct,
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single,
      Fin.sum_univ_succ]

/-- The order-four monodromy sends the third basis vector to the difference of the fourth and
second basis vectors. -/
public theorem paperMonodromyTwo_integralBasisVector_two :
    paperMonodromyTwo
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) =
      -SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1 +
        SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3 := by
  ext i
  fin_cases i <;>
    simp [paperMonodromyTwo, A₂, dotProduct,
      SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector, Pi.single,
      Fin.sum_univ_succ]

/-- Two lattice markings conjugated by the same meridian propagate equality along their common
monodromy. -/
public theorem latticeAddHom_eq_propagates_of_conjugates
    {Λ G : Type*} [AddCommGroup Λ] [Group G]
    (M : Λ →+ Λ) (f g : Λ →+ Additive G) (r : G)
    (hf : ∀ a, r * Additive.toMul (f a) * r⁻¹ = Additive.toMul (f (M a)))
    (hg : ∀ a, r * Additive.toMul (g a) * r⁻¹ = Additive.toMul (g (M a))) :
    ∀ a, f a = g a → f (M a) = g (M a) := by
  intro a h
  change Additive.toMul (f (M a)) = Additive.toMul (g (M a))
  rw [← hf, ← hg, h]

/-- For order three, monodromy propagation reduces equality of lattice maps to three marked
coordinates. -/
public theorem latticeAddHom_ext_orderThreeMonodromy
    {G : Type*} [AddGroup G] (f g : Lattice →+ G)
    (hmonodromy : ∀ a, f a = g a →
      f (paperMonodromyOne a) = g (paperMonodromyOne a))
    (hzero : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0))
    (hone : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1))
    (hthree : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3)) :
    f = g := by
  have hmonodromyOne := hmonodromy
    (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) hone
  rw [paperMonodromyOne_integralBasisVector_one, map_add, map_add, map_neg, map_neg]
    at hmonodromyOne
  rw [hthree] at hmonodromyOne
  have htwo : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) := by
    exact neg_injective (add_right_cancel hmonodromyOne)
  apply latticeAddHom_ext_integralBasis
  intro i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo
  · exact hthree

/-- For order four, monodromy propagation reduces equality of lattice maps to two marked
coordinates. -/
public theorem latticeAddHom_ext_orderFourMonodromy
    {G : Type*} [AddGroup G] (f g : Lattice →+ G)
    (hmonodromy : ∀ a, f a = g a →
      f (paperMonodromyTwo a) = g (paperMonodromyTwo a))
    (hzero : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0))
    (hone : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)) :
    f = g := by
  have htwo : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) := by
    rw [← paperMonodromyTwo_integralBasisVector_one]
    exact hmonodromy
      (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) hone
  have hmonodromyTwo := hmonodromy
    (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 2) htwo
  rw [paperMonodromyTwo_integralBasisVector_two, map_add, map_add, map_neg, map_neg]
    at hmonodromyTwo
  rw [hone] at hmonodromyTwo
  have hthree : f (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      g (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) := by
    exact add_left_cancel hmonodromyTwo
  apply latticeAddHom_ext_integralBasis
  intro i
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo
  · exact hthree

/-- The order-three collar translations, transported to the central core. -/
public noncomputable def actualEllipticThreeTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 3 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩) :
    Lattice →+ Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :=
  A.actualEllipticThreeOverlapToCore.toAdditive.comp
    (fundamentalGroupAddHomOfBaseEq hb D.translation)

/-- The order-four collar translations, transported to the central core. -/
public noncomputable def actualEllipticFourTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 4 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩) :
    Lattice →+ Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :=
  A.actualEllipticFourOverlapToCore.toAdditive.comp
    (fundamentalGroupAddHomOfBaseEq hb D.translation)

/-- The central-family translations, transported to the central core. -/
public noncomputable def actualCentralTranslationToCore
    (N : A.ActualCuspCentralNaturality) :
    Lattice →+ Additive
      (FundamentalGroup A.actualVanKampenFourPieceCover.core
        ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩) :=
  N.centralToCore.toMonoidHom.toAdditive.comp A.centralAffineCorePiOneData.translation

/-- The first central meridian conjugates the transported central marking by the order-three
monodromy. -/
public theorem actualCentralRhoOne_conjugatesTranslationToCore
    (N : A.ActualCuspCentralNaturality) (a : Lattice) :
    N.centralToCore A.centralAffineCorePiOneData.rhoOne *
        Additive.toMul (A.actualCentralTranslationToCore N a) *
        (N.centralToCore A.centralAffineCorePiOneData.rhoOne)⁻¹ =
      Additive.toMul
        (A.actualCentralTranslationToCore N (paperMonodromyOne a)) :=
  (A.coreDataOf N).conjugate_one a

/-- The second central meridian conjugates the transported central marking by the order-four
monodromy. -/
public theorem actualCentralRhoTwo_conjugatesTranslationToCore
    (N : A.ActualCuspCentralNaturality) (a : Lattice) :
    N.centralToCore A.centralAffineCorePiOneData.rhoTwo *
        Additive.toMul (A.actualCentralTranslationToCore N a) *
        (N.centralToCore A.centralAffineCorePiOneData.rhoTwo)⁻¹ =
      Additive.toMul
        (A.actualCentralTranslationToCore N (paperMonodromyTwo a)) :=
  (A.coreDataOf N).conjugate_two a

/-- The transported order-three collar meridian conjugates its translations by the paper
monodromy whenever the selected deck monodromy has the corresponding inverse convention. -/
public theorem actualEllipticThreeMeridian_conjugatesTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 3 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticThree)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
        A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩)
    (hinv : ∀ a, D.monodromy.toAdd (paperMonodromyOne a) = a) (a : Lattice) :
    A.actualEllipticThreeOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian) *
        Additive.toMul (A.actualEllipticThreeTranslationToCore D hb a) *
        (A.actualEllipticThreeOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian))⁻¹ =
      Additive.toMul
        (A.actualEllipticThreeTranslationToCore D hb (paperMonodromyOne a)) := by
  have h := D.meridian_conjugates_translation_of_rightInverse paperMonodromyOne hinv a
  have h' := congrArg
    (fun z ↦ A.actualEllipticThreeOverlapToCore
      (fundamentalGroupElementOfBaseEq hb z)) h
  simpa only [actualEllipticThreeTranslationToCore, AddMonoidHom.comp_apply,
    fundamentalGroupAddHomOfBaseEq_apply, MonoidHom.coe_toAdditive, Function.comp_apply,
    toMul_ofMul, fundamentalGroupElementOfBaseEq_mul, fundamentalGroupElementOfBaseEq_inv,
    map_mul, map_inv] using h'

/-- The transported order-four collar meridian conjugates its translations by the paper
monodromy whenever the selected deck monodromy has the corresponding inverse convention. -/
public theorem actualEllipticFourMeridian_conjugatesTranslationToCore
    (D : ChosenCyclicAffineFillingCoverModel 4 Lattice
      (A.actualVanKampenFourPieceCover.core ∩
        A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
      A.actualVanKampenFourPieceCover.ellipticFour)
    (hb : D.boundaryBase =
      ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
        A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩)
    (hinv : ∀ a, D.monodromy.toAdd (paperMonodromyTwo a) = a) (a : Lattice) :
    A.actualEllipticFourOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian) *
        Additive.toMul (A.actualEllipticFourTranslationToCore D hb a) *
        (A.actualEllipticFourOverlapToCore
          (fundamentalGroupElementOfBaseEq hb D.meridian))⁻¹ =
      Additive.toMul
        (A.actualEllipticFourTranslationToCore D hb (paperMonodromyTwo a)) := by
  have h := D.meridian_conjugates_translation_of_rightInverse paperMonodromyTwo hinv a
  have h' := congrArg
    (fun z ↦ A.actualEllipticFourOverlapToCore
      (fundamentalGroupElementOfBaseEq hb z)) h
  simpa only [actualEllipticFourTranslationToCore, AddMonoidHom.comp_apply,
    fundamentalGroupAddHomOfBaseEq_apply, MonoidHom.coe_toAdditive, Function.comp_apply,
    toMul_ofMul, fundamentalGroupElementOfBaseEq_mul, fundamentalGroupElementOfBaseEq_inv,
    map_mul, map_inv] using h'

/-- The exact elliptic cover geometry and a finite marking.

The cover monodromy is required to be inverse to the displayed paper monodromy, as dictated by
the opposite-deck-group convention.  Conjugation then propagates translation naturality from
three marked coordinates on the order-three side and two on the order-four side. -/
public structure ActualEllipticCentralBasisNaturality (N : A.ActualCuspCentralNaturality) where
  orderThreeCover : ChosenCyclicAffineFillingCoverModel 3 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticThree : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticThree
  orderThreeBoundaryBase_eq : orderThreeCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem⟩
  orderThreeFillingBase_eq : orderThreeCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticThreePoint,
      A.actualVanKampenFourPieceCover.ellipticThreePoint_mem.2⟩
  orderThreeMap_eq : fundamentalGroupHomOfBaseEq
    orderThreeBoundaryBase_eq orderThreeFillingBase_eq
    orderThreeCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
  orderThreeTwist_eq : orderThreeCover.twist = epsilon
  orderThreeMonodromy_inverse : ∀ a,
    orderThreeCover.monodromy.toAdd (paperMonodromyOne a) = a
  orderThreeTranslation_zero :
    A.actualEllipticThreeTranslationToCore orderThreeCover orderThreeBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderThreeTranslation_one :
    A.actualEllipticThreeTranslationToCore orderThreeCover orderThreeBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderThreeTranslation_three :
    A.actualEllipticThreeTranslationToCore orderThreeCover orderThreeBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3)
  orderThreeMeridian_naturality :
    A.actualEllipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq orderThreeBoundaryBase_eq
          orderThreeCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourCover : ChosenCyclicAffineFillingCoverModel 4 Lattice
    (A.actualVanKampenFourPieceCover.core ∩
      A.actualVanKampenFourPieceCover.ellipticFour : Set A.VanKampenSpace)
    A.actualVanKampenFourPieceCover.ellipticFour
  orderFourBoundaryBase_eq : orderFourCover.boundaryBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem⟩
  orderFourFillingBase_eq : orderFourCover.fillingBase =
    ⟨A.actualVanKampenFourPieceCover.ellipticFourPoint,
      A.actualVanKampenFourPieceCover.ellipticFourPoint_mem.2⟩
  orderFourMap_eq : fundamentalGroupHomOfBaseEq
    orderFourBoundaryBase_eq orderFourFillingBase_eq
    orderFourCover.fundamentalGroupMap =
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
  orderFourTwist_eq : orderFourCover.twist = -epsilon'
  orderFourMonodromy_inverse : ∀ a,
    orderFourCover.monodromy.toAdd (paperMonodromyTwo a) = a
  orderFourTranslation_zero :
    A.actualEllipticFourTranslationToCore orderFourCover orderFourBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderFourTranslation_one :
    A.actualEllipticFourTranslationToCore orderFourCover orderFourBoundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderFourMeridian_naturality :
    A.actualEllipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq orderFourBoundaryBase_eq
          orderFourCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

namespace ActualEllipticCentralBasisNaturality

variable {A} {N : A.ActualCuspCentralNaturality}

/-- Extend the finite basis marking to every lattice translation. -/
public noncomputable def toActualEllipticCentralNaturality
    (E : ActualEllipticCentralBasisNaturality A N) :
    ActualEllipticCentralNaturality A N where
  orderThreeCover := E.orderThreeCover
  orderThreeBoundaryBase_eq := E.orderThreeBoundaryBase_eq
  orderThreeFillingBase_eq := E.orderThreeFillingBase_eq
  orderThreeMap_eq := E.orderThreeMap_eq
  orderThreeTwist_eq := E.orderThreeTwist_eq
  orderThreeTranslation_naturality := fun a ↦ by
    have hf : ∀ x,
        N.centralToCore A.centralAffineCorePiOneData.rhoOne *
            Additive.toMul
              (A.actualEllipticThreeTranslationToCore E.orderThreeCover
                E.orderThreeBoundaryBase_eq x) *
            (N.centralToCore A.centralAffineCorePiOneData.rhoOne)⁻¹ =
          Additive.toMul
            (A.actualEllipticThreeTranslationToCore E.orderThreeCover
              E.orderThreeBoundaryBase_eq (paperMonodromyOne x)) := by
      intro x
      rw [← E.orderThreeMeridian_naturality]
      exact A.actualEllipticThreeMeridian_conjugatesTranslationToCore E.orderThreeCover
        E.orderThreeBoundaryBase_eq E.orderThreeMonodromy_inverse x
    have hprop := latticeAddHom_eq_propagates_of_conjugates paperMonodromyOne
      (A.actualEllipticThreeTranslationToCore E.orderThreeCover
        E.orderThreeBoundaryBase_eq)
      (A.actualCentralTranslationToCore N)
      (N.centralToCore A.centralAffineCorePiOneData.rhoOne) hf
      (A.actualCentralRhoOne_conjugatesTranslationToCore N)
    have hmaps := latticeAddHom_ext_orderThreeMonodromy
      (A.actualEllipticThreeTranslationToCore E.orderThreeCover
        E.orderThreeBoundaryBase_eq)
      (A.actualCentralTranslationToCore N) hprop E.orderThreeTranslation_zero
      E.orderThreeTranslation_one E.orderThreeTranslation_three
    exact congrArg Additive.toMul (DFunLike.congr_fun hmaps a)
  orderThreeMeridian_naturality := E.orderThreeMeridian_naturality
  orderFourCover := E.orderFourCover
  orderFourBoundaryBase_eq := E.orderFourBoundaryBase_eq
  orderFourFillingBase_eq := E.orderFourFillingBase_eq
  orderFourMap_eq := E.orderFourMap_eq
  orderFourTwist_eq := E.orderFourTwist_eq
  orderFourTranslation_naturality := fun a ↦ by
    have hf : ∀ x,
        N.centralToCore A.centralAffineCorePiOneData.rhoTwo *
            Additive.toMul
              (A.actualEllipticFourTranslationToCore E.orderFourCover
                E.orderFourBoundaryBase_eq x) *
            (N.centralToCore A.centralAffineCorePiOneData.rhoTwo)⁻¹ =
          Additive.toMul
            (A.actualEllipticFourTranslationToCore E.orderFourCover
              E.orderFourBoundaryBase_eq (paperMonodromyTwo x)) := by
      intro x
      rw [← E.orderFourMeridian_naturality]
      exact A.actualEllipticFourMeridian_conjugatesTranslationToCore E.orderFourCover
        E.orderFourBoundaryBase_eq E.orderFourMonodromy_inverse x
    have hprop := latticeAddHom_eq_propagates_of_conjugates paperMonodromyTwo
      (A.actualEllipticFourTranslationToCore E.orderFourCover
        E.orderFourBoundaryBase_eq)
      (A.actualCentralTranslationToCore N)
      (N.centralToCore A.centralAffineCorePiOneData.rhoTwo) hf
      (A.actualCentralRhoTwo_conjugatesTranslationToCore N)
    have hmaps := latticeAddHom_ext_orderFourMonodromy
      (A.actualEllipticFourTranslationToCore E.orderFourCover
        E.orderFourBoundaryBase_eq)
      (A.actualCentralTranslationToCore N) hprop E.orderFourTranslation_zero
      E.orderFourTranslation_one
    exact congrArg Additive.toMul (DFunLike.congr_fun hmaps a)
  orderFourMeridian_naturality := E.orderFourMeridian_naturality

end ActualEllipticCentralBasisNaturality

/-- The exact remaining elliptic filling and marking data after constructing both collar covers
and their deck presentations.

Only the filling extensions, five lattice anchors, and the two marked meridians remain.  The
chosen collar-cover models, marked base points, twists, inverse-monodromy identities, and induced
overlap maps are reconstructed from these fields. -/
public structure ActualEllipticMarkedFillingExtensionNaturality
    (N : A.ActualCuspCentralNaturality) where
  orderThreeExtension : A.OrderThreeActualEllipticFillingExtension
  orderThreeTranslation_zero :
    A.actualEllipticThreeTranslationToCore orderThreeExtension.toChosenCover
        orderThreeExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderThreeTranslation_one :
    A.actualEllipticThreeTranslationToCore orderThreeExtension.toChosenCover
        orderThreeExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderThreeTranslation_three :
    A.actualEllipticThreeTranslationToCore orderThreeExtension.toChosenCover
        orderThreeExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3)
  orderThreeMeridian_naturality :
    A.actualEllipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq orderThreeExtension.toChosenCover_boundaryBase_eq
          orderThreeExtension.toChosenCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourExtension : A.OrderFourActualEllipticFillingExtension
  orderFourTranslation_zero :
    A.actualEllipticFourTranslationToCore orderFourExtension.toChosenCover
        orderFourExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderFourTranslation_one :
    A.actualEllipticFourTranslationToCore orderFourExtension.toChosenCover
        orderFourExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderFourMeridian_naturality :
    A.actualEllipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq orderFourExtension.toChosenCover_boundaryBase_eq
          orderFourExtension.toChosenCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

namespace ActualEllipticMarkedFillingExtensionNaturality

variable {A} {N : A.ActualCuspCentralNaturality}

/-- Reconstruct the former elliptic basis-naturality package from the explicit collar covers. -/
public noncomputable def toActualEllipticCentralBasisNaturality
    (E : ActualEllipticMarkedFillingExtensionNaturality A N) :
    ActualEllipticCentralBasisNaturality A N where
  orderThreeCover := E.orderThreeExtension.toChosenCover
  orderThreeBoundaryBase_eq := E.orderThreeExtension.toChosenCover_boundaryBase_eq
  orderThreeFillingBase_eq := E.orderThreeExtension.toChosenCover_fillingBase_eq
  orderThreeMap_eq := by
    exact fundamentalGroupHomOfBaseEq_map_transport
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapToPiece
      E.orderThreeExtension.toChosenCover_boundaryBase_eq
      E.orderThreeExtension.toChosenCover_fillingBase_eq
  orderThreeTwist_eq := rfl
  orderThreeMonodromy_inverse := fun a ↦ by
    change (rhoLambda g₁).symm (A₁.mulVec a) = a
    rw [← rhoLambda_g₁_apply, (rhoLambda g₁).symm_apply_apply]
  orderThreeTranslation_zero := E.orderThreeTranslation_zero
  orderThreeTranslation_one := E.orderThreeTranslation_one
  orderThreeTranslation_three := E.orderThreeTranslation_three
  orderThreeMeridian_naturality := E.orderThreeMeridian_naturality
  orderFourCover := E.orderFourExtension.toChosenCover
  orderFourBoundaryBase_eq := E.orderFourExtension.toChosenCover_boundaryBase_eq
  orderFourFillingBase_eq := E.orderFourExtension.toChosenCover_fillingBase_eq
  orderFourMap_eq := by
    exact fundamentalGroupHomOfBaseEq_map_transport
      A.actualVanKampenFourPieceCover.ellipticFourOverlapToPiece
      E.orderFourExtension.toChosenCover_boundaryBase_eq
      E.orderFourExtension.toChosenCover_fillingBase_eq
  orderFourTwist_eq := rfl
  orderFourMonodromy_inverse := fun a ↦ by
    change (rhoLambda g₂).symm (A₂.mulVec a) = a
    rw [← rhoLambda_g₂_apply, (rhoLambda g₂).symm_apply_apply]
  orderFourTranslation_zero := E.orderFourTranslation_zero
  orderFourTranslation_one := E.orderFourTranslation_one
  orderFourMeridian_naturality := E.orderFourMeridian_naturality

end ActualEllipticMarkedFillingExtensionNaturality

/-- The elliptic filling and marking data with each lift's equivariance reduced to one point. -/
public structure ActualEllipticMarkedFillingExtensionAtBaseNaturality
    (N : A.ActualCuspCentralNaturality) where
  orderThreeExtension : A.OrderThreeActualEllipticFillingExtensionAtBase
  orderThreeTranslation_zero :
    A.actualEllipticThreeTranslationToCore
        orderThreeExtension.toFillingExtension.toChosenCover
        orderThreeExtension.toFillingExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderThreeTranslation_one :
    A.actualEllipticThreeTranslationToCore
        orderThreeExtension.toFillingExtension.toChosenCover
        orderThreeExtension.toFillingExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderThreeTranslation_three :
    A.actualEllipticThreeTranslationToCore
        orderThreeExtension.toFillingExtension.toChosenCover
        orderThreeExtension.toFillingExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 3)
  orderThreeMeridian_naturality :
    A.actualEllipticThreeOverlapToCore
        (fundamentalGroupElementOfBaseEq
          orderThreeExtension.toFillingExtension.toChosenCover_boundaryBase_eq
          orderThreeExtension.toFillingExtension.toChosenCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoOne
  orderFourExtension : A.OrderFourActualEllipticFillingExtensionAtBase
  orderFourTranslation_zero :
    A.actualEllipticFourTranslationToCore
        orderFourExtension.toFillingExtension.toChosenCover
        orderFourExtension.toFillingExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 0)
  orderFourTranslation_one :
    A.actualEllipticFourTranslationToCore
        orderFourExtension.toFillingExtension.toChosenCover
        orderFourExtension.toFillingExtension.toChosenCover_boundaryBase_eq
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1) =
      A.actualCentralTranslationToCore N
        (SphereSixComplex.Geometry.GlobalTorusFamily.integralBasisVector 1)
  orderFourMeridian_naturality :
    A.actualEllipticFourOverlapToCore
        (fundamentalGroupElementOfBaseEq
          orderFourExtension.toFillingExtension.toChosenCover_boundaryBase_eq
          orderFourExtension.toFillingExtension.toChosenCover.meridian) =
      N.centralToCore A.centralAffineCorePiOneData.rhoTwo

namespace ActualEllipticMarkedFillingExtensionAtBaseNaturality

variable {A} {N : A.ActualCuspCentralNaturality}

/-- Recover the former marked filling-extension package by uniqueness of lifts. -/
public noncomputable def toFillingExtensionNaturality
    (E : ActualEllipticMarkedFillingExtensionAtBaseNaturality A N) :
    ActualEllipticMarkedFillingExtensionNaturality A N where
  orderThreeExtension := E.orderThreeExtension.toFillingExtension
  orderThreeTranslation_zero := E.orderThreeTranslation_zero
  orderThreeTranslation_one := E.orderThreeTranslation_one
  orderThreeTranslation_three := E.orderThreeTranslation_three
  orderThreeMeridian_naturality := E.orderThreeMeridian_naturality
  orderFourExtension := E.orderFourExtension.toFillingExtension
  orderFourTranslation_zero := E.orderFourTranslation_zero
  orderFourTranslation_one := E.orderFourTranslation_one
  orderFourMeridian_naturality := E.orderFourMeridian_naturality

end ActualEllipticMarkedFillingExtensionAtBaseNaturality

private theorem fundamentalGroup_map_surjective_of_homeomorph_square
    {X X' Y Y' : Type*}
    [TopologicalSpace X] [TopologicalSpace X']
    [TopologicalSpace Y] [TopologicalSpace Y']
    (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
    (f : C(X, Y)) (g : C(X', Y'))
    (hcomm : g.comp (⟨eX, eX.continuous⟩ : C(X, X')) =
      (⟨eY, eY.continuous⟩ : C(Y, Y')).comp f)
    (x' : X')
    (hsurj : Function.Surjective (FundamentalGroup.map f (eX.symm x'))) :
    Function.Surjective (FundamentalGroup.map g x') := by
  let x := eX.symm x'
  have hx : eX x = x' := eX.apply_symm_apply x'
  have hy : eY (f x) = g x' := by
    exact (DFunLike.congr_fun hcomm x).symm.trans (congrArg g hx)
  let sourceEquiv := TauCeti.FundamentalGroup.homeomorphMulEquivOfEq eX hx
  let targetEquiv := TauCeti.FundamentalGroup.homeomorphMulEquivOfEq eY hy
  have hnatural (a : FundamentalGroup X x) :
      FundamentalGroup.map g x' (sourceEquiv a) =
        targetEquiv (FundamentalGroup.map f x a) := by
    change FundamentalGroup.map g x'
        (FundamentalGroup.mapOfEq ⟨eX, eX.continuous⟩ hx a) =
      FundamentalGroup.mapOfEq ⟨eY, eY.continuous⟩ hy
        (FundamentalGroup.map f x a)
    rw [← TauCeti.FundamentalGroup.mapOfEq_rfl g,
      TauCeti.FundamentalGroup.mapOfEq_comp]
    rw [← TauCeti.FundamentalGroup.mapOfEq_rfl f,
      TauCeti.FundamentalGroup.mapOfEq_comp]
    exact TauCeti.FundamentalGroup.mapOfEq_congr hcomm _ _ a
  intro z
  obtain ⟨y, rfl⟩ := targetEquiv.surjective z
  obtain ⟨a, ha⟩ := hsurj y
  refine ⟨sourceEquiv a, ?_⟩
  rw [hnatural, ha]

/-- The actual order-three overlap inclusion is onto on fundamental groups, independently of
the marked filling-extension naturality package. -/
public theorem actualOrderThreeOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  let D := A.actualVanKampenFourPieceCover
  let eX := A.orderThreeCollarToActualOverlapHomeomorph
  let eY := A.orderThreeFillingToActualPieceHomeomorph
  let f : C(A.starCollarSourceType 1, A.starFillingType 1) :=
    ⟨A.starToFilling 1, (A.starToFilling_isOpenEmbedding 1).continuous⟩
  let g := D.ellipticThreeOverlapToPiece
  let x' : (D.core ∩ D.ellipticThree : Set A.VanKampenSpace) :=
    ⟨D.ellipticThreePoint, D.ellipticThreePoint_mem⟩
  have hcomm : g.comp (⟨eX, eX.continuous⟩ : C(_, _)) =
      (⟨eY, eY.continuous⟩ : C(_, _)).comp f := by
    ext q
    change A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι none
        (A.openEmbeddingStarData.toCentral 1 q) =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 1)
        (A.openEmbeddingStarData.toFilling 1 q)
    symm
    apply (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
      (some 1) none (A.openEmbeddingStarData.toFilling 1 q)
        (A.openEmbeddingStarData.toCentral 1 q)).mpr
    refine ⟨A.openEmbeddingStarData.fillingCollarPoint 1 q, rfl, ?_⟩
    exact congrArg Subtype.val
      (A.openEmbeddingStarData.collarEquiv_symm_toFilling 1 q)
  have hsurj : Function.Surjective (FundamentalGroup.map f (eX.symm x')) := by
    exact A.orderThreePuncturedCollarToFilling_fundamentalGroup_surjective_at
      A.starSeparation.orderThree.radius_pos
      A.starSeparation.orderThree.radius_lt_one (eX.symm x')
  change Function.Surjective (FundamentalGroup.map g x')
  exact fundamentalGroup_map_surjective_of_homeomorph_square
    eX eY f g hcomm x' hsurj

/-- The actual order-four overlap inclusion is onto on fundamental groups, independently of
the marked filling-extension naturality package. -/
public theorem actualOrderFourOverlapFundamentalGroupMap_surjective :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  let D := A.actualVanKampenFourPieceCover
  let eX := A.orderFourCollarToActualOverlapHomeomorph
  let eY := A.orderFourFillingToActualPieceHomeomorph
  let f : C(A.starCollarSourceType 2, A.starFillingType 2) :=
    ⟨A.starToFilling 2, (A.starToFilling_isOpenEmbedding 2).continuous⟩
  let g := D.ellipticFourOverlapToPiece
  let x' : (D.core ∩ D.ellipticFour : Set A.VanKampenSpace) :=
    ⟨D.ellipticFourPoint, D.ellipticFourPoint_mem⟩
  have hcomm : g.comp (⟨eX, eX.continuous⟩ : C(_, _)) =
      (⟨eY, eY.continuous⟩ : C(_, _)).comp f := by
    ext q
    change A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι none
        (A.openEmbeddingStarData.toCentral 2 q) =
      A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.toGlueData.ι (some 2)
        (A.openEmbeddingStarData.toFilling 2 q)
    symm
    apply (A.openEmbeddingStarData.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
      (some 2) none (A.openEmbeddingStarData.toFilling 2 q)
        (A.openEmbeddingStarData.toCentral 2 q)).mpr
    refine ⟨A.openEmbeddingStarData.fillingCollarPoint 2 q, rfl, ?_⟩
    exact congrArg Subtype.val
      (A.openEmbeddingStarData.collarEquiv_symm_toFilling 2 q)
  have hsurj : Function.Surjective (FundamentalGroup.map f (eX.symm x')) := by
    exact A.orderFourPuncturedCollarToFilling_fundamentalGroup_surjective_at
      A.starSeparation.orderFour.radius_pos
      A.starSeparation.orderFour.radius_lt_one (eX.symm x')
  change Function.Surjective (FundamentalGroup.map g x')
  exact fundamentalGroup_map_surjective_of_homeomorph_square
    eX eY f g hcomm x' hsurj

namespace ActualEllipticCentralNaturality

variable {A} {N : A.ActualCuspCentralNaturality}

/-- The actual order-three collar inclusion is onto on fundamental groups. -/
public theorem orderThreeOverlapFundamentalGroupMap_surjective
    (E : ActualEllipticCentralNaturality A N) :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap := by
  rw [← E.orderThreeMap_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    E.orderThreeBoundaryBase_eq E.orderThreeFillingBase_eq
    E.orderThreeCover.fundamentalGroupMap
    E.orderThreeCover.fundamentalGroupMap_surjective

/-- The actual order-four collar inclusion is onto on fundamental groups. -/
public theorem orderFourOverlapFundamentalGroupMap_surjective
    (E : ActualEllipticCentralNaturality A N) :
    Function.Surjective
      A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap := by
  rw [← E.orderFourMap_eq]
  exact fundamentalGroupHomOfBaseEq_surjective
    E.orderFourBoundaryBase_eq E.orderFourFillingBase_eq
    E.orderFourCover.fundamentalGroupMap
    E.orderFourCover.fundamentalGroupMap_surjective

/-- The order-three filling kills the marked cyclic affine relation at twist `epsilon`. -/
public theorem orderThreeRelation_killed (E : ActualEllipticCentralNaturality A N) :
    A.actualVanKampenFourPieceCover.ellipticThreeOverlapFundamentalGroupMap
        ((fundamentalGroupElementOfBaseEq E.orderThreeBoundaryBase_eq
            E.orderThreeCover.meridian) ^ 3 *
          (Additive.toMul
            (fundamentalGroupAddHomOfBaseEq E.orderThreeBoundaryBase_eq
              E.orderThreeCover.translation epsilon))⁻¹) = 1 := by
  rw [← E.orderThreeMap_eq]
  exact chosenCyclicRelation_killed E.orderThreeCover E.orderThreeBoundaryBase_eq
    E.orderThreeFillingBase_eq E.orderThreeTwist_eq

/-- The order-four filling kills the marked cyclic affine relation at twist `-epsilon'`. -/
public theorem orderFourRelation_killed (E : ActualEllipticCentralNaturality A N) :
    A.actualVanKampenFourPieceCover.ellipticFourOverlapFundamentalGroupMap
        ((fundamentalGroupElementOfBaseEq E.orderFourBoundaryBase_eq
            E.orderFourCover.meridian) ^ 4 *
          (Additive.toMul
            (fundamentalGroupAddHomOfBaseEq E.orderFourBoundaryBase_eq
              E.orderFourCover.translation (-epsilon')))⁻¹) = 1 := by
  rw [← E.orderFourMap_eq]
  exact chosenCyclicRelation_killed E.orderFourCover E.orderFourBoundaryBase_eq
    E.orderFourFillingBase_eq E.orderFourTwist_eq

/-- The complete based affine star filling bridge for the actual four-piece cover. -/
public noncomputable def bridge (E : ActualEllipticCentralNaturality A N) :
    AffineTorusStarFillingBridge A.actualVanKampenFourPieceCover
      (A.coreDataOf N) 3 4 epsilon (-epsilon') 0 paperToricSubgroup where
  cuspSurjective := A.actualCuspOverlapFundamentalGroupMap_surjective
  oneSurjective := A.actualOrderThreeOverlapFundamentalGroupMap_surjective
  twoSurjective := A.actualOrderFourOverlapFundamentalGroupMap_surjective
  cuspToCore := A.actualCuspOverlapToCore
  oneToCore := A.actualEllipticThreeOverlapToCore
  twoToCore := A.actualEllipticFourOverlapToCore
  cuspSquare := A.actualCuspAffineBridge_cuspSquare
  oneSquare := A.actualEllipticThreeAffineBridge_square
  twoSquare := A.actualEllipticFourAffineBridge_square
  cuspTranslation := A.actualCuspAffineBridgeTranslation
  cuspMeridian := A.actualCuspAffineBridgeMeridian
  cuspTranslation_core := A.cuspBridge_translation_core N
  cuspMeridian_core := A.cuspBridge_meridian_core N
  cuspMeridian_killed := A.actualCuspAffineBridge_meridian_killed
  cuspToric_killed := A.actualCuspAffineBridge_toric_killed
  oneTranslation := fundamentalGroupAddHomOfBaseEq E.orderThreeBoundaryBase_eq
    E.orderThreeCover.translation
  oneMeridian := fundamentalGroupElementOfBaseEq E.orderThreeBoundaryBase_eq
    E.orderThreeCover.meridian
  oneTranslation_core := E.orderThreeTranslation_naturality
  oneMeridian_core := E.orderThreeMeridian_naturality
  oneRelation_killed := E.orderThreeRelation_killed
  twoTranslation := fundamentalGroupAddHomOfBaseEq E.orderFourBoundaryBase_eq
    E.orderFourCover.translation
  twoMeridian := fundamentalGroupElementOfBaseEq E.orderFourBoundaryBase_eq
    E.orderFourCover.meridian
  twoTranslation_core := E.orderFourTranslation_naturality
  twoMeridian_core := E.orderFourMeridian_naturality
  twoRelation_killed := E.orderFourRelation_killed

/-- The three actual regular cover squares, assembled from the marked elliptic package and the
explicit cusp cover square. -/
public noncomputable def toActualAffineFillingCoverSquares
    (E : ActualEllipticCentralNaturality A N) :
    A.ActualAffineFillingCoverSquares where
  coreData := A.coreDataOf N
  centralToCore := N.centralToCore
  coreData_eq := rfl
  orderThreeCover := E.orderThreeCover
  orderThreeBoundaryBase_eq := E.orderThreeBoundaryBase_eq
  orderThreeFillingBase_eq := E.orderThreeFillingBase_eq
  orderThreeMap_eq := E.orderThreeMap_eq
  orderFourCover := E.orderFourCover
  orderFourBoundaryBase_eq := E.orderFourBoundaryBase_eq
  orderFourFillingBase_eq := E.orderFourFillingBase_eq
  orderFourMap_eq := E.orderFourMap_eq
  cuspCover := A.actualCuspChosenAffineFillingCover
  cuspBoundaryBase_eq := A.actualCuspChosenAffineFillingCover_boundaryBase_eq
  cuspFillingBase_eq := A.actualCuspChosenAffineFillingCover_fillingBase_eq
  cuspMap_eq := A.actualCuspChosenAffineFillingCover_map_eq
  bridge := E.bridge
  orderThreeTwist_eq := E.orderThreeTwist_eq
  orderThreeTranslation_eq := rfl
  orderThreeMeridian_eq := rfl
  orderFourTwist_eq := E.orderFourTwist_eq
  orderFourTranslation_eq := rfl
  orderFourMeridian_eq := rfl
  cuspTranslation_eq := rfl
  cuspMeridian_eq := rfl
  cuspVanishing_onto := A.actualCuspAffineBridge_vanishing_onto

end ActualEllipticCentralNaturality

/-- The two elliptic marked cover packages are the only missing inputs: together with any marked
cusp naturality they yield the full actual affine filling-cover square package. -/
public theorem nonempty_actualAffineFillingCoverSquares_of_ellipticNaturality
    (N : A.ActualCuspCentralNaturality) (E : ActualEllipticCentralNaturality A N) :
    Nonempty A.ActualAffineFillingCoverSquares :=
  ⟨E.toActualAffineFillingCoverSquares⟩

/-- Marked peripheral naturality for all three collars of the actual four-piece star.

The `cusp` field is the marked cusp naturality of `PaperCuspCentralNaturality`; the `elliptic`
field is its exact counterpart for the two elliptic collars, together with their chosen cyclic
regular-cover models. -/
public structure ActualStarPeripheralNaturality where
  cusp : A.ActualCuspCentralNaturality
  elliptic : ActualEllipticCentralNaturality A cusp

/-- The remaining elliptic filling-extension and finite-marking input.

For each filling, equivariance of the lift is required only over the marked boundary base point;
covering-map uniqueness propagates it over the entire connected collar cover. -/
public axiom establishedActualEllipticMarkedFillingExtensionAtBaseNaturality :
    Nonempty
      (ActualEllipticMarkedFillingExtensionAtBaseNaturality
        A A.actualCuspCentralNaturality)

/-- The former global-equivariance input, reconstructed from marked-point equivariance. -/
public theorem establishedActualEllipticMarkedFillingExtensionNaturality :
    Nonempty
      (ActualEllipticMarkedFillingExtensionNaturality A A.actualCuspCentralNaturality) :=
  A.establishedActualEllipticMarkedFillingExtensionAtBaseNaturality.map
    ActualEllipticMarkedFillingExtensionAtBaseNaturality.toFillingExtensionNaturality

/-- The former basis-naturality boundary, reconstructed from the explicit collar covers and the
remaining filling extensions and finite marking. -/
public theorem establishedActualEllipticCentralBasisNaturality :
    Nonempty (ActualEllipticCentralBasisNaturality A A.actualCuspCentralNaturality) :=
  A.establishedActualEllipticMarkedFillingExtensionNaturality.map
    ActualEllipticMarkedFillingExtensionNaturality.toActualEllipticCentralBasisNaturality

/-- The full elliptic naturality package, extended from finite monodromy-orbit anchors. -/
public theorem establishedActualEllipticCentralNaturality :
    Nonempty (ActualEllipticCentralNaturality A A.actualCuspCentralNaturality) :=
  A.establishedActualEllipticCentralBasisNaturality.map
    ActualEllipticCentralBasisNaturality.toActualEllipticCentralNaturality

/-- Marked peripheral naturality for all three actual collars.  The cusp half is now proved
(`actualCuspCentralNaturality`), so only the elliptic half remains assumed. -/
public theorem establishedActualStarPeripheralNaturality :
    Nonempty A.ActualStarPeripheralNaturality :=
  A.establishedActualEllipticCentralNaturality.elim fun E ↦
    ⟨{ cusp := A.actualCuspCentralNaturality, elliptic := E }⟩

/-- The three actual regular cover squares exist, given the star's peripheral naturality. -/
public theorem nonempty_actualAffineFillingCoverSquares :
    Nonempty A.ActualAffineFillingCoverSquares :=
  A.establishedActualStarPeripheralNaturality.elim fun P ↦
    nonempty_actualAffineFillingCoverSquares_of_ellipticNaturality A P.cusp P.elliptic

end SphereSixComplex.Geometry.PaperAnalyticData

end
