module

public import SphereSixComplex.Topology.BinaryOpenCoverOrientedRefinementNaturality
public import SphereSixComplex.Topology.CanonicalProductWangBoundarySlant
public import SphereSixComplex.Topology.NormalizedFiniteOrderAdditiveCircleSweepProof

/-!
# Fixed-loop sweeps and the Wang boundary

This file constructs the map of explicit cylinder mapping tori induced by a pointwise fixed
parametrized loop.  Because it preserves the cylinder coordinate literally, it also preserves the
vertex/edge cover used to define the Wang boundary.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Topology.FixedLoopSweepWangBoundary

open CircleProductIdentityMappingTorus
open CanonicalProductWangBoundarySlant
open CyclicAngularFundamentalDomain
open NormalizedFiniteOrderAdditiveCircleSweep
open NormalizedFiniteOrderAdditiveCircleSweepProof
open PositiveCircleCross
open StandardTorusHomology

public theorem canonicalOpenCoverBoundary_eq_naturality
    {X : TopCat} {U V U' V' : Opens X}
    (hU : U = U') (hV : V = V')
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤) (n : ℕ) :
    (BinaryOpenCover.openCoverHomologyComparisonOfCover hcover).boundary n ≫
        BinaryOpenCover.openIntersectionRefinementHomologyMap
          (le_of_eq hU) (le_of_eq hV) n =
      (BinaryOpenCover.openCoverHomologyComparisonOfCover hcover').boundary n := by
  subst U'
  subst V'
  have hp : hcover' = hcover := Subsingleton.elim _ _
  cases hp
  change (BinaryOpenCover.openCoverHomologyComparisonOfCover hcover).boundary n ≫
      (BinaryOpenCover.integralHomologyFunctor n).map
        (BinaryOpenCover.openIntersectionRefinementMap
          (le_of_eq rfl) (le_of_eq rfl)) = _
  rw [show BinaryOpenCover.openIntersectionRefinementMap
      (le_of_eq (rfl : U = U)) (le_of_eq (rfl : V = V)) = 𝟙 _ by rfl]
  rw [(BinaryOpenCover.integralHomologyFunctor n).map_id, Category.comp_id]

private theorem fixedLoop_apply'
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (x : StdTorus 1) :
    phi (c.1 x) = c.1 x := by
  have h := LinearMap.mem_ker.mp c.2
  have hx := DFunLike.congr_fun h x
  apply sub_eq_zero.mp
  simpa [loopAction] using hx

public def fixedLoopCylinderPreMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    C(Unit × unitInterval × StdTorus 1, Unit × unitInterval × G) where
  toFun p := (p.1, p.2.1, c.1 p.2.2)
  continuous_toFun := continuous_fst.prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      (c.1.continuous.comp (continuous_snd.comp continuous_snd)))

public theorem fixedLoopCylinderPreMap_relation
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi)
    {p q : Unit × unitInterval × StdTorus 1}
    (h : finiteBouquetMappingTorusRelation
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) p q) :
    finiteBouquetMappingTorusRelation (fun _ : Unit ↦ phi.toHomeomorph)
      (fixedLoopCylinderPreMap phi c p) (fixedLoopCylinderPreMap phi c q) := by
  rcases h with h | h | h
  · exact Or.inl ⟨h.1, congrArg (fun z ↦ (z.1, c.1 z.2)) h.2⟩
  · exact Or.inr (Or.inl ⟨h.1, h.2.1, congrArg c.1 h.2.2⟩)
  · refine Or.inr (Or.inr ⟨h.1, h.2.1, ?_⟩)
    change c.1 q.2.2 = phi (c.1 p.2.2)
    have hqp : q.2.2 = p.2.2 := by simpa using h.2.2
    rw [hqp]
    exact (fixedLoop_apply' phi c p.2.2).symm

public theorem fixedLoopCylinderPreMap_setoid
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi)
    {p q : Unit × unitInterval × StdTorus 1}
    (hpq : Relation.EqvGen (finiteBouquetMappingTorusRelation
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) p q) :
    Relation.EqvGen (finiteBouquetMappingTorusRelation
      (fun _ : Unit ↦ phi.toHomeomorph))
        (fixedLoopCylinderPreMap phi c p) (fixedLoopCylinderPreMap phi c q) := by
  induction hpq with
  | rel p q h =>
      exact Relation.EqvGen.rel _ _ (fixedLoopCylinderPreMap_relation phi c h)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q h ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r hpq hqr ihpq ihqr => exact Relation.EqvGen.trans _ _ _ ihpq ihqr

/-- The map of explicit one-loop mapping tori induced by a pointwise fixed parametrized loop. -/
public def fixedLoopCylinderMappingTorusMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)),
      CircleMappingTorus phi.toHomeomorph) where
  toFun := @Quotient.map _ _
    (finiteBouquetMappingTorusSetoid
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
    (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi.toHomeomorph))
    (fixedLoopCylinderPreMap phi c)
    (fun _ _ h ↦ fixedLoopCylinderPreMap_setoid phi c h)
  continuous_toFun := continuous_quot_lift _
    (continuous_quot_mk.comp (fixedLoopCylinderPreMap phi c).continuous)

@[simp]
public theorem fixedLoopCylinderMappingTorusMap_mk
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi)
    (p : Unit × unitInterval × StdTorus 1) :
    fixedLoopCylinderMappingTorusMap phi c
        (bouquetMk (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) p) =
      bouquetMk (fun _ : Unit ↦ phi.toHomeomorph)
        (p.1, p.2.1, c.1 p.2.2) := by
  have hmap := @Quotient.map_mk
    (Unit × unitInterval × StdTorus 1) (Unit × unitInterval × G)
    (finiteBouquetMappingTorusSetoid
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
    (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi.toHomeomorph))
    (fixedLoopCylinderPreMap phi c)
    (fun {_ _} h ↦ fixedLoopCylinderPreMap_setoid phi c h) p
  change (@Quotient.map _ _
      (finiteBouquetMappingTorusSetoid
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
      (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi.toHomeomorph))
      (fixedLoopCylinderPreMap phi c)
      (fun {_ _} h ↦ fixedLoopCylinderPreMap_setoid phi c h))
        (Quotient.mk _ p) =
      Quotient.mk _ (fixedLoopCylinderPreMap phi c p)
  exact hmap

public theorem fixedLoopCylinderMappingTorusMap_mem_bouquetPiece_iff
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (s : Set unitInterval)
    (hs : (0 : unitInterval) ∈ s ↔ (1 : unitInterval) ∈ s)
    (z : CircleMappingTorus (Homeomorph.refl (StdTorus 1))) :
    fixedLoopCylinderMappingTorusMap phi c z ∈
        bouquetPiece (fun _ : Unit ↦ phi.toHomeomorph) s ↔
      z ∈ bouquetPiece
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) s := by
  obtain ⟨p, rfl⟩ := bouquetMk_surjective
    (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) z
  rw [fixedLoopCylinderMappingTorusMap_mk,
    mem_bouquetPiece_mk_iff (fun _ : Unit ↦ phi.toHomeomorph) hs,
    mem_bouquetPiece_mk_iff
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) hs]

public theorem fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi)
    (z : CircleMappingTorus (Homeomorph.refl (StdTorus 1))) :
    fixedLoopCylinderMappingTorusMap phi c z ∈
        vertexPiece (fun _ : Unit ↦ phi.toHomeomorph) ↔
      z ∈ vertexPiece
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  exact fixedLoopCylinderMappingTorusMap_mem_bouquetPiece_iff
    phi c vertexBand vertexBand_ends z

public theorem fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi)
    (z : CircleMappingTorus (Homeomorph.refl (StdTorus 1))) :
    fixedLoopCylinderMappingTorusMap phi c z ∈
        edgePiece (fun _ : Unit ↦ phi.toHomeomorph) ↔
      z ∈ edgePiece
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  exact fixedLoopCylinderMappingTorusMap_mem_bouquetPiece_iff
    phi c edgeBand edgeBand_ends z

public def fixedLoopCylinderTopCatMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    TopCat.of (CircleMappingTorus (Homeomorph.refl (StdTorus 1))) ⟶
      TopCat.of (CircleMappingTorus phi.toHomeomorph) :=
  TopCat.ofHom (fixedLoopCylinderMappingTorusMap phi c)

public theorem fixedLoopCylinderTopCatMap_vertexOpen
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph)) =
      coverVertexOpen
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  ext z
  change fixedLoopCylinderMappingTorusMap phi c z ∈
      vertexPiece (fun _ : Unit ↦ phi.toHomeomorph) ↔
    z ∈ vertexPiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
  exact fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff phi c z

public theorem fixedLoopCylinderTopCatMap_edgeOpen
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) =
      coverEdgeOpen
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  ext z
  change fixedLoopCylinderMappingTorusMap phi c z ∈
      edgePiece (fun _ : Unit ↦ phi.toHomeomorph) ↔
    z ∈ edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
  exact fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff phi c z

public theorem fixedLoopCylinderPullbackOpenCover
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
          (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph)) ⊔
        (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
          (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) = ⊤ := by
  rw [fixedLoopCylinderTopCatMap_vertexOpen,
    fixedLoopCylinderTopCatMap_edgeOpen]
  exact coverOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))

public noncomputable def fixedLoopCylinderPullbackHomologyComparison
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    BinaryOpenCover.OpenCoverHomologyComparison
      ((Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph)))
      ((Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph))) :=
  BinaryOpenCover.openCoverHomologyComparisonOfCover
    (fixedLoopCylinderPullbackOpenCover phi c)

public theorem fixedLoopCylinderBoundary_pullback_naturality
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    (fixedLoopCylinderPullbackHomologyComparison phi c).boundary n ≫
        BinaryOpenCover.openIntersectionPullbackHomologyMap
          (fixedLoopCylinderTopCatMap phi c)
          (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
          (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) n =
      (BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (fixedLoopCylinderTopCatMap phi c) ≫
        (coverHomologyComparison
          (fun _ : Unit ↦ phi.toHomeomorph)).boundary n := by
  apply BinaryOpenCover.OpenCoverHomologyComparison.boundary_pullback_naturality
  exact BinaryOpenCover.openCoverHomologyComparisonOfCover_pullbackNaturality
    (fixedLoopCylinderTopCatMap phi c)
    (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
    (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph))
    (fixedLoopCylinderPullbackOpenCover phi c)
    (coverOpen (fun _ : Unit ↦ phi.toHomeomorph))

public theorem fixedLoopCylinderPullbackHomologyComparison_heq
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    HEq (fixedLoopCylinderPullbackHomologyComparison phi c)
      (coverHomologyComparison
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) := by
  simp only [fixedLoopCylinderPullbackHomologyComparison]
  unfold coverHomologyComparison
  congr
  · exact fixedLoopCylinderTopCatMap_vertexOpen phi c
  · exact fixedLoopCylinderTopCatMap_edgeOpen phi c
  · exact proof_irrel_heq _ _

public theorem fixedLoopCylinderPullbackBoundary_heq
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    HEq ((fixedLoopCylinderPullbackHomologyComparison phi c).boundary n)
      ((coverHomologyComparison
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))).boundary n) := by
  unfold fixedLoopCylinderPullbackHomologyComparison coverHomologyComparison
  congr
  all_goals first
    | exact fixedLoopCylinderTopCatMap_vertexOpen phi c
    | exact fixedLoopCylinderTopCatMap_edgeOpen phi c
    | exact proof_irrel_heq _ _

public theorem identityMappingTorusBoundary_positiveCircleProductGenerator :
    (circleMappingTorusWangPresentationOfCover
        (Homeomorph.refl (StdTorus 1)) 1).boundary
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator) =
      standardCircleHomologyGenerator := by
  exact canonicalProductWangBoundary_positiveGenerator

public theorem identityMappingTorusCoverBoundary_positiveCircleProductGenerator :
    (overlapEquiv
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1).symm
      (coverBoundary
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1
        ((unionEquiv
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 2).symm
          (integralSingularHomologyMap 2
            (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
              C(UnitAddCircle × StdTorus 1,
                CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
            positiveCircleProductGenerator))) =
      (fun _ : Unit ↦ standardCircleHomologyGenerator,
        fun _ : Unit ↦ -standardCircleHomologyGenerator) := by
  let z := integralSingularHomologyMap 2
    (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
      C(UnitAddCircle × StdTorus 1,
        CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
    positiveCircleProductGenerator
  let p := (overlapEquiv
    (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1).symm
      (coverBoundary
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1
        ((unionEquiv
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 2).symm z))
  have hfst : p.1 () = standardCircleHomologyGenerator := by
    exact identityMappingTorusBoundary_positiveCircleProductGenerator
  have hsnd := coverWangBoundary_snd_eq_neg_fst
    (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1 z
  change p.2 = -p.1 at hsnd
  apply Prod.ext
  · funext i
    cases i
    exact hfst
  · funext i
    cases i
    rw [hsnd]
    exact congrArg Neg.neg hfst

public theorem fixedLoopCylinderMappingTorusMap_comp_productHomeomorph
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    (fixedLoopCylinderMappingTorusMap phi c).comp
        (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
          C(UnitAddCircle × StdTorus 1,
            CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) =
      fixedLoopMappingTorusMap phi c := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  change fixedLoopCylinderMappingTorusMap phi c
      (circleProductIdentityMappingTorusHomeomorph ((t : UnitAddCircle), x)) =
    realMappingTorusHomeomorph phi.toHomeomorph
      (fixedLoopRealMappingTorusMap phi c
        (circleProductRealMappingTorusHomeomorph ((t : UnitAddCircle), x)))
  rw [circleProductIdentityMappingTorusHomeomorph, Homeomorph.trans_apply]
  have hreal := circleProductRealMappingTorusHomeomorph_real
    (X := StdTorus 1) (t, x)
  change circleProductRealMappingTorusHomeomorph ((t : UnitAddCircle), x) = _ at hreal
  rw [hreal]
  change fixedLoopCylinderMappingTorusMap phi c
      (realMappingTorusHomeomorph (Homeomorph.refl (StdTorus 1))
        (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x))) =
    realMappingTorusHomeomorph phi.toHomeomorph
      (fixedLoopRealMappingTorusMap phi c
        (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)))
  let Ds := realMappingTorusClutchingData (Homeomorph.refl (StdTorus 1))
  let Dt := realMappingTorusClutchingData phi.toHomeomorph
  apply Dt.circleToTotal_bijective.1
  change Dt.circleToTotal
      (fixedLoopCylinderMappingTorusMap phi c
        (Ds.totalHomeomorphCircleMappingTorus
          (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)))) =
    Dt.circleToTotal
      (Dt.totalHomeomorphCircleMappingTorus
        (fixedLoopRealMappingTorusMap phi c
          (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x))))
  have ht := Dt.totalHomeomorphCircleMappingTorus.symm_apply_apply
    (fixedLoopRealMappingTorusMap phi c
      (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)))
  change Dt.circleToTotal
      (Dt.totalHomeomorphCircleMappingTorus
        (fixedLoopRealMappingTorusMap phi c
          (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)))) = _ at ht
  rw [ht]
  obtain ⟨p, hp⟩ := bouquetMk_surjective
    (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
    (Ds.totalHomeomorphCircleMappingTorus
      (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)))
  have hq : Ds.circleToTotal
      (bouquetMk (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) p) =
      Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x) := by
    rw [hp]
    exact Ds.totalHomeomorphCircleMappingTorus.symm_apply_apply _
  rw [← hp, fixedLoopCylinderMappingTorusMap_mk, ← hq]
  change Dt.circleToTotal
      (circleMappingTorusCylinderProjection phi.toHomeomorph
        (p.2.1, c.1 p.2.2)) =
    fixedLoopRealMappingTorusMap phi c
      (Ds.circleToTotal
        (circleMappingTorusCylinderProjection (Homeomorph.refl (StdTorus 1))
          (p.2.1, p.2.2)))
  rw [Dt.circleToTotal_mk, Ds.circleToTotal_mk]
  rfl

public theorem fixedLoopSweepClass_eq_cylinderMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    fixedLoopSweepClass phi c =
      integralSingularHomologyMap 2 (fixedLoopCylinderMappingTorusMap phi c)
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
  positiveCircleProductGenerator) := by
  unfold fixedLoopSweepClass
  rw [← fixedLoopCylinderMappingTorusMap_comp_productHomeomorph]
  rw [integralSingularHomologyMap_comp_wang]

public def fixedLoopCylinderOverlapMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    C(↥(vertexPiece
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
        edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))),
      ↥(vertexPiece (fun _ : Unit ↦ phi.toHomeomorph) ∩
        edgePiece (fun _ : Unit ↦ phi.toHomeomorph))) where
  toFun z := ⟨fixedLoopCylinderMappingTorusMap phi c z,
    ⟨(fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff phi c z).2 z.2.1,
      (fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff phi c z).2 z.2.2⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((fixedLoopCylinderMappingTorusMap phi c).continuous.comp continuous_subtype_val) _

public theorem fixedLoopCylinderOverlapMap_lowPt
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    (fixedLoopCylinderOverlapMap phi c).comp
        (overlapPt
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
          uQuarter_mem_overlapBand ()) =
      (overlapPt (fun _ : Unit ↦ phi.toHomeomorph)
        uQuarter_mem_overlapBand ()).comp c.1 := by
  apply ContinuousMap.ext
  intro x
  rfl

public theorem fixedLoopCylinderOverlapMap_lowPt_homology
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ)
    (x : IntegralSingularHomology n (StdTorus 1)) :
    integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
        (integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uQuarter_mem_overlapBand ()) x) =
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi.toHomeomorph)
          uQuarter_mem_overlapBand ())
        (integralSingularHomologyMap n c.1 x) := by
  have hleft : integralSingularHomologyMap n
      ((fixedLoopCylinderOverlapMap phi c).comp
        (overlapPt
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
          uQuarter_mem_overlapBand ())) x =
      integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
        (integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uQuarter_mem_overlapBand ()) x) := by
    rw [integralSingularHomologyMap_comp_wang]
  have hright : integralSingularHomologyMap n
      ((overlapPt (fun _ : Unit ↦ phi.toHomeomorph)
        uQuarter_mem_overlapBand ()).comp c.1) x =
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi.toHomeomorph)
          uQuarter_mem_overlapBand ())
        (integralSingularHomologyMap n c.1 x) := by
    rw [integralSingularHomologyMap_comp_wang]
  calc
    _ = integralSingularHomologyMap n
        ((fixedLoopCylinderOverlapMap phi c).comp
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uQuarter_mem_overlapBand ())) x :=
      hleft.symm
    _ = integralSingularHomologyMap n
        ((overlapPt (fun _ : Unit ↦ phi.toHomeomorph)
          uQuarter_mem_overlapBand ()).comp c.1) x := by
      rw [fixedLoopCylinderOverlapMap_lowPt]
    _ = _ := hright

public theorem fixedLoopCylinderPullbackOverlap_membership_fun
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    (fun z : CircleMappingTorus (Homeomorph.refl (StdTorus 1)) ↦
      z ∈
        (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
            (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph)) ⊓
          (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
            (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph))) =
      fun z ↦ z ∈
        (vertexPiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
          edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) := by
  funext z
  apply propext
  change
    (fixedLoopCylinderMappingTorusMap phi c z ∈
        vertexPiece (fun _ : Unit ↦ phi.toHomeomorph) ∧
      fixedLoopCylinderMappingTorusMap phi c z ∈
        edgePiece (fun _ : Unit ↦ phi.toHomeomorph)) ↔
      z ∈ vertexPiece
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∧
        z ∈ edgePiece
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
  exact and_congr
    (fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff phi c z)
    (fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff phi c z)

public def fixedLoopCylinderSourceOverlapToPullback
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    TopCat.of ↥(vertexPiece
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
        edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) ⟶
      (Opens.toTopCat
        (TopCat.of (CircleMappingTorus (Homeomorph.refl (StdTorus 1))))).obj
        ((Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
            (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph)) ⊓
          (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
            (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph))) :=
  TopCat.ofHom
    { toFun := fun z ↦ ⟨z, ⟨
        (fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff phi c z).2 z.2.1,
        (fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff phi c z).2 z.2.2⟩⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }

public theorem fixedLoopCylinderSourceOverlapToPullback_eq_refinement
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    fixedLoopCylinderSourceOverlapToPullback phi c =
      BinaryOpenCover.openIntersectionRefinementMap
        (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
        (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) := by
  ext z
  rfl

public theorem fixedLoopCylinderLegacyOverlap_comp_refinement
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    (TopCat.isoOfHomeo
          (BinaryOpenCover.opensIntersectionHomeomorph
            (coverVertexOpen
              (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
            (coverEdgeOpen
              (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))))).hom ≫
        BinaryOpenCover.openIntersectionRefinementMap
          (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
          (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) =
      fixedLoopCylinderSourceOverlapToPullback phi c := by
  ext z
  rfl

public theorem fixedLoopCylinderLegacyOverlap_homology_comp_refinement
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    (BinaryOpenCover.opensIntersectionHomologyIso
          (coverVertexOpen
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverEdgeOpen
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) n).hom ≫
        BinaryOpenCover.openIntersectionRefinementHomologyMap
          (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
          (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) n =
      (BinaryOpenCover.integralHomologyFunctor n).map
        (fixedLoopCylinderSourceOverlapToPullback phi c) := by
  unfold BinaryOpenCover.opensIntersectionHomologyIso
    BinaryOpenCover.openIntersectionRefinementHomologyMap
  simp only [Functor.mapIso_hom]
  rw [← Functor.map_comp]
  exact congrArg (BinaryOpenCover.integralHomologyFunctor n).map
    (fixedLoopCylinderLegacyOverlap_comp_refinement phi c)

public theorem fixedLoopCylinderSourceOverlapToPullback_comp_preimage
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) :
    fixedLoopCylinderSourceOverlapToPullback phi c ≫
        BinaryOpenCover.openIntersectionPreimageMap
        (fixedLoopCylinderTopCatMap phi c)
        (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
        (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) =
      TopCat.ofHom (fixedLoopCylinderOverlapMap phi c) := by
  ext z
  rfl

public theorem fixedLoopCylinderSourceOverlapToPullback_homology
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    (BinaryOpenCover.integralHomologyFunctor n).map
          (fixedLoopCylinderSourceOverlapToPullback phi c) ≫
        BinaryOpenCover.openIntersectionPullbackHomologyMap
          (fixedLoopCylinderTopCatMap phi c)
          (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
          (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) n =
      (BinaryOpenCover.integralHomologyFunctor n).map
        (TopCat.ofHom (fixedLoopCylinderOverlapMap phi c)) := by
  unfold BinaryOpenCover.openIntersectionPullbackHomologyMap
  rw [← Functor.map_comp,
    fixedLoopCylinderSourceOverlapToPullback_comp_preimage]
  rfl

public theorem fixedLoopCylinderSourceBoundary_toPullback
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    (coverHomologyComparison
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))).boundary n ≫
        BinaryOpenCover.openIntersectionRefinementHomologyMap
          (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
          (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) n =
      (fixedLoopCylinderPullbackHomologyComparison phi c).boundary n := by
  have h := canonicalOpenCoverBoundary_eq_naturality
    (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm
    (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm
    (coverOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
    (fixedLoopCylinderPullbackOpenCover phi c) n
  unfold coverHomologyComparison fixedLoopCylinderPullbackHomologyComparison
  exact h

public noncomputable def fixedLoopCylinderLegacyIntersectionMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    IntegralSingularHomology n
        ↥(vertexPiece
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
          edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) →+
      IntegralSingularHomology n
        ↥(vertexPiece (fun _ : Unit ↦ phi.toHomeomorph) ∩
          edgePiece (fun _ : Unit ↦ phi.toHomeomorph)) :=
  ConcreteCategory.hom
    ((BinaryOpenCover.opensIntersectionHomologyIso
        (coverVertexOpen
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
        (coverEdgeOpen
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) n).hom ≫
      BinaryOpenCover.openIntersectionRefinementHomologyMap
        (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
        (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) n ≫
      BinaryOpenCover.openIntersectionPullbackHomologyMap
        (fixedLoopCylinderTopCatMap phi c)
        (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
        (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) n ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
        (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) n).inv)

public noncomputable def fixedLoopCylinderLegacyUnionMap
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    IntegralSingularHomology n
        ↥(vertexPiece
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∪
          edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) →+
      IntegralSingularHomology n
        ↥(vertexPiece (fun _ : Unit ↦ phi.toHomeomorph) ∪
          edgePiece (fun _ : Unit ↦ phi.toHomeomorph)) :=
  ConcreteCategory.hom
    ((BinaryOpenCover.opensUnionHomologyIso
        (coverVertexOpen
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
        (coverEdgeOpen
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
        (coverOpen
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) n).hom ≫
      (BinaryOpenCover.integralHomologyFunctor n).map
        (fixedLoopCylinderTopCatMap phi c) ≫
      (BinaryOpenCover.opensUnionHomologyIso
        (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
        (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph))
        (coverOpen (fun _ : Unit ↦ phi.toHomeomorph)) n).inv)

public theorem fixedLoopCylinderBoundary_refinement_pullback_naturality
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ) :
    (coverHomologyComparison
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))).boundary n ≫
        BinaryOpenCover.openIntersectionRefinementHomologyMap
          (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
          (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) n ≫
        BinaryOpenCover.openIntersectionPullbackHomologyMap
          (fixedLoopCylinderTopCatMap phi c)
          (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
          (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) n =
      (BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (fixedLoopCylinderTopCatMap phi c) ≫
        (coverHomologyComparison
          (fun _ : Unit ↦ phi.toHomeomorph)).boundary n := by
  rw [← Category.assoc, fixedLoopCylinderSourceBoundary_toPullback]
  exact fixedLoopCylinderBoundary_pullback_naturality phi c n

public theorem fixedLoopCylinderPullbackIntersection_lowPt_homology
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : FixedLoop phi) (n : ℕ)
    (x : IntegralSingularHomology n (StdTorus 1)) :
    ConcreteCategory.hom
        ((BinaryOpenCover.integralHomologyFunctor n).map
            (fixedLoopCylinderSourceOverlapToPullback phi c) ≫
          BinaryOpenCover.openIntersectionPullbackHomologyMap
            (fixedLoopCylinderTopCatMap phi c)
            (coverVertexOpen (fun _ : Unit ↦ phi.toHomeomorph))
            (coverEdgeOpen (fun _ : Unit ↦ phi.toHomeomorph)) n)
        (integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uQuarter_mem_overlapBand ()) x) =
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi.toHomeomorph)
          uQuarter_mem_overlapBand ())
        (integralSingularHomologyMap n c.1 x) := by
  have hcat := fixedLoopCylinderSourceOverlapToPullback_homology phi c n
  have hfun := congrArg ConcreteCategory.hom hcat
  have happ := DFunLike.congr_fun hfun
    (integralSingularHomologyMap n
      (overlapPt
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
        uQuarter_mem_overlapBand ()) x)
  change _ = integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
      (integralSingularHomologyMap n
        (overlapPt
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
          uQuarter_mem_overlapBand ()) x) at happ
  rw [fixedLoopCylinderOverlapMap_lowPt_homology] at happ
  exact happ

end SphereSixComplex.Topology.FixedLoopSweepWangBoundary

end

end
