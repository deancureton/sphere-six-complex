module

public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverOrientedRefinementNaturality
public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundaryPositiveGenerator
public import SphereSixComplex.Prerequisites.Topology.NormalizedFiniteOrderAdditiveCircleSweepProof

/-!
# Fixed-circle sweeps and the Wang boundary

This file constructs the map of explicit cylinder mapping tori induced by a pointwise fixed
parametrized circle in an arbitrary topological space.  Because it preserves the cylinder coordinate literally, it also preserves the
vertex/edge cover used to define the Wang boundary.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary

open CircleProductIdentityMappingTorus
open CanonicalProductWangBoundarySlant
open CyclicAngularFundamentalDomain
open NormalizedFiniteOrderAdditiveCircleSweep
open CyclicMappingTorus.CircleSweep
open PositiveCircleCross
open StandardTorusHomology

public abbrev FixedTopologicalCircle {G : Type} [TopologicalSpace G] (phi : G ≃ₜ G) :=
  {c : C(StdTorus 1, G) // ∀ x, phi (c x) = c x}

private theorem fixedLoop_apply
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (x : StdTorus 1) :
    phi (c.1 x) = c.1 x := by
  exact c.2 x

private theorem fixedLoop_zpow_apply
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (k : ℤ) (x : StdTorus 1) :
    (phi ^ k) (c.1 x) = c.1 x := by
  refine Int.induction_on (motive := fun n ↦
    (phi ^ n) (c.1 x) = c.1 x) k ?_ ?_ ?_
  · rfl
  · intro i hi
    rw [zpow_add_one]
    change (phi ^ (i : ℤ)) (phi (c.1 x)) = c.1 x
    rw [fixedLoop_apply phi c x, hi]
  · intro i hi
    rw [zpow_sub_one]
    change (phi ^ (-(i : ℤ))) (phi.symm (c.1 x)) = c.1 x
    have hinv : phi.symm (c.1 x) = c.1 x := by
      apply phi.injective
      rw [phi.apply_symm_apply, fixedLoop_apply phi c x]
    rw [hinv, hi]

public def fixedLoopRealPreMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) : C(ℝ × StdTorus 1, ℝ × G) where
  toFun p := (p.1, c.1 p.2)
  continuous_toFun := continuous_fst.prodMk (c.1.continuous.comp continuous_snd)

/-- A pointwise fixed parametrized loop induces a map from the identity mapping torus into the
mapping torus of the clutching map. -/
public noncomputable def fixedLoopRealMappingTorusMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    C(RealMappingTorus (Homeomorph.refl (StdTorus 1)),
      RealMappingTorus phi) where
  toFun := Quotient.map (fixedLoopRealPreMap phi c) fun p q hpq ↦ by
    change realMappingTorusSetoid (Homeomorph.refl (StdTorus 1)) p q at hpq
    change realMappingTorusSetoid phi
      (fixedLoopRealPreMap phi c p) (fixedLoopRealPreMap phi c q)
    obtain ⟨k, hk⟩ := hpq
    refine ⟨k, ?_⟩
    rw [hk, mappingTorusShift_apply, mappingTorusShift_apply]
    apply Prod.ext
    · rfl
    · change c.1 (((Homeomorph.refl (StdTorus 1)) ^ k) p.2) =
        (phi ^ k) (c.1 p.2)
      rw [show Homeomorph.refl (StdTorus 1) = 1 by rfl, one_zpow]
      exact (fixedLoop_zpow_apply phi c k p.2).symm
  continuous_toFun := continuous_quot_lift _
    (continuous_quot_mk.comp (fixedLoopRealPreMap phi c).continuous)

@[simp]
public theorem fixedLoopRealMappingTorusMap_mk
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (t : ℝ) (x : StdTorus 1) :
    fixedLoopRealMappingTorusMap phi c
        (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)) =
      Quotient.mk (realMappingTorusSetoid phi) (t, c.1 x) := by
  rfl

/-- The torus carried by a pointwise fixed parametrized loop in the mapping torus. -/
public noncomputable def fixedLoopMappingTorusMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    C(UnitAddCircle × StdTorus 1, CircleMappingTorus phi) :=
  (realMappingTorusHomeomorph phi :
      C(RealMappingTorus phi, CircleMappingTorus phi)).comp
    ((fixedLoopRealMappingTorusMap phi c).comp
      (circleProductRealMappingTorusHomeomorph (X := StdTorus 1) :
        C(UnitAddCircle × StdTorus 1,
          RealMappingTorus (Homeomorph.refl (StdTorus 1)))))

/-- The geometric degree-two class swept out by a pointwise fixed parametrized loop. -/
public noncomputable def fixedLoopSweepClass
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    IntegralSingularHomology 2 (CircleMappingTorus phi) :=
  integralSingularHomologyMap 2 (fixedLoopMappingTorusMap phi c)
    positiveCircleProductGenerator



private theorem opensIntersectionHomologyIso_inv_apply
    {X : TopCat} (U V : Opens X) (n : ℕ)
    (x : IntegralSingularHomology n ((Opens.toTopCat X).obj (U ⊓ V))) :
    ConcreteCategory.hom
        (BinaryOpenCover.opensIntersectionHomologyIso U V n).inv x = x := by
  have hinv :
      (TopCat.isoOfHomeo (BinaryOpenCover.opensIntersectionHomeomorph U V)).inv =
        𝟙 (TopCat.of ((U : Set X) ∩ (V : Set X) : Set X)) := by
    ext y
    rfl
  have hmap := congrArg (BinaryOpenCover.integralHomologyFunctor n).map hinv
  rw [(BinaryOpenCover.integralHomologyFunctor n).map_id] at hmap
  have hfun := congrArg ConcreteCategory.hom hmap
  exact DFunLike.congr_fun hfun x

private theorem opensUnionHomologyIso_hom_apply
    {ι F : Type} [Fintype ι] [Inhabited ι] [TopologicalSpace ι]
    [DiscreteTopology ι] [TopologicalSpace F]
    (φ : ι → F ≃ₜ F) (n : ℕ)
    (x : IntegralSingularHomology n
      (vertexPiece φ ∪ edgePiece φ : Set (FiniteBouquetMappingTorus φ))) :
    ConcreteCategory.hom
        (BinaryOpenCover.opensUnionHomologyIso
          (coverVertexOpen φ) (coverEdgeOpen φ) (coverOpen φ) n).hom x =
      unionEquiv φ n x := by
  have htop :
      (TopCat.isoOfHomeo (BinaryOpenCover.opensUnionHomeomorph
        (coverVertexOpen φ) (coverEdgeOpen φ) (coverOpen φ))).hom =
        TopCat.ofHom (coverUnionCM φ) := by
    ext y
    rfl
  have hmap := congrArg (BinaryOpenCover.integralHomologyFunctor n).map htop
  have hfun := congrArg ConcreteCategory.hom hmap
  exact DFunLike.congr_fun hfun x

private theorem opensUnionHomologyIso_inv_apply
    {ι F : Type} [Fintype ι] [Inhabited ι] [TopologicalSpace ι]
    [DiscreteTopology ι] [TopologicalSpace F]
    (φ : ι → F ≃ₜ F) (n : ℕ)
    (z : IntegralSingularHomology n (FiniteBouquetMappingTorus φ)) :
    ConcreteCategory.hom
        (BinaryOpenCover.opensUnionHomologyIso
          (coverVertexOpen φ) (coverEdgeOpen φ) (coverOpen φ) n).inv z =
      (unionEquiv φ n).symm z := by
  apply (unionEquiv φ n).injective
  calc
    _ = ConcreteCategory.hom
        (BinaryOpenCover.opensUnionHomologyIso
          (coverVertexOpen φ) (coverEdgeOpen φ) (coverOpen φ) n).hom
        (ConcreteCategory.hom
          (BinaryOpenCover.opensUnionHomologyIso
            (coverVertexOpen φ) (coverEdgeOpen φ) (coverOpen φ) n).inv z) :=
      (opensUnionHomologyIso_hom_apply φ n _).symm
    _ = z := by simp
    _ = unionEquiv φ n ((unionEquiv φ n).symm z) :=
      (AddEquiv.apply_symm_apply _ _).symm

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
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (x : StdTorus 1) :
    phi (c.1 x) = c.1 x := by
  exact c.2 x

public def fixedLoopCylinderPreMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    C(Unit × unitInterval × StdTorus 1, Unit × unitInterval × G) where
  toFun p := (p.1, p.2.1, c.1 p.2.2)
  continuous_toFun := continuous_fst.prodMk
    ((continuous_fst.comp continuous_snd).prodMk
      (c.1.continuous.comp (continuous_snd.comp continuous_snd)))

public theorem fixedLoopCylinderPreMap_relation
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi)
    {p q : Unit × unitInterval × StdTorus 1}
    (h : FiniteBouquetMappingTorusRel
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) p q) :
    FiniteBouquetMappingTorusRel (fun _ : Unit ↦ phi)
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
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi)
    {p q : Unit × unitInterval × StdTorus 1}
    (hpq : Relation.EqvGen (FiniteBouquetMappingTorusRel
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) p q) :
    Relation.EqvGen (FiniteBouquetMappingTorusRel
      (fun _ : Unit ↦ phi))
        (fixedLoopCylinderPreMap phi c p) (fixedLoopCylinderPreMap phi c q) := by
  induction hpq with
  | rel p q h =>
      exact Relation.EqvGen.rel _ _ (fixedLoopCylinderPreMap_relation phi c h)
  | refl p => exact Relation.EqvGen.refl _
  | symm p q h ih => exact Relation.EqvGen.symm _ _ ih
  | trans p q r hpq hqr ihpq ihqr => exact Relation.EqvGen.trans _ _ _ ihpq ihqr

/-- The map of explicit one-loop mapping tori induced by a pointwise fixed parametrized loop. -/
public def fixedLoopCylinderMappingTorusMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    C(CircleMappingTorus (Homeomorph.refl (StdTorus 1)),
      CircleMappingTorus phi) where
  toFun := @Quotient.map _ _
    (finiteBouquetMappingTorusSetoid
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
    (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi))
    (fixedLoopCylinderPreMap phi c)
    (fun _ _ h ↦ fixedLoopCylinderPreMap_setoid phi c h)
  continuous_toFun := continuous_quot_lift _
    (continuous_quot_mk.comp (fixedLoopCylinderPreMap phi c).continuous)

@[simp]
public theorem fixedLoopCylinderMappingTorusMap_mk
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi)
    (p : Unit × unitInterval × StdTorus 1) :
    fixedLoopCylinderMappingTorusMap phi c
        (bouquetMk (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) p) =
      bouquetMk (fun _ : Unit ↦ phi)
        (p.1, p.2.1, c.1 p.2.2) := by
  have hmap := @Quotient.map_mk
    (Unit × unitInterval × StdTorus 1) (Unit × unitInterval × G)
    (finiteBouquetMappingTorusSetoid
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
    (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi))
    (fixedLoopCylinderPreMap phi c)
    (fun {_ _} h ↦ fixedLoopCylinderPreMap_setoid phi c h) p
  change (@Quotient.map _ _
      (finiteBouquetMappingTorusSetoid
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
      (finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi))
      (fixedLoopCylinderPreMap phi c)
      (fun {_ _} h ↦ fixedLoopCylinderPreMap_setoid phi c h))
        (Quotient.mk _ p) =
      Quotient.mk _ (fixedLoopCylinderPreMap phi c p)
  exact hmap

public theorem fixedLoopCylinderMappingTorusMap_mem_bouquetPiece_iff
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (s : Set unitInterval)
    (hs : (0 : unitInterval) ∈ s ↔ (1 : unitInterval) ∈ s)
    (z : CircleMappingTorus (Homeomorph.refl (StdTorus 1))) :
    fixedLoopCylinderMappingTorusMap phi c z ∈
        bouquetPiece (fun _ : Unit ↦ phi) s ↔
      z ∈ bouquetPiece
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) s := by
  obtain ⟨p, rfl⟩ := bouquetMk_surjective
    (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) z
  rw [fixedLoopCylinderMappingTorusMap_mk,
    mem_bouquetPiece_mk_iff (fun _ : Unit ↦ phi) hs,
    mem_bouquetPiece_mk_iff
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) hs]

public theorem fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi)
    (z : CircleMappingTorus (Homeomorph.refl (StdTorus 1))) :
    fixedLoopCylinderMappingTorusMap phi c z ∈
        vertexPiece (fun _ : Unit ↦ phi) ↔
      z ∈ vertexPiece
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  exact fixedLoopCylinderMappingTorusMap_mem_bouquetPiece_iff
    phi c vertexBand vertexBand_ends z

public theorem fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi)
    (z : CircleMappingTorus (Homeomorph.refl (StdTorus 1))) :
    fixedLoopCylinderMappingTorusMap phi c z ∈
        edgePiece (fun _ : Unit ↦ phi) ↔
      z ∈ edgePiece
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  exact fixedLoopCylinderMappingTorusMap_mem_bouquetPiece_iff
    phi c edgeBand edgeBand_ends z

public def fixedLoopCylinderTopCatMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    TopCat.of (CircleMappingTorus (Homeomorph.refl (StdTorus 1))) ⟶
      TopCat.of (CircleMappingTorus phi) :=
  TopCat.ofHom (fixedLoopCylinderMappingTorusMap phi c)

public theorem fixedLoopCylinderTopCatMap_vertexOpen
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverVertexOpen (fun _ : Unit ↦ phi)) =
      coverVertexOpen
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  ext z
  change fixedLoopCylinderMappingTorusMap phi c z ∈
      vertexPiece (fun _ : Unit ↦ phi) ↔
    z ∈ vertexPiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
  exact fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff phi c z

public theorem fixedLoopCylinderTopCatMap_edgeOpen
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverEdgeOpen (fun _ : Unit ↦ phi)) =
      coverEdgeOpen
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) := by
  ext z
  change fixedLoopCylinderMappingTorusMap phi c z ∈
      edgePiece (fun _ : Unit ↦ phi) ↔
    z ∈ edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
  exact fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff phi c z

public theorem fixedLoopCylinderPullbackOpenCover
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
          (coverVertexOpen (fun _ : Unit ↦ phi)) ⊔
        (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
          (coverEdgeOpen (fun _ : Unit ↦ phi)) = ⊤ := by
  rw [fixedLoopCylinderTopCatMap_vertexOpen,
    fixedLoopCylinderTopCatMap_edgeOpen]
  exact coverOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))

public noncomputable def fixedLoopCylinderPullbackHomologyComparison
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    BinaryOpenCover.OpenCoverHomologyComparison
      ((Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverVertexOpen (fun _ : Unit ↦ phi)))
      ((Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
        (coverEdgeOpen (fun _ : Unit ↦ phi))) :=
  BinaryOpenCover.openCoverHomologyComparisonOfCover
    (fixedLoopCylinderPullbackOpenCover phi c)

public theorem fixedLoopCylinderBoundary_pullback_naturality
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ) :
    (fixedLoopCylinderPullbackHomologyComparison phi c).boundary n ≫
        BinaryOpenCover.openIntersectionPullbackHomologyMap
          (fixedLoopCylinderTopCatMap phi c)
          (coverVertexOpen (fun _ : Unit ↦ phi))
          (coverEdgeOpen (fun _ : Unit ↦ phi)) n =
      (BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (fixedLoopCylinderTopCatMap phi c) ≫
        (coverHomologyComparison
          (fun _ : Unit ↦ phi)).boundary n := by
  apply BinaryOpenCover.OpenCoverHomologyComparison.boundary_pullback_naturality
  exact BinaryOpenCover.openCoverHomologyComparisonOfCover_pullbackNaturality
    (fixedLoopCylinderTopCatMap phi c)
    (coverVertexOpen (fun _ : Unit ↦ phi))
    (coverEdgeOpen (fun _ : Unit ↦ phi))
    (fixedLoopCylinderPullbackOpenCover phi c)
    (coverOpen (fun _ : Unit ↦ phi))



public theorem identityMappingTorusBoundary_positiveCircleProductGenerator :
    (circleMappingTorusWangPresentationOfCover
        (Homeomorph.refl (StdTorus 1)) 1).boundary
        (integralSingularHomologyMap 2
          (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
            C(UnitAddCircle × StdTorus 1,
              CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
          positiveCircleProductGenerator) =
      standardCircleHomologyGenerator := by
  exact canonicalProductWangBoundary_positiveGenerator_core

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
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
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
    realMappingTorusHomeomorph phi
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
    realMappingTorusHomeomorph phi
      (fixedLoopRealMappingTorusMap phi c
        (Quotient.mk (realMappingTorusSetoid (Homeomorph.refl (StdTorus 1))) (t, x)))
  let Ds := realMappingTorusClutchingData (Homeomorph.refl (StdTorus 1))
  let Dt := realMappingTorusClutchingData phi
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
      (circleMappingTorusCylinderProjection phi
        (p.2.1, c.1 p.2.2)) =
    fixedLoopRealMappingTorusMap phi c
      (Ds.circleToTotal
        (circleMappingTorusCylinderProjection (Homeomorph.refl (StdTorus 1))
          (p.2.1, p.2.2)))
  rw [Dt.circleToTotal_mk, Ds.circleToTotal_mk]
  rfl

public theorem fixedLoopSweepClass_eq_cylinderMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
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
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    C(↥(vertexPiece
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
        edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))),
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩
        edgePiece (fun _ : Unit ↦ phi))) where
  toFun z := ⟨fixedLoopCylinderMappingTorusMap phi c z,
    ⟨(fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff phi c z).2 z.2.1,
      (fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff phi c z).2 z.2.2⟩⟩
  continuous_toFun := Continuous.subtype_mk
    ((fixedLoopCylinderMappingTorusMap phi c).continuous.comp continuous_subtype_val) _

public theorem fixedLoopCylinderOverlapMap_lowPt
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    (fixedLoopCylinderOverlapMap phi c).comp
        (overlapPt
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
          uQuarter_mem_overlapBand ()) =
      (overlapPt (fun _ : Unit ↦ phi)
        uQuarter_mem_overlapBand ()).comp c.1 := by
  apply ContinuousMap.ext
  intro x
  rfl

public theorem fixedLoopCylinderOverlapMap_lowPt_homology
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ)
    (x : IntegralSingularHomology n (StdTorus 1)) :
    integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
        (integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uQuarter_mem_overlapBand ()) x) =
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi)
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
      ((overlapPt (fun _ : Unit ↦ phi)
        uQuarter_mem_overlapBand ()).comp c.1) x =
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi)
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
        ((overlapPt (fun _ : Unit ↦ phi)
          uQuarter_mem_overlapBand ()).comp c.1) x := by
      rw [fixedLoopCylinderOverlapMap_lowPt]
    _ = _ := hright

public theorem fixedLoopCylinderOverlapMap_highPt
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    (fixedLoopCylinderOverlapMap phi c).comp
        (overlapPt
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
          uThreeQuarters_mem_overlapBand ()) =
      (overlapPt (fun _ : Unit ↦ phi)
        uThreeQuarters_mem_overlapBand ()).comp c.1 := by
  apply ContinuousMap.ext
  intro x
  rfl

public theorem fixedLoopCylinderOverlapMap_highPt_homology
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ)
    (x : IntegralSingularHomology n (StdTorus 1)) :
    integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
        (integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uThreeQuarters_mem_overlapBand ()) x) =
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi)
          uThreeQuarters_mem_overlapBand ())
        (integralSingularHomologyMap n c.1 x) := by
  have hleft : integralSingularHomologyMap n
      ((fixedLoopCylinderOverlapMap phi c).comp
        (overlapPt
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
          uThreeQuarters_mem_overlapBand ())) x =
      integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
        (integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uThreeQuarters_mem_overlapBand ()) x) := by
    rw [integralSingularHomologyMap_comp_wang]
  have hright : integralSingularHomologyMap n
      ((overlapPt (fun _ : Unit ↦ phi)
        uThreeQuarters_mem_overlapBand ()).comp c.1) x =
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi)
          uThreeQuarters_mem_overlapBand ())
        (integralSingularHomologyMap n c.1 x) := by
    rw [integralSingularHomologyMap_comp_wang]
  calc
    _ = integralSingularHomologyMap n
        ((fixedLoopCylinderOverlapMap phi c).comp
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uThreeQuarters_mem_overlapBand ())) x := hleft.symm
    _ = integralSingularHomologyMap n
        ((overlapPt (fun _ : Unit ↦ phi)
          uThreeQuarters_mem_overlapBand ()).comp c.1) x := by
      rw [fixedLoopCylinderOverlapMap_highPt]
    _ = _ := hright


public def fixedLoopCylinderSourceOverlapToPullback
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    TopCat.of ↥(vertexPiece
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
        edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) ⟶
      (Opens.toTopCat
        (TopCat.of (CircleMappingTorus (Homeomorph.refl (StdTorus 1))))).obj
        ((Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
            (coverVertexOpen (fun _ : Unit ↦ phi)) ⊓
          (Opens.map (fixedLoopCylinderTopCatMap phi c)).obj
            (coverEdgeOpen (fun _ : Unit ↦ phi))) :=
  TopCat.ofHom
    { toFun := fun z ↦ ⟨z, ⟨
        (fixedLoopCylinderMappingTorusMap_mem_vertexPiece_iff phi c z).2 z.2.1,
        (fixedLoopCylinderMappingTorusMap_mem_edgePiece_iff phi c z).2 z.2.2⟩⟩
      continuous_toFun := continuous_subtype_val.subtype_mk _ }


public theorem fixedLoopCylinderLegacyOverlap_comp_refinement
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
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
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ) :
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
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    fixedLoopCylinderSourceOverlapToPullback phi c ≫
        BinaryOpenCover.openIntersectionPreimageMap
        (fixedLoopCylinderTopCatMap phi c)
        (coverVertexOpen (fun _ : Unit ↦ phi))
        (coverEdgeOpen (fun _ : Unit ↦ phi)) =
      TopCat.ofHom (fixedLoopCylinderOverlapMap phi c) := by
  ext z
  rfl

public theorem fixedLoopCylinderSourceOverlapToPullback_homology
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ) :
    (BinaryOpenCover.integralHomologyFunctor n).map
          (fixedLoopCylinderSourceOverlapToPullback phi c) ≫
        BinaryOpenCover.openIntersectionPullbackHomologyMap
          (fixedLoopCylinderTopCatMap phi c)
          (coverVertexOpen (fun _ : Unit ↦ phi))
          (coverEdgeOpen (fun _ : Unit ↦ phi)) n =
      (BinaryOpenCover.integralHomologyFunctor n).map
        (TopCat.ofHom (fixedLoopCylinderOverlapMap phi c)) := by
  unfold BinaryOpenCover.openIntersectionPullbackHomologyMap
  rw [← Functor.map_comp,
    fixedLoopCylinderSourceOverlapToPullback_comp_preimage]
  rfl

public theorem fixedLoopCylinderSourceBoundary_toPullback
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ) :
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
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ) :
    IntegralSingularHomology n
        ↥(vertexPiece
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
          edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) →+
      IntegralSingularHomology n
        ↥(vertexPiece (fun _ : Unit ↦ phi) ∩
          edgePiece (fun _ : Unit ↦ phi)) :=
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
        (coverVertexOpen (fun _ : Unit ↦ phi))
        (coverEdgeOpen (fun _ : Unit ↦ phi)) n ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (coverVertexOpen (fun _ : Unit ↦ phi))
        (coverEdgeOpen (fun _ : Unit ↦ phi)) n).inv)

public noncomputable def fixedLoopCylinderLegacyUnionMap
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ) :
    IntegralSingularHomology n
        ↥(vertexPiece
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∪
          edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) →+
      IntegralSingularHomology n
        ↥(vertexPiece (fun _ : Unit ↦ phi) ∪
          edgePiece (fun _ : Unit ↦ phi)) :=
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
        (coverVertexOpen (fun _ : Unit ↦ phi))
        (coverEdgeOpen (fun _ : Unit ↦ phi))
        (coverOpen (fun _ : Unit ↦ phi)) n).inv)

public theorem fixedLoopCylinderLegacyUnionMap_unionEquiv_symm
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ)
    (z : IntegralSingularHomology n
      (CircleMappingTorus (Homeomorph.refl (StdTorus 1)))) :
    fixedLoopCylinderLegacyUnionMap phi c n
        ((unionEquiv
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) n).symm z) =
      (unionEquiv (fun _ : Unit ↦ phi) n).symm
        (integralSingularHomologyMap n
          (fixedLoopCylinderMappingTorusMap phi c) z) := by
  unfold fixedLoopCylinderLegacyUnionMap
  change ConcreteCategory.hom
      (BinaryOpenCover.opensUnionHomologyIso
        (coverVertexOpen (fun _ : Unit ↦ phi))
        (coverEdgeOpen (fun _ : Unit ↦ phi))
        (coverOpen (fun _ : Unit ↦ phi)) n).inv
      (ConcreteCategory.hom
        ((BinaryOpenCover.integralHomologyFunctor n).map
          (fixedLoopCylinderTopCatMap phi c))
        (ConcreteCategory.hom
          (BinaryOpenCover.opensUnionHomologyIso
            (coverVertexOpen
              (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
            (coverEdgeOpen
              (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
            (coverOpen
              (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) n).hom
          ((unionEquiv
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) n).symm z))) = _
  rw [opensUnionHomologyIso_hom_apply, AddEquiv.apply_symm_apply]
  exact opensUnionHomologyIso_inv_apply _ _ _

public theorem fixedLoopCylinderLegacyIntersectionMap_apply
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ)
    (x : IntegralSingularHomology n
      ↥(vertexPiece
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) ∩
        edgePiece (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))) :
    fixedLoopCylinderLegacyIntersectionMap phi c n x =
      integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c) x := by
  have hp := fixedLoopCylinderLegacyOverlap_homology_comp_refinement phi c n
  have hi := fixedLoopCylinderSourceOverlapToPullback_homology phi c n
  have hcat :
      (BinaryOpenCover.opensIntersectionHomologyIso
          (coverVertexOpen
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverEdgeOpen
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) n).hom ≫
        BinaryOpenCover.openIntersectionRefinementHomologyMap
          (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
          (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) n ≫
        BinaryOpenCover.openIntersectionPullbackHomologyMap
          (fixedLoopCylinderTopCatMap phi c)
          (coverVertexOpen (fun _ : Unit ↦ phi))
          (coverEdgeOpen (fun _ : Unit ↦ phi)) n =
      (BinaryOpenCover.integralHomologyFunctor n).map
        (TopCat.ofHom (fixedLoopCylinderOverlapMap phi c)) := by
    rw [← Category.assoc, hp]
    exact hi
  have hcat' := congrArg
    (fun q ↦ q ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (coverVertexOpen (fun _ : Unit ↦ phi))
        (coverEdgeOpen (fun _ : Unit ↦ phi)) n).inv)
    hcat
  simp only [Category.assoc] at hcat'
  have hfun := congrArg ConcreteCategory.hom hcat'
  have happ := DFunLike.congr_fun hfun x
  change fixedLoopCylinderLegacyIntersectionMap phi c n x =
    ConcreteCategory.hom
      (BinaryOpenCover.opensIntersectionHomologyIso
        (coverVertexOpen (fun _ : Unit ↦ phi))
        (coverEdgeOpen (fun _ : Unit ↦ phi)) n).inv
      (integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c) x) at happ
  exact happ.trans (opensIntersectionHomologyIso_inv_apply _ _ _ _)

public theorem fixedLoopCylinderLegacyIntersectionMap_overlapEquiv
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ)
    (x y : IntegralSingularHomology n (StdTorus 1)) :
    fixedLoopCylinderLegacyIntersectionMap phi c n
        (overlapEquiv
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) n
          ((fun _ : Unit ↦ x), fun _ : Unit ↦ y)) =
      overlapEquiv (fun _ : Unit ↦ phi) n
        ((fun _ : Unit ↦ integralSingularHomologyMap n c.1 x),
          fun _ : Unit ↦ integralSingularHomologyMap n c.1 y) := by
  rw [fixedLoopCylinderLegacyIntersectionMap_apply]
  change integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
      (overlapLegSum
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) n
        ((fun _ : Unit ↦ x), fun _ : Unit ↦ y)) =
    overlapLegSum (fun _ : Unit ↦ phi) n
      ((fun _ : Unit ↦ integralSingularHomologyMap n c.1 x),
        fun _ : Unit ↦ integralSingularHomologyMap n c.1 y)
  rw [overlapLegSum_apply, overlapLegSum_apply]
  simp only [Fintype.sum_unique]
  change integralSingularHomologyMap n (fixedLoopCylinderOverlapMap phi c)
      (integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uQuarter_mem_overlapBand ()) x +
        integralSingularHomologyMap n
          (overlapPt
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))
            uThreeQuarters_mem_overlapBand ()) y) =
    integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi)
          uQuarter_mem_overlapBand ())
        (integralSingularHomologyMap n c.1 x) +
      integralSingularHomologyMap n
        (overlapPt (fun _ : Unit ↦ phi)
          uThreeQuarters_mem_overlapBand ())
        (integralSingularHomologyMap n c.1 y)
  rw [map_add, fixedLoopCylinderOverlapMap_lowPt_homology,
    fixedLoopCylinderOverlapMap_highPt_homology]

/-- Naturality of the vertex/edge Mayer--Vietoris boundary for a pointwise-fixed loop,
transported to the set-subtype interface used by the mapping-torus Wang presentation. -/
public theorem fixedLoopCylinderLegacyBoundary_naturality
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) (n : ℕ) :
    (fixedLoopCylinderLegacyIntersectionMap phi c n).comp
        (coverBoundary
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) n) =
      (coverBoundary (fun _ : Unit ↦ phi) n).comp
        (fixedLoopCylinderLegacyUnionMap phi c (n + 1)) := by
  unfold fixedLoopCylinderLegacyIntersectionMap fixedLoopCylinderLegacyUnionMap coverBoundary
  apply AddMonoidHom.ext
  intro x
  have hn := fixedLoopCylinderBoundary_pullback_naturality phi c n
  rw [← fixedLoopCylinderSourceBoundary_toPullback phi c n] at hn
  have hcat :
      ((BinaryOpenCover.opensUnionHomologyIso
          (coverVertexOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverEdgeOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) (n + 1)).hom ≫
        (coverHomologyComparison
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))).boundary n ≫
        (BinaryOpenCover.opensIntersectionHomologyIso
          (coverVertexOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverEdgeOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) n).inv) ≫
          ((BinaryOpenCover.opensIntersectionHomologyIso
            (coverVertexOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
            (coverEdgeOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) n).hom ≫
          BinaryOpenCover.openIntersectionRefinementHomologyMap
            (le_of_eq (fixedLoopCylinderTopCatMap_vertexOpen phi c).symm)
            (le_of_eq (fixedLoopCylinderTopCatMap_edgeOpen phi c).symm) n ≫
          BinaryOpenCover.openIntersectionPullbackHomologyMap
            (fixedLoopCylinderTopCatMap phi c)
            (coverVertexOpen (fun _ : Unit ↦ phi))
            (coverEdgeOpen (fun _ : Unit ↦ phi)) n ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (coverVertexOpen (fun _ : Unit ↦ phi))
            (coverEdgeOpen (fun _ : Unit ↦ phi)) n).inv) =
        ((BinaryOpenCover.opensUnionHomologyIso
          (coverVertexOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverEdgeOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) (n + 1)).hom ≫
        (BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (fixedLoopCylinderTopCatMap phi c) ≫
        (BinaryOpenCover.opensUnionHomologyIso
          (coverVertexOpen (fun _ : Unit ↦ phi))
          (coverEdgeOpen (fun _ : Unit ↦ phi))
          (coverOpen (fun _ : Unit ↦ phi)) (n + 1)).inv) ≫
          ((BinaryOpenCover.opensUnionHomologyIso
            (coverVertexOpen (fun _ : Unit ↦ phi))
            (coverEdgeOpen (fun _ : Unit ↦ phi))
            (coverOpen (fun _ : Unit ↦ phi)) (n + 1)).hom ≫
          (coverHomologyComparison
            (fun _ : Unit ↦ phi)).boundary n ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (coverVertexOpen (fun _ : Unit ↦ phi))
            (coverEdgeOpen (fun _ : Unit ↦ phi)) n).inv) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using congrArg
      (fun q ↦
        (BinaryOpenCover.opensUnionHomologyIso
          (coverVertexOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverEdgeOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)))
          (coverOpen (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1))) (n + 1)).hom ≫
        q ≫
        (BinaryOpenCover.opensIntersectionHomologyIso
          (coverVertexOpen (fun _ : Unit ↦ phi))
          (coverEdgeOpen (fun _ : Unit ↦ phi)) n).inv)
      hn
  have hfun := congrArg ConcreteCategory.hom hcat
  exact DFunLike.congr_fun hfun x



/-- The Wang boundary of the torus swept out by a pointwise-fixed loop is the homology class of
that loop, with the sign fixed by the positive base-circle convention. -/
public theorem fixedLoopSweepClass_boundary
    {G : Type} [TopologicalSpace G]
    (phi : G ≃ₜ G) (c : FixedTopologicalCircle phi) :
    (circleMappingTorusWangPresentationOfCover phi 1).boundary
        (fixedLoopSweepClass phi c) =
      integralSingularHomologyMap 1 c.1 standardCircleHomologyGenerator := by
  let z := integralSingularHomologyMap 2
    (circleProductIdentityMappingTorusHomeomorph (X := StdTorus 1) :
      C(UnitAddCircle × StdTorus 1,
        CircleMappingTorus (Homeomorph.refl (StdTorus 1))))
    positiveCircleProductGenerator
  have hsourcePair := identityMappingTorusCoverBoundary_positiveCircleProductGenerator
  have hsource :
      coverBoundary
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1
          ((unionEquiv
            (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 2).symm z) =
        overlapEquiv
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1
          ((fun _ : Unit ↦ standardCircleHomologyGenerator),
            fun _ : Unit ↦ -standardCircleHomologyGenerator) := by
    apply (overlapEquiv
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1).symm.injective
    rw [AddEquiv.symm_apply_apply]
    exact hsourcePair
  have hnat := fixedLoopCylinderLegacyBoundary_naturality phi c 1
  have happ := DFunLike.congr_fun hnat
    ((unionEquiv
      (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 2).symm z)
  change fixedLoopCylinderLegacyIntersectionMap phi c 1
      (coverBoundary
        (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 1
        ((unionEquiv
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 2).symm z)) =
    coverBoundary (fun _ : Unit ↦ phi) 1
      (fixedLoopCylinderLegacyUnionMap phi c 2
        ((unionEquiv
          (fun _ : Unit ↦ Homeomorph.refl (StdTorus 1)) 2).symm z)) at happ
  rw [hsource, fixedLoopCylinderLegacyIntersectionMap_overlapEquiv,
    fixedLoopCylinderLegacyUnionMap_unionEquiv_symm] at happ
  rw [fixedLoopSweepClass_eq_cylinderMap]
  rw [circleMappingTorusWangPresentationOfCover_boundary_apply]
  change ((overlapEquiv (fun _ : Unit ↦ phi) 1).symm
      (coverBoundary (fun _ : Unit ↦ phi) 1
        ((unionEquiv (fun _ : Unit ↦ phi) 2).symm
          (integralSingularHomologyMap 2
            (fixedLoopCylinderMappingTorusMap phi c) z)))).1 () = _
  rw [← happ, AddEquiv.symm_apply_apply]

variable {G : Type} [TopologicalSpace G]

private def reflFixedLoop (c : C(StdTorus 1, G)) :
    FixedTopologicalCircle (Homeomorph.refl G) := by
  exact ⟨c, fun _ ↦ rfl⟩

private theorem fixedLoopMappingTorusMap_refl (c : C(StdTorus 1, G)) :
    fixedLoopMappingTorusMap (Homeomorph.refl G) (reflFixedLoop c) =
      (circleProductIdentityMappingTorusHomeomorph (X := G) :
        C(UnitAddCircle × G, CircleMappingTorus (Homeomorph.refl G))).comp
        (circleProductMap c) := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  change realMappingTorusHomeomorph (Homeomorph.refl G)
      (fixedLoopRealMappingTorusMap (Homeomorph.refl G) (reflFixedLoop c)
        (circleProductRealMappingTorusHomeomorph (((t : ℝ) : UnitAddCircle), x))) =
    realMappingTorusHomeomorph (Homeomorph.refl G)
      (circleProductRealMappingTorusHomeomorph (((t : ℝ) : UnitAddCircle), c x))
  rw [← show realToCircleProduct (t, x) = (((t : ℝ) : UnitAddCircle), x) by rfl,
    ← show realToCircleProduct (t, c x) =
      (((t : ℝ) : UnitAddCircle), c x) by rfl,
    circleProductRealMappingTorusHomeomorph_real,
    circleProductRealMappingTorusHomeomorph_real,
    fixedLoopRealMappingTorusMap_mk]
  rfl

/-- The positive-cross formula for the canonical product boundary, proved from the explicit
fixed-loop cover calculation rather than the finite-order sweep axiom. -/
public theorem canonicalProductWangBoundary_positiveCircleCross
    (c : C(StdTorus 1, G)) :
    canonicalProductWangBoundary 1 (positiveCircleCross c) =
      integralSingularHomologyMap 1 c standardCircleHomologyGenerator := by
  let phi : G ≃ₜ G := Homeomorph.refl G
  let d : FixedTopologicalCircle phi := reflFixedLoop c
  change (circleMappingTorusWangPresentationOfCover phi 1).boundary
      (integralSingularHomologyMap 2
        (circleProductIdentityMappingTorusHomeomorph (X := G) :
          C(UnitAddCircle × G, CircleMappingTorus (Homeomorph.refl G)))
        (positiveCircleCross c)) = _
  rw [positiveCircleCross, integralSingularHomologyMap_comp_wang,
    ← fixedLoopMappingTorusMap_refl c]
  exact fixedLoopSweepClass_boundary phi d

end SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary

end

end

@[expose] public section
noncomputable section
open AlgebraicTopology
namespace SphereSixComplex.Topology.FixedLoopSweepWangBoundary
open NormalizedFiniteOrderAdditiveCircleSweep
open CyclicMappingTorus.CircleSweep
open StandardTorusHomology

public theorem fixedLoopSweepClass_boundary
    {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    (phi : G ≃ₜ+ G) (c : fixedLoops phi) :
    (circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1).boundary
        (fixedLoopSweepClass phi c) =
      integralSingularHomologyMap 1 c.1 standardCircleHomologyGenerator := by
  let d : FixedTopologicalCircleWangBoundary.FixedTopologicalCircle phi.toHomeomorph :=
    ⟨c.1, fun x ↦ by
      change phi (c.1 x) = c.1 x
      have h := LinearMap.mem_ker.mp c.2
      have hx := DFunLike.congr_fun h x
      apply sub_eq_zero.mp
      simpa [loopAction] using hx⟩
  exact FixedTopologicalCircleWangBoundary.fixedLoopSweepClass_boundary phi.toHomeomorph d

end SphereSixComplex.Topology.FixedLoopSweepWangBoundary
end
end
