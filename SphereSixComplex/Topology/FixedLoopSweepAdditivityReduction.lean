module

public import SphereSixComplex.Topology.FixedLoopSweepWangBoundary

/-!
# Additivity of fixed-loop sweeps modulo fibre classes

The explicit fixed-loop sweep has the expected additive Wang boundary.  Consequently, its
possible additive defect in total-space homology is supported in the fibre.  This isolates the
remaining geometric input in the normalized finite-cover sweep theorem: an actual additivity
proof must show that this fibre correction vanishes.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex.Topology.FixedLoopSweepAdditivityReduction

open CircleProductIdentityMappingTorus
open CyclicAngularFundamentalDomain
open NormalizedFiniteOrderAdditiveCircleSweep
open NormalizedFiniteOrderAdditiveCircleSweepProof
open FixedLoopSweepWangBoundary
open CanonicalProductWangBoundaryNaturality
open NormalizedAffineMappingTorusCover
open PaperAffineCyclicReducedFiberMappingTorus
open PositiveCircleCross
open StandardTorusHomology

variable {G : Type} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [PathConnectedSpace G]

public abbrev FixedLoopPresentation (phi : G ≃ₜ+ G) :=
  circleMappingTorusWangPresentationOfCover phi.toHomeomorph 1

private def unitAddCircleProductProjection :
    C(UnitAddCircle × StdTorus 1, UnitAddCircle) where
  toFun := Prod.fst
  continuous_toFun := continuous_fst

private def unitAddCircleZeroSection :
    C(UnitAddCircle, UnitAddCircle × StdTorus 1) where
  toFun s := (s, 0)
  continuous_toFun := continuous_id.prodMk continuous_const

private noncomputable def fixedLoopZeroBaseMap (phi : G ≃ₜ+ G) :
    C(UnitAddCircle, CircleMappingTorus phi.toHomeomorph) :=
  (fixedLoopMappingTorusMap phi 0).comp unitAddCircleZeroSection

omit [PathConnectedSpace G] in
private theorem fixedLoopMappingTorusMap_zero_factor (phi : G ≃ₜ+ G) :
    (fixedLoopZeroBaseMap phi).comp unitAddCircleProductProjection =
      fixedLoopMappingTorusMap phi 0 := by
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective
    (s := AddSubgroup.zmultiples (1 : ℝ)) s
  change fixedLoopMappingTorusMap phi 0 ((t : UnitAddCircle), 0) =
    fixedLoopMappingTorusMap phi 0 ((t : UnitAddCircle), x)
  unfold fixedLoopMappingTorusMap
  change realMappingTorusHomeomorph phi.toHomeomorph
      (fixedLoopRealMappingTorusMap phi 0
        (circleProductRealMappingTorusHomeomorph (realToCircleProduct (t, 0)))) =
    realMappingTorusHomeomorph phi.toHomeomorph
      (fixedLoopRealMappingTorusMap phi 0
        (circleProductRealMappingTorusHomeomorph (realToCircleProduct (t, x))))
  rw [circleProductRealMappingTorusHomeomorph_real,
    circleProductRealMappingTorusHomeomorph_real]
  rfl

private theorem subsingleton_homologyTwo_standardCircle :
    Subsingleton (IntegralSingularHomology 2 (StdTorus 1)) := by
  constructor
  intro x y
  apply (stdTorusHomologyTwo 1).injective
  funext i
  exact Fin.elim0 i

private theorem subsingleton_homologyTwo_unitAddCircle :
    Subsingleton (IntegralSingularHomology 2 UnitAddCircle) := by
  constructor
  intro x y
  apply (integralSingularHomologyEquiv 2
    StandardCircleHomologyLiftDegree.stdTorusOneHomeomorph).symm.injective
  let _ := subsingleton_homologyTwo_standardCircle
  exact Subsingleton.elim _ _

omit [PathConnectedSpace G] in
/-- The explicit geometric sweep of the zero loop vanishes. -/
public theorem fixedLoopSweepClass_zero (phi : G ≃ₜ+ G) :
    fixedLoopSweepClass phi 0 = 0 := by
  unfold fixedLoopSweepClass
  rw [← fixedLoopMappingTorusMap_zero_factor]
  let _ := subsingleton_homologyTwo_unitAddCircle
  have hzero : integralSingularHomologyMap 2 unitAddCircleProductProjection
      positiveCircleProductGenerator = 0 := Subsingleton.elim _ _
  calc
    integralSingularHomologyMap 2
        ((fixedLoopZeroBaseMap phi).comp unitAddCircleProductProjection)
        positiveCircleProductGenerator =
      integralSingularHomologyMap 2 (fixedLoopZeroBaseMap phi)
        (integralSingularHomologyMap 2 unitAddCircleProductProjection
          positiveCircleProductGenerator) :=
      (integralSingularHomologyMap_comp_wang _ _ _ _).symm
    _ = 0 := by rw [hzero, map_zero]

/-- The Wang boundary of the explicit sweep is additive in the pointwise-fixed loop. -/
public theorem fixedLoopSweepClass_boundary_add (phi : G ≃ₜ+ G)
    (c d : FixedLoop phi) :
    (FixedLoopPresentation phi).boundary (fixedLoopSweepClass phi (c + d)) =
      (FixedLoopPresentation phi).boundary (fixedLoopSweepClass phi c) +
        (FixedLoopPresentation phi).boundary (fixedLoopSweepClass phi d) := by
  rw [fixedLoopSweepClass_boundary, fixedLoopSweepClass_boundary,
    fixedLoopSweepClass_boundary]
  exact standardCircleHomologyClass_map_add c.1 d.1

omit [PathConnectedSpace G] in
/-- The Wang boundary of the explicit sweep of the zero loop vanishes. -/
public theorem fixedLoopSweepClass_boundary_zero (phi : G ≃ₜ+ G) :
    (FixedLoopPresentation phi).boundary (fixedLoopSweepClass phi 0) = 0 := by
  rw [fixedLoopSweepClass_boundary]
  exact standardCircleHomologyClass_map_zero

/-- The additive defect of the explicit fixed-loop sweep lies in the image of the fibre
inclusion.  This is the strongest conclusion supplied by Wang exactness alone. -/
public theorem fixedLoopSweepClass_add_defect_mem_fibre (phi : G ≃ₜ+ G)
    (c d : FixedLoop phi) :
    fixedLoopSweepClass phi (c + d) - fixedLoopSweepClass phi c -
        fixedLoopSweepClass phi d ∈
      Set.range (FixedLoopPresentation phi).inclusion := by
  apply ((FixedLoopPresentation phi).exact_inclusion_boundary _).mp
  rw [map_sub, map_sub, fixedLoopSweepClass_boundary_add]
  abel

/-- Equivalently, the sweep of a sum is the sum of the sweeps up to one fibre class. -/
public theorem fixedLoopSweepClass_add_eq_add_add_fibre (phi : G ≃ₜ+ G)
    (c d : FixedLoop phi) :
    ∃ x : IntegralSingularHomology 2 G,
      fixedLoopSweepClass phi (c + d) =
        fixedLoopSweepClass phi c + fixedLoopSweepClass phi d +
          (FixedLoopPresentation phi).inclusion x := by
  obtain ⟨x, hx⟩ := fixedLoopSweepClass_add_defect_mem_fibre phi c d
  refine ⟨x, ?_⟩
  rw [hx]
  abel

/-- If the fibre has no degree-two homology, the explicit fixed-loop sweep is additive already
in total-space homology. -/
public theorem fixedLoopSweepClass_add_of_subsingleton_homologyTwo
    [Subsingleton (IntegralSingularHomology 2 G)] (phi : G ≃ₜ+ G)
    (c d : FixedLoop phi) :
    fixedLoopSweepClass phi (c + d) =
      fixedLoopSweepClass phi c + fixedLoopSweepClass phi d := by
  obtain ⟨x, hx⟩ := fixedLoopSweepClass_add_eq_add_add_fibre phi c d
  have hx0 : x = 0 := Subsingleton.elim _ _
  rw [hx0, map_zero, add_zero] at hx
  exact hx

/-- In the absence of degree-two fibre homology, the explicit geometric construction is an
additive homomorphism without passing to a quotient. -/
public noncomputable def fixedLoopSweepClassHomOfSubsingletonHomologyTwo
    [Subsingleton (IntegralSingularHomology 2 G)] (phi : G ≃ₜ+ G) :
    FixedLoop phi →+ IntegralSingularHomology 2
      (CircleMappingTorus phi.toHomeomorph) where
  toFun := fixedLoopSweepClass phi
  map_zero' := fixedLoopSweepClass_zero phi
  map_add' := fixedLoopSweepClass_add_of_subsingleton_homologyTwo phi

omit [PathConnectedSpace G] in
/-- The explicit sweep of the zero loop is itself a fibre-supported class. -/
public theorem fixedLoopSweepClass_zero_mem_fibre (phi : G ≃ₜ+ G) :
    fixedLoopSweepClass phi 0 ∈ Set.range (FixedLoopPresentation phi).inclusion := by
  apply ((FixedLoopPresentation phi).exact_inclusion_boundary _).mp
  exact fixedLoopSweepClass_boundary_zero phi

omit [PathConnectedSpace G] in
/-- Any degree-two class with the prescribed fixed-loop Wang boundary differs from the explicit
sweep by a fibre-supported class. -/
public theorem eq_fixedLoopSweepClass_add_fibre_of_boundary (phi : G ≃ₜ+ G)
    (c : FixedLoop phi)
    (z : IntegralSingularHomology 2 (CircleMappingTorus phi.toHomeomorph))
    (hz : (FixedLoopPresentation phi).boundary z =
      integralSingularHomologyMap 1 c.1 standardCircleHomologyGenerator) :
    ∃ x : IntegralSingularHomology 2 G,
      z = fixedLoopSweepClass phi c + (FixedLoopPresentation phi).inclusion x := by
  have hmem : z - fixedLoopSweepClass phi c ∈
      Set.range (FixedLoopPresentation phi).inclusion := by
    apply ((FixedLoopPresentation phi).exact_inclusion_boundary _).mp
    rw [map_sub, fixedLoopSweepClass_boundary, hz, sub_self]
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  rw [hx]
  abel

/-- The explicit sweep of the cyclic orbit norm has exactly the expected norm as its Wang
boundary. -/
public theorem fixedLoopSweepClass_orbitNorm_boundary
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G)) :
    (FixedLoopPresentation phi).boundary
        (fixedLoopSweepClass phi (orbitNorm m phi hpow c)) =
      ∑ i ∈ Finset.range m,
        integralSingularHomologyMap 1
          ((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G))
          (integralSingularHomologyMap 1 c standardCircleHomologyGenerator) := by
  rw [fixedLoopSweepClass_boundary, standardCircleHomologyClass_orbitNorm]

/-- If the normalized-cover cross has the expected Wang boundary, then it agrees with the
explicit orbit-norm sweep up to a fibre-supported class. -/
public theorem normalizedCover_cross_eq_fixedLoopSweepClass_add_fibre_of_boundary
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G))
    (hboundary :
      (FixedLoopPresentation phi).boundary
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross c)) =
        ∑ i ∈ Finset.range m,
          integralSingularHomologyMap 1
            ((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G))
            (integralSingularHomologyMap 1 c standardCircleHomologyGenerator)) :
    ∃ x : IntegralSingularHomology 2 G,
      integralSingularHomologyMap 2
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
          (positiveCircleCross c) =
        fixedLoopSweepClass phi (orbitNorm m phi hpow c) +
          (FixedLoopPresentation phi).inclusion x := by
  apply eq_fixedLoopSweepClass_add_fibre_of_boundary
  rw [standardCircleHomologyClass_orbitNorm]
  exact hboundary

/-- Fibre-supported degree-two classes in the mapping torus. -/
public abbrev FixedLoopFibreRange (phi : G ≃ₜ+ G) :=
  LinearMap.range (FixedLoopPresentation phi).inclusion.toIntLinearMap

/-- Degree-two mapping-torus homology modulo classes supported in the fibre. -/
public abbrev FixedLoopSweepModuloFibre (phi : G ≃ₜ+ G) :=
  IntegralSingularHomology 2 (CircleMappingTorus phi.toHomeomorph) ⧸
    FixedLoopFibreRange phi

/-- The explicit fixed-loop sweep is genuinely additive after quotienting out fibre-supported
classes. -/
public noncomputable def fixedLoopSweepClassModuloFibre (phi : G ≃ₜ+ G) :
    FixedLoop phi →+ FixedLoopSweepModuloFibre phi where
  toFun c := Submodule.Quotient.mk (fixedLoopSweepClass phi c)
  map_zero' := by
    apply (Submodule.Quotient.eq (FixedLoopFibreRange phi)).2
    rw [sub_zero]
    obtain ⟨x, hx⟩ := fixedLoopSweepClass_zero_mem_fibre phi
    exact ⟨x, hx⟩
  map_add' c d := by
    apply (Submodule.Quotient.eq (FixedLoopFibreRange phi)).2
    change fixedLoopSweepClass phi (c + d) -
        (fixedLoopSweepClass phi c + fixedLoopSweepClass phi d) ∈
      FixedLoopFibreRange phi
    obtain ⟨x, hx⟩ := fixedLoopSweepClass_add_defect_mem_fibre phi c d
    refine ⟨x, ?_⟩
    change (FixedLoopPresentation phi).inclusion x = _
    rw [hx]
    abel

@[simp]
public theorem fixedLoopSweepClassModuloFibre_apply (phi : G ≃ₜ+ G)
    (c : FixedLoop phi) :
    fixedLoopSweepClassModuloFibre phi c =
      Submodule.Quotient.mk (fixedLoopSweepClass phi c) :=
  rfl

/-- In the quotient by fibre-supported classes, the Wang boundary uniquely determines the
explicit fixed-loop sweep class. -/
public theorem quotient_mk_eq_fixedLoopSweepClass_of_boundary (phi : G ≃ₜ+ G)
    (c : FixedLoop phi)
    (z : IntegralSingularHomology 2 (CircleMappingTorus phi.toHomeomorph))
    (hz : (FixedLoopPresentation phi).boundary z =
      integralSingularHomologyMap 1 c.1 standardCircleHomologyGenerator) :
    (Submodule.Quotient.mk z : FixedLoopSweepModuloFibre phi) =
      fixedLoopSweepClassModuloFibre phi c := by
  rw [fixedLoopSweepClassModuloFibre_apply]
  apply (Submodule.Quotient.eq (FixedLoopFibreRange phi)).2
  have hmem : z - fixedLoopSweepClass phi c ∈
      Set.range (FixedLoopPresentation phi).inclusion := by
    apply ((FixedLoopPresentation phi).exact_inclusion_boundary _).mp
    rw [map_sub, fixedLoopSweepClass_boundary, hz, sub_self]
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, hx⟩

/-! ## Reduction of the normalized-cover boundary to one overlap calculation -/

omit [AddCommGroup G] [IsTopologicalAddGroup G] [PathConnectedSpace G] in
private theorem mappingTorusOpensUnionHomologyIso_hom_apply
    (phi : G ≃ₜ G) (n : ℕ)
    (x : IntegralSingularHomology n
      (vertexPiece (fun _ : Unit ↦ phi) ∪ edgePiece (fun _ : Unit ↦ phi) :
        Set (CircleMappingTorus phi))) :
    ConcreteCategory.hom
        (BinaryOpenCover.opensUnionHomologyIso
          (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
          (mappingTorusOpenCover phi) n).hom x =
      unionEquiv (fun _ : Unit ↦ phi) n x := by
  have htop :
      (TopCat.isoOfHomeo (BinaryOpenCover.opensUnionHomeomorph
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
        (mappingTorusOpenCover phi))).hom =
        TopCat.ofHom (coverUnionCM (fun _ : Unit ↦ phi)) := by
    ext y
    rfl
  have hmap := congrArg (BinaryOpenCover.integralHomologyFunctor n).map htop
  have hfun := congrArg ConcreteCategory.hom hmap
  exact DFunLike.congr_fun hfun x

omit [AddCommGroup G] [IsTopologicalAddGroup G] [PathConnectedSpace G] in
private theorem mappingTorusOpensUnionHomologyIso_inv_apply
    (phi : G ≃ₜ G) (n : ℕ)
    (z : IntegralSingularHomology n (CircleMappingTorus phi)) :
    ConcreteCategory.hom
        (BinaryOpenCover.opensUnionHomologyIso
          (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
          (mappingTorusOpenCover phi) n).inv z =
      (unionEquiv (fun _ : Unit ↦ phi) n).symm z := by
  apply (unionEquiv (fun _ : Unit ↦ phi) n).injective
  calc
    _ = ConcreteCategory.hom
        (BinaryOpenCover.opensUnionHomologyIso
          (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
          (mappingTorusOpenCover phi) n).hom
        (ConcreteCategory.hom
          (BinaryOpenCover.opensUnionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
            (mappingTorusOpenCover phi) n).inv z) := by
      symm
      exact (mappingTorusOpensUnionHomologyIso_hom_apply phi n _).symm
    _ = z := by simp
    _ = unionEquiv (fun _ : Unit ↦ phi) n
        ((unionEquiv (fun _ : Unit ↦ phi) n).symm z) :=
      (AddEquiv.apply_symm_apply _ _).symm

/-- The lift of a source class to the union term of the pulled-back binary cover. -/
public noncomputable def affinePullbackUnionLift
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (n : ℕ)
    (z : IntegralSingularHomology n (UnitAddCircle × G)) :
    IntegralSingularHomology n
      ((affinePullbackVertexOpen phi.toHomeomorph hpow : Set (UnitAddCircle × G)) ∪
        (affinePullbackEdgeOpen phi.toHomeomorph hpow : Set (UnitAddCircle × G)) :
        Set (UnitAddCircle × G)) :=
  ConcreteCategory.hom
    (BinaryOpenCover.opensUnionHomologyIso
      (affinePullbackVertexOpen phi.toHomeomorph hpow)
      (affinePullbackEdgeOpen phi.toHomeomorph hpow)
      (affinePullbackOpenCover phi.toHomeomorph hpow) n).inv z

omit [IsTopologicalAddGroup G] [PathConnectedSpace G] in
/-- Under normalized-cover naturality, the canonical source-union lift maps to the canonical
target-union lift of the ordinary homology pushforward. -/
public theorem affinePullbackLegacyUnionMap_unionLift
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (n : ℕ)
    (z : IntegralSingularHomology n (UnitAddCircle × G)) :
    affinePullbackLegacyUnionMap phi.toHomeomorph hpow n
        (affinePullbackUnionLift m phi hpow n z) =
      (unionEquiv (fun _ : Unit ↦ phi.toHomeomorph) n).symm
        (integralSingularHomologyMap n
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow) z) := by
  unfold affinePullbackLegacyUnionMap affinePullbackUnionLift
  change ConcreteCategory.hom
      (BinaryOpenCover.opensUnionHomologyIso
        (mappingTorusVertexOpen phi.toHomeomorph)
        (mappingTorusEdgeOpen phi.toHomeomorph)
        (mappingTorusOpenCover phi.toHomeomorph) n).inv
      (ConcreteCategory.hom
        ((BinaryOpenCover.integralHomologyFunctor n).map
          (normalizedAffineCoverTopCatMap phi.toHomeomorph hpow))
        (ConcreteCategory.hom
          (BinaryOpenCover.opensUnionHomologyIso
            (affinePullbackVertexOpen phi.toHomeomorph hpow)
            (affinePullbackEdgeOpen phi.toHomeomorph hpow)
            (affinePullbackOpenCover phi.toHomeomorph hpow) n).hom
          (ConcreteCategory.hom
            (BinaryOpenCover.opensUnionHomologyIso
              (affinePullbackVertexOpen phi.toHomeomorph hpow)
              (affinePullbackEdgeOpen phi.toHomeomorph hpow)
              (affinePullbackOpenCover phi.toHomeomorph hpow) n).inv z))) = _
  have hcancel :
      ConcreteCategory.hom
          (BinaryOpenCover.opensUnionHomologyIso
            (affinePullbackVertexOpen phi.toHomeomorph hpow)
            (affinePullbackEdgeOpen phi.toHomeomorph hpow)
            (affinePullbackOpenCover phi.toHomeomorph hpow) n).hom
        (ConcreteCategory.hom
          (BinaryOpenCover.opensUnionHomologyIso
            (affinePullbackVertexOpen phi.toHomeomorph hpow)
            (affinePullbackEdgeOpen phi.toHomeomorph hpow)
            (affinePullbackOpenCover phi.toHomeomorph hpow) n).inv z) = z := by
    rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  rw [hcancel]
  exact mappingTorusOpensUnionHomologyIso_inv_apply _ _ _

/-- The cyclic norm in fibre homology which is expected as the normalized-cover Wang
boundary. -/
public noncomputable def normalizedCoverOrbitBoundary
    (m : ℕ) (phi : G ≃ₜ+ G) (c : C(StdTorus 1, G)) :
    IntegralSingularHomology 1 G :=
  ∑ i ∈ Finset.range m,
    integralSingularHomologyMap 1
      ((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G))
      (integralSingularHomologyMap 1 c standardCircleHomologyGenerator)

/-- A signed source-cover calculation for the normalized positive cross.  The low overlap
collar carries the positive cyclic norm and the high collar its negative. -/
public def NormalizedCoverCrossSignedOverlapCalculation
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G)) : Prop :=
  affinePullbackLegacyIntersectionMap phi.toHomeomorph hpow 1
      (affinePullbackCanonicalCoverBoundary phi.toHomeomorph hpow 1
        (affinePullbackUnionLift m phi hpow 2 (positiveCircleCross c))) =
    overlapEquiv (fun _ : Unit ↦ phi.toHomeomorph) 1
      ((fun _ : Unit ↦ normalizedCoverOrbitBoundary m phi c),
        fun _ : Unit ↦ -normalizedCoverOrbitBoundary m phi c)

/-- The minimal source-cover calculation needed for the normalized-cover Wang boundary: after
mapping the pullback Mayer--Vietoris boundary into the target overlap, its low-collar coordinate
is the positive cyclic norm. -/
public def NormalizedCoverCrossLowOverlapCalculation
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G)) : Prop :=
  ((overlapEquiv (fun _ : Unit ↦ phi.toHomeomorph) 1).symm
    (affinePullbackLegacyIntersectionMap phi.toHomeomorph hpow 1
      (affinePullbackCanonicalCoverBoundary phi.toHomeomorph hpow 1
        (affinePullbackUnionLift m phi hpow 2 (positiveCircleCross c))))).1 () =
    normalizedCoverOrbitBoundary m phi c

omit [IsTopologicalAddGroup G] [PathConnectedSpace G] in
/-- The full signed overlap formula implies the minimal low-collar calculation. -/
public theorem normalizedCoverCrossLowOverlapCalculation_of_signed
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G))
    (hcalc : NormalizedCoverCrossSignedOverlapCalculation m phi hpow c) :
    NormalizedCoverCrossLowOverlapCalculation m phi hpow c := by
  unfold NormalizedCoverCrossLowOverlapCalculation
  rw [hcalc, AddEquiv.symm_apply_apply]

omit [IsTopologicalAddGroup G] [PathConnectedSpace G] in
/-- Mayer--Vietoris naturality turns the concrete signed overlap calculation into the desired
Wang boundary formula for the normalized-cover positive cross. -/
public theorem normalizedAffineCover_positiveCircleCross_boundary_of_overlapCalculation
    (m : ℕ) [NeZero m] (phi : G ≃ₜ+ G)
    (hpow : phi.toHomeomorph ^ m = 1) (c : C(StdTorus 1, G))
    (hcalc : NormalizedCoverCrossLowOverlapCalculation m phi hpow c) :
    (FixedLoopPresentation phi).boundary
        (integralSingularHomologyMap 2
          (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
          (positiveCircleCross c)) =
      ∑ i ∈ Finset.range m,
        integralSingularHomologyMap 1
          ((phi.toHomeomorph ^ i : G ≃ₜ G) : C(G, G))
          (integralSingularHomologyMap 1 c standardCircleHomologyGenerator) := by
  have hnat := normalizedAffineCover_legacyBoundary_naturality
    phi.toHomeomorph hpow 1
  have happ := DFunLike.congr_fun hnat
    (affinePullbackUnionLift m phi hpow 2 (positiveCircleCross c))
  change affinePullbackLegacyIntersectionMap phi.toHomeomorph hpow 1
      (affinePullbackCanonicalCoverBoundary phi.toHomeomorph hpow 1
        (affinePullbackUnionLift m phi hpow 2 (positiveCircleCross c))) =
    coverBoundary (fun _ : Unit ↦ phi.toHomeomorph) 1
      (affinePullbackLegacyUnionMap phi.toHomeomorph hpow 2
        (affinePullbackUnionLift m phi hpow 2 (positiveCircleCross c))) at happ
  rw [affinePullbackLegacyUnionMap_unionLift] at happ
  rw [circleMappingTorusWangPresentationOfCover_boundary_apply]
  change ((overlapEquiv (fun _ : Unit ↦ phi.toHomeomorph) 1).symm
      (coverBoundary (fun _ : Unit ↦ phi.toHomeomorph) 1
        ((unionEquiv (fun _ : Unit ↦ phi.toHomeomorph) 2).symm
          (integralSingularHomologyMap 2
            (normalizedAffineCoverToCircleMappingTorus phi.toHomeomorph hpow)
            (positiveCircleCross c))))).1 () = _
  rw [← happ]
  exact hcalc

end SphereSixComplex.Topology.FixedLoopSweepAdditivityReduction

end

end
