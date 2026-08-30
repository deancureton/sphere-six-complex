module

public import SphereSixComplex.Topology.BinaryOpenCoverAssembly
public import SphereSixComplex.Topology.FiniteCyclicMappingTorusWangNaturality

/-!
# Canonical mapping-torus boundary naturality

This module realizes the vertex/edge Mayer--Vietoris boundary through the canonical binary
open-cover comparison. Pulling the cover back along the normalized affine cyclic map then gives
the boundary naturality square directly, without choosing a witness of exactness.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

open NormalizedAffineMappingTorusCover
open CircleProductIdentityMappingTorus
open PaperAffineCyclicReducedFiberMappingTorus

variable {m : ℕ} [NeZero m] {F : Type} [TopologicalSpace F]

/-- The normalized affine cyclic map as a morphism of bundled topological spaces. -/
public def normalizedAffineCoverTopCatMap
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    TopCat.of (UnitAddCircle × F) ⟶ TopCat.of (CircleMappingTorus phi) :=
  TopCat.ofHom (normalizedAffineCoverToCircleMappingTorus phi hpow)

/-- The normalized affine cover preserves the marked fibre over the circle origin. -/
public theorem normalizedAffineCover_fiber
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (x : F) :
    normalizedAffineCoverToCircleMappingTorus phi hpow (0, x) =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) x := by
  change CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi
      (normalizedAffineCyclicQuotientRealMappingTorusHomeomorph phi hpow
        (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) (0, x))) = _
  have hreal :
      normalizedAffineCyclicQuotientRealMappingTorusHomeomorph phi hpow
          (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) (0, x)) =
        Quotient.mk (CyclicAngularFundamentalDomain.realMappingTorusSetoid phi)
          ((0 : ℝ), x) := by
    unfold normalizedAffineCyclicQuotientRealMappingTorusHomeomorph
    unfold CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
    dsimp only
    apply (normalizedAffineQuotientMap_eq_iff phi hpow _ _).mp
    calc
      normalizedAffineQuotientMap (m := m) phi
          (Function.surjInv (normalizedAffineQuotientMap_surjective (m := m) phi)
            (Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) (0, x))) =
        Quotient.mk (normalizedAffineCyclicSetoid (m := m) phi) (0, x) :=
          Function.surjInv_eq (normalizedAffineQuotientMap_surjective (m := m) phi) _
      _ = normalizedAffineQuotientMap (m := m) phi ((0 : ℝ), x) := by
        simp [normalizedAffineQuotientMap, normalizedAffineBaseCover]
  rw [hreal]
  rw [← show
    (CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi).symm
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) x) =
      Quotient.mk (CyclicAngularFundamentalDomain.realMappingTorusSetoid phi)
        ((0 : ℝ), x) by rfl]
  exact Homeomorph.apply_symm_apply _ _

/-- The normalized affine cover composed with the product fibre inclusion is the mapping-torus
fibre inclusion. -/
public theorem normalizedAffineCover_comp_productFiberInclusion
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    (normalizedAffineCoverToCircleMappingTorus phi hpow).comp
        (productFiberInclusion (X := F)) =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) := by
  ext x
  exact normalizedAffineCover_fiber phi hpow x

/-- The fibre square in finite cyclic Wang naturality follows by functoriality. -/
public theorem normalizedAffineCover_fiber_homology
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (n : ℕ)
    (x : IntegralSingularHomology n F) :
    integralSingularHomologyMap n
        (normalizedAffineCoverToCircleMappingTorus phi hpow)
        (integralSingularHomologyMap n (productFiberInclusion (X := F)) x) =
      integralSingularHomologyMap n
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) x := by
  rw [integralSingularHomologyMap_comp_wang,
    normalizedAffineCover_comp_productFiberInclusion phi hpow]

/-- The fibre square in the exact form used by a finite cyclic Wang presentation. -/
public theorem normalizedAffineCover_fiber_square
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (k : ℕ)
    (x : IntegralSingularHomology (k + 1) F) :
    integralSingularHomologyMap (k + 1)
        (normalizedAffineCoverToCircleMappingTorus phi hpow)
        (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := F)) x) =
      (circleMappingTorusWangPresentationOfCover phi k).inclusion x :=
  normalizedAffineCover_fiber_homology phi hpow (k + 1) x

/-- The vertex member of the standard mapping-torus cover as an open subset. -/
public abbrev mappingTorusVertexOpen (phi : F ≃ₜ F) :
    Opens (TopCat.of (CircleMappingTorus phi)) :=
  coverVertexOpen (fun _ : Unit ↦ phi)

/-- The edge member of the standard mapping-torus cover as an open subset. -/
public abbrev mappingTorusEdgeOpen (phi : F ≃ₜ F) :
    Opens (TopCat.of (CircleMappingTorus phi)) :=
  coverEdgeOpen (fun _ : Unit ↦ phi)

/-- The vertex and edge opens cover the mapping torus. -/
public theorem mappingTorusOpenCover (phi : F ≃ₜ F) :
    mappingTorusVertexOpen phi ⊔ mappingTorusEdgeOpen phi = ⊤ :=
  coverOpen (fun _ : Unit ↦ phi)

/-- The pullback of the vertex open under the normalized affine cyclic map. -/
public abbrev affinePullbackVertexOpen (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    Opens (TopCat.of (UnitAddCircle × F)) :=
  (Opens.map (normalizedAffineCoverTopCatMap phi hpow)).obj (mappingTorusVertexOpen phi)

/-- The pullback of the edge open under the normalized affine cyclic map. -/
public abbrev affinePullbackEdgeOpen (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    Opens (TopCat.of (UnitAddCircle × F)) :=
  (Opens.map (normalizedAffineCoverTopCatMap phi hpow)).obj (mappingTorusEdgeOpen phi)

/-- The two pulled-back opens cover the normalized affine source. -/
public theorem affinePullbackOpenCover (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    affinePullbackVertexOpen phi hpow ⊔ affinePullbackEdgeOpen phi hpow = ⊤ := by
  unfold affinePullbackVertexOpen affinePullbackEdgeOpen
  change (Opens.map (normalizedAffineCoverTopCatMap phi hpow)).obj
    (mappingTorusVertexOpen phi ⊔ mappingTorusEdgeOpen phi) = ⊤
  rw [mappingTorusOpenCover]
  rfl

/-- The canonical comparison for the pulled-back cover. -/
public noncomputable def affinePullbackOpenCoverHomologyComparison
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    BinaryOpenCover.OpenCoverHomologyComparison
      (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow) :=
  BinaryOpenCover.openCoverHomologyComparisonOfCover (affinePullbackOpenCover phi hpow)

/-- The canonical comparison for the mapping-torus vertex/edge cover. -/
public noncomputable def mappingTorusOpenCoverHomologyComparison (phi : F ≃ₜ F) :
    BinaryOpenCover.OpenCoverHomologyComparison
      (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) :=
  coverHomologyComparison (fun _ : Unit ↦ phi)

/-- The canonical connecting map for the pulled-back cover in the set-subtype interface. -/
public noncomputable def affinePullbackCanonicalCoverBoundary
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (n : ℕ) :
    IntegralSingularHomology (n + 1)
        ((affinePullbackVertexOpen phi hpow : Set (UnitAddCircle × F)) ∪
          (affinePullbackEdgeOpen phi hpow : Set (UnitAddCircle × F)) :
          Set (UnitAddCircle × F)) →+
      IntegralSingularHomology n
        ((affinePullbackVertexOpen phi hpow : Set (UnitAddCircle × F)) ∩
          (affinePullbackEdgeOpen phi hpow : Set (UnitAddCircle × F)) :
          Set (UnitAddCircle × F)) :=
  ((affinePullbackOpenCoverHomologyComparison phi hpow).toIntegralMayerVietorisData
    (affinePullbackOpenCover phi hpow)).legacyBoundary n

/-- The map between the legacy overlap terms induced by the normalized affine cover. -/
public noncomputable def affinePullbackLegacyIntersectionMap
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (n : ℕ) :
    IntegralSingularHomology n
        ((affinePullbackVertexOpen phi hpow : Set (UnitAddCircle × F)) ∩
          (affinePullbackEdgeOpen phi hpow : Set (UnitAddCircle × F)) :
          Set (UnitAddCircle × F)) →+
      IntegralSingularHomology n
        (vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi) :
          Set (CircleMappingTorus phi)) :=
  ConcreteCategory.hom
    ((BinaryOpenCover.opensIntersectionHomologyIso
        (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow) n).hom ≫
      BinaryOpenCover.openIntersectionPullbackHomologyMap
        (normalizedAffineCoverTopCatMap phi hpow)
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n ≫
      (BinaryOpenCover.opensIntersectionHomologyIso
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).inv)

/-- The map between the legacy union terms induced by the normalized affine cover. -/
public noncomputable def affinePullbackLegacyUnionMap
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (n : ℕ) :
    IntegralSingularHomology n
        ((affinePullbackVertexOpen phi hpow : Set (UnitAddCircle × F)) ∪
          (affinePullbackEdgeOpen phi hpow : Set (UnitAddCircle × F)) :
          Set (UnitAddCircle × F)) →+
      IntegralSingularHomology n
        (vertexPiece (fun _ : Unit ↦ phi) ∪ edgePiece (fun _ : Unit ↦ phi) :
          Set (CircleMappingTorus phi)) :=
  ConcreteCategory.hom
    ((BinaryOpenCover.opensUnionHomologyIso
        (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow)
        (affinePullbackOpenCover phi hpow) n).hom ≫
      (BinaryOpenCover.integralHomologyFunctor n).map
        (normalizedAffineCoverTopCatMap phi hpow) ≫
      (BinaryOpenCover.opensUnionHomologyIso
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
        (mappingTorusOpenCover phi) n).inv)

/-- The canonical vertex/edge connecting map in the legacy set-subtype interface. -/
public noncomputable def mappingTorusCanonicalCoverBoundary (phi : F ≃ₜ F) (n : ℕ) :
    IntegralSingularHomology (n + 1)
        (vertexPiece (fun _ : Unit ↦ phi) ∪ edgePiece (fun _ : Unit ↦ phi) :
          Set (CircleMappingTorus phi)) →+
      IntegralSingularHomology n
        (vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi) :
          Set (CircleMappingTorus phi)) :=
  coverBoundary (fun _ : Unit ↦ phi) n

/-- The canonical legacy boundary has the three required Mayer--Vietoris exactness properties. -/
public theorem mappingTorusCanonicalCoverBoundary_spec (phi : F ≃ₜ F) (n : ℕ) :
    Function.Exact
        (IntegralMayerVietoris.sumMap
          (vertexPiece (fun _ : Unit ↦ phi)) (edgePiece (fun _ : Unit ↦ phi)) (n + 1))
        (mappingTorusCanonicalCoverBoundary phi n) ∧
      Function.Exact (mappingTorusCanonicalCoverBoundary phi n)
        (IntegralMayerVietoris.differenceMap
          (vertexPiece (fun _ : Unit ↦ phi)) (edgePiece (fun _ : Unit ↦ phi)) n) ∧
      Function.Exact
        (IntegralMayerVietoris.differenceMap
          (vertexPiece (fun _ : Unit ↦ phi)) (edgePiece (fun _ : Unit ↦ phi)) n)
        (IntegralMayerVietoris.sumMap
          (vertexPiece (fun _ : Unit ↦ phi)) (edgePiece (fun _ : Unit ↦ phi)) n) :=
  coverBoundary_spec (fun _ : Unit ↦ phi) n

/-- Naturality of the canonical boundary under the normalized affine cyclic map. -/
public theorem normalizedAffineCover_boundary_naturality
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (n : ℕ) :
    (affinePullbackOpenCoverHomologyComparison phi hpow).boundary n ≫
        BinaryOpenCover.openIntersectionPullbackHomologyMap
          (normalizedAffineCoverTopCatMap phi hpow)
          (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n =
      (BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (normalizedAffineCoverTopCatMap phi hpow) ≫
        (mappingTorusOpenCoverHomologyComparison phi).boundary n := by
  apply BinaryOpenCover.OpenCoverHomologyComparison.boundary_pullback_naturality
  exact BinaryOpenCover.openCoverHomologyComparisonOfCover_pullbackNaturality
    (normalizedAffineCoverTopCatMap phi hpow)
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
    (affinePullbackOpenCover phi hpow) (mappingTorusOpenCover phi)

/-- Pullback naturality transported to the exact set-subtype boundary used by the Wang
presentation. -/
public theorem normalizedAffineCover_legacyBoundary_naturality
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (n : ℕ) :
    (affinePullbackLegacyIntersectionMap phi hpow n).comp
        (affinePullbackCanonicalCoverBoundary phi hpow n) =
      (mappingTorusCanonicalCoverBoundary phi n).comp
        (affinePullbackLegacyUnionMap phi hpow (n + 1)) := by
  unfold affinePullbackLegacyIntersectionMap affinePullbackCanonicalCoverBoundary
    mappingTorusCanonicalCoverBoundary affinePullbackLegacyUnionMap coverBoundary
  apply AddMonoidHom.ext
  intro x
  have hn := normalizedAffineCover_boundary_naturality phi hpow n
  have hcat :
      ((BinaryOpenCover.opensUnionHomologyIso
          (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow)
          (affinePullbackOpenCover phi hpow) (n + 1)).hom ≫
        (affinePullbackOpenCoverHomologyComparison phi hpow).boundary n ≫
        (BinaryOpenCover.opensIntersectionHomologyIso
          (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow) n).inv) ≫
          ((BinaryOpenCover.opensIntersectionHomologyIso
            (affinePullbackVertexOpen phi hpow)
            (affinePullbackEdgeOpen phi hpow) n).hom ≫
          BinaryOpenCover.openIntersectionPullbackHomologyMap
            (normalizedAffineCoverTopCatMap phi hpow)
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).inv) =
        ((BinaryOpenCover.opensUnionHomologyIso
          (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow)
          (affinePullbackOpenCover phi hpow) (n + 1)).hom ≫
        (BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (normalizedAffineCoverTopCatMap phi hpow) ≫
        (BinaryOpenCover.opensUnionHomologyIso
          (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
          (mappingTorusOpenCover phi) (n + 1)).inv) ≫
          ((BinaryOpenCover.opensUnionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
            (mappingTorusOpenCover phi) (n + 1)).hom ≫
          (mappingTorusOpenCoverHomologyComparison phi).boundary n ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).inv) := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using congrArg
      (fun q ↦
        (BinaryOpenCover.opensUnionHomologyIso
          (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow)
          (affinePullbackOpenCover phi hpow) (n + 1)).hom ≫
        q ≫
        (BinaryOpenCover.opensIntersectionHomologyIso
          (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).inv)
      hn
  have hfun := congrArg ConcreteCategory.hom hcat
  change ConcreteCategory.hom
      (((BinaryOpenCover.opensUnionHomologyIso
          (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow)
          (affinePullbackOpenCover phi hpow) (n + 1)).hom ≫
        (affinePullbackOpenCoverHomologyComparison phi hpow).boundary n ≫
        (BinaryOpenCover.opensIntersectionHomologyIso
          (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow) n).inv) ≫
          ((BinaryOpenCover.opensIntersectionHomologyIso
            (affinePullbackVertexOpen phi hpow)
            (affinePullbackEdgeOpen phi hpow) n).hom ≫
          BinaryOpenCover.openIntersectionPullbackHomologyMap
            (normalizedAffineCoverTopCatMap phi hpow)
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).inv)) x =
    ConcreteCategory.hom
      (((BinaryOpenCover.opensUnionHomologyIso
          (affinePullbackVertexOpen phi hpow) (affinePullbackEdgeOpen phi hpow)
          (affinePullbackOpenCover phi hpow) (n + 1)).hom ≫
        (BinaryOpenCover.integralHomologyFunctor (n + 1)).map
          (normalizedAffineCoverTopCatMap phi hpow) ≫
        (BinaryOpenCover.opensUnionHomologyIso
          (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
          (mappingTorusOpenCover phi) (n + 1)).inv) ≫
          ((BinaryOpenCover.opensUnionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
            (mappingTorusOpenCover phi) (n + 1)).hom ≫
          (mappingTorusOpenCoverHomologyComparison phi).boundary n ≫
          (BinaryOpenCover.opensIntersectionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).inv)) x
  exact DFunLike.congr_fun hfun x

end SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

end

end
