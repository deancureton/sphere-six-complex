module

public import SphereSixComplex.Topology.BinaryOpenCoverMapNaturality
public import SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

/-!
# Degree-one comparison of Mayer--Vietoris and Wang boundaries

The connecting morphism of a pullback binary open cover is natural for every continuous map.
If the map has degree one in the relevant homology degree and the chosen reading of the pulled-
back overlap agrees with the reading of the target overlap, the two read connecting morphisms
are equal.  Specializing the target to the standard vertex--edge cover of a mapping torus
identifies its low overlap leg with the canonical Wang boundary.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex

namespace BinaryOpenCover

/-- The ordinary homology map underlying the connecting morphism of a binary open cover. -/
public noncomputable def OpenCoverHomologyComparison.boundaryHom {X : TopCat}
    {U V : Opens X} (C : OpenCoverHomologyComparison U V) (n : ℕ) :
    IntegralSingularHomology (n + 1) X →+
      IntegralSingularHomology n ((Opens.toTopCat X).obj (U ⊓ V)) :=
  (C.boundary n).hom

/-- The homology map underlying the map from a pulled-back overlap to the target overlap. -/
public noncomputable def openIntersectionPullbackHomologyHom {X Y : TopCat}
    (f : X ⟶ Y) (U V : Opens Y) (n : ℕ) :
    IntegralSingularHomology n
        ((Opens.toTopCat X).obj ((Opens.map f).obj U ⊓ (Opens.map f).obj V)) →+
      IntegralSingularHomology n ((Opens.toTopCat Y).obj (U ⊓ V)) :=
  (openIntersectionPullbackHomologyMap f U V n).hom

/-- The homology map induced by a continuous map, in the additive-homomorphism interface. -/
public noncomputable def integralHomologyMapHom {X Y : TopCat}
    (f : X ⟶ Y) (n : ℕ) :
    IntegralSingularHomology n X →+ IntegralSingularHomology n Y :=
  ((integralHomologyFunctor n).map f).hom

/-- The pullback of a binary open cover is again a cover. -/
public theorem pullback_open_cover {X Y : TopCat} (f : X ⟶ Y)
    (U V : Opens Y) (hcover : U ⊔ V = ⊤) :
    (Opens.map f).obj U ⊔ (Opens.map f).obj V = ⊤ := by
  change (Opens.map f).obj (U ⊔ V) = ⊤
  rw [hcover]
  rfl

/-- A self-map homotopic to the identity has degree one in every integral homology degree. -/
public theorem integralHomologyMapHom_eq_id_of_homotopic_id
    {X : Type} [TopologicalSpace X] (f : C(X, X))
    (h : f.Homotopic (ContinuousMap.id X)) (n : ℕ) :
    integralHomologyMapHom (TopCat.ofHom f) n = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  change integralSingularHomologyMap n f x = x
  rw [integralSingularHomologyMap_congr_of_homotopic n h]
  exact integralSingularHomologyMap_id_wang n x

/-- Data saying that a self-map is degree one in degree `n + 1` and preserves a chosen reading
of the overlap of a two-open cover.  The source cover is literally the pullback cover, so its
Mayer--Vietoris naturality is supplied by the canonical chain construction rather than assumed
as a field. -/
public structure DegreeOnePullbackCoverComparison {X : TopCat}
    (f : X ⟶ X) (U V : Opens X) (n : ℕ)
    {K : Type*} [AddCommGroup K]
    (sourceRead : IntegralSingularHomology n
        ((Opens.toTopCat X).obj ((Opens.map f).obj U ⊓ (Opens.map f).obj V)) →+ K)
    (targetRead : IntegralSingularHomology n ((Opens.toTopCat X).obj (U ⊓ V)) →+ K) :
    Prop where
  degreeOne : integralHomologyMapHom f (n + 1) = AddMonoidHom.id _
  overlap : targetRead.comp (openIntersectionPullbackHomologyHom f U V n) = sourceRead

/-- A homotopy to the identity and the oriented overlap square construct the whole degree-one
comparison package. -/
public theorem DegreeOnePullbackCoverComparison.of_homotopic_id
    {X : Type} [TopologicalSpace X] (f : C(X, X))
    (h : f.Homotopic (ContinuousMap.id X)) (U V : Opens (TopCat.of X)) (n : ℕ)
    {K : Type*} [AddCommGroup K]
    (sourceRead : IntegralSingularHomology n
        ((Opens.toTopCat (TopCat.of X)).obj
          ((Opens.map (TopCat.ofHom f)).obj U ⊓ (Opens.map (TopCat.ofHom f)).obj V)) →+ K)
    (targetRead : IntegralSingularHomology n
        ((Opens.toTopCat (TopCat.of X)).obj (U ⊓ V)) →+ K)
    (hoverlap : targetRead.comp
      (openIntersectionPullbackHomologyHom (TopCat.ofHom f) U V n) = sourceRead) :
    DegreeOnePullbackCoverComparison (TopCat.ofHom f) U V n sourceRead targetRead where
  degreeOne := integralHomologyMapHom_eq_id_of_homotopic_id f h (n + 1)
  overlap := hoverlap

/-- A degree-one pullback comparison identifies the read connecting morphisms. -/
public theorem degreeOnePullbackCoverComparison_boundary {X : TopCat}
    (f : X ⟶ X) (U V : Opens X) (hcover : U ⊔ V = ⊤) (n : ℕ)
    {K : Type*} [AddCommGroup K]
    (sourceRead : IntegralSingularHomology n
        ((Opens.toTopCat X).obj ((Opens.map f).obj U ⊓ (Opens.map f).obj V)) →+ K)
    (targetRead : IntegralSingularHomology n ((Opens.toTopCat X).obj (U ⊓ V)) →+ K)
    (D : DegreeOnePullbackCoverComparison f U V n sourceRead targetRead) :
    sourceRead.comp
        ((openCoverHomologyComparisonOfCover
          (pullback_open_cover f U V hcover)).boundaryHom n) =
      targetRead.comp ((openCoverHomologyComparisonOfCover hcover).boundaryHom n) := by
  apply AddMonoidHom.ext
  intro x
  have h := OpenCoverHomologyComparison.boundary_pullback_naturality
    f U V
    (openCoverHomologyComparisonOfCover (pullback_open_cover f U V hcover))
    (openCoverHomologyComparisonOfCover hcover)
    (openCoverHomologyComparisonOfCover_pullbackNaturality
      f U V (pullback_open_cover f U V hcover) hcover) n
  have hfun := congrArg ConcreteCategory.hom h
  have hx := DFunLike.congr_fun hfun x
  change sourceRead
      ((openCoverHomologyComparisonOfCover
        (pullback_open_cover f U V hcover)).boundaryHom n x) = _
  rw [← D.overlap]
  change targetRead
      (openIntersectionPullbackHomologyHom f U V n
        ((openCoverHomologyComparisonOfCover
          (pullback_open_cover f U V hcover)).boundaryHom n x)) = _
  have hx' :
      openIntersectionPullbackHomologyHom f U V n
          ((openCoverHomologyComparisonOfCover
            (pullback_open_cover f U V hcover)).boundaryHom n x) =
        (openCoverHomologyComparisonOfCover hcover).boundaryHom n
          (integralHomologyMapHom f (n + 1) x) := by
    simpa [OpenCoverHomologyComparison.boundaryHom,
      openIntersectionPullbackHomologyHom, integralHomologyMapHom] using hx
  rw [hx']
  change targetRead ((openCoverHomologyComparisonOfCover hcover).boundaryHom n
      (integralHomologyMapHom f (n + 1) x)) =
    targetRead ((openCoverHomologyComparisonOfCover hcover).boundaryHom n x)
  rw [DFunLike.congr_fun D.degreeOne x]
  rfl

end BinaryOpenCover

namespace MappingTorusDegreeOneCoverComparison

open Topology.CanonicalProductWangBoundaryNaturality

variable {F : Type} [TopologicalSpace F]

private theorem mappingTorusOpensUnionHomologyIso_hom_apply
    (phi : F ≃ₜ F) (n : ℕ)
    (x : IntegralSingularHomology n
      (↑(vertexPiece (fun _ : Unit ↦ phi) ∪ edgePiece (fun _ : Unit ↦ phi)) :
        Set (CircleMappingTorus phi))) :
    (BinaryOpenCover.opensUnionHomologyIso
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
        (mappingTorusOpenCover phi) n).hom.hom x =
      unionEquiv (fun _ : Unit ↦ phi) n x := by
  have htop :
      (TopCat.isoOfHomeo (BinaryOpenCover.opensUnionHomeomorph
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
        (mappingTorusOpenCover phi))).hom =
        TopCat.ofHom (coverUnionCM (fun _ : Unit ↦ phi)) := by
    ext y
    rfl
  have hmap := congrArg (BinaryOpenCover.integralHomologyFunctor n).map htop
  exact DFunLike.congr_fun (congrArg ConcreteCategory.hom hmap) x

/-- The low-leg reading of the standard vertex--edge overlap of a circle mapping torus. -/
public noncomputable def lowOverlapRead (phi : F ≃ₜ F) (n : ℕ) :
    IntegralSingularHomology n
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus phi))).obj
          (mappingTorusVertexOpen phi ⊓ mappingTorusEdgeOpen phi)) →+
      IntegralSingularHomology n F := by
  let I := BinaryOpenCover.opensIntersectionHomologyIso
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n
  let openToLegacy := I.inv.hom
  let toLegs :
      IntegralSingularHomology n
          (↑((↑(mappingTorusVertexOpen phi) : Set (CircleMappingTorus phi)) ∩
            ↑(mappingTorusEdgeOpen phi)) : Set (CircleMappingTorus phi)) →+
        (Unit → IntegralSingularHomology n F) ×
          (Unit → IntegralSingularHomology n F) := by
    change IntegralSingularHomology n
        (↑(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)) :
          Set (CircleMappingTorus phi)) →+ _
    exact (overlapEquiv (fun _ : Unit ↦ phi) n).symm.toAddMonoidHom
  let first := (AddMonoidHom.fst (Unit → IntegralSingularHomology n F)
    (Unit → IntegralSingularHomology n F)).comp toLegs
  let evaluate : (Unit → IntegralSingularHomology n F) →+
      IntegralSingularHomology n F :=
    { toFun := fun x ↦ x ()
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact evaluate.comp (first.comp openToLegacy)

/-- Reading the low overlap leg of the canonical open-cover boundary gives the canonical Wang
boundary. -/
public theorem lowOverlapRead_comp_boundary (phi : F ≃ₜ F) (n : ℕ) :
    (lowOverlapRead phi n).comp
        ((mappingTorusOpenCoverHomologyComparison phi).boundaryHom n) =
      (circleMappingTorusWangPresentationOfCover phi n).boundary := by
  apply AddMonoidHom.ext
  intro x
  let I := BinaryOpenCover.opensIntersectionHomologyIso
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n
  let U := BinaryOpenCover.opensUnionHomologyIso
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
    (mappingTorusOpenCover phi) (n + 1)
  let y := (unionEquiv (fun _ : Unit ↦ phi) (n + 1)).symm x
  have hU : U.hom.hom y = x := by
    rw [mappingTorusOpensUnionHomologyIso_hom_apply]
    exact (unionEquiv (fun _ : Unit ↦ phi) (n + 1)).apply_symm_apply x
  have hLegacy :
      I.inv.hom (((mappingTorusOpenCoverHomologyComparison phi).boundary n).hom x) =
        coverBoundary (fun _ : Unit ↦ phi) n y := by
    unfold coverBoundary BinaryOpenCover.IntegralMayerVietorisData.legacyBoundary
    change I.inv.hom (((mappingTorusOpenCoverHomologyComparison phi).boundary n).hom x) =
      I.inv.hom (((mappingTorusOpenCoverHomologyComparison phi).boundary n).hom
        (U.hom.hom y))
    rw [hU]
  rw [circleMappingTorusWangPresentationOfCover_boundary_apply]
  unfold lowOverlapRead BinaryOpenCover.OpenCoverHomologyComparison.boundaryHom
  simp only [AddMonoidHom.comp_apply]
  rw [hLegacy]
  rfl

/-- Every degree-one self-map whose pullback cover has the same oriented low-overlap reading
identifies that pullback cover's Mayer--Vietoris boundary with the canonical Wang boundary. -/
public theorem degreeOnePullbackCover_boundary_eq_wang
    (phi : F ≃ₜ F) (f : TopCat.of (CircleMappingTorus phi) ⟶
      TopCat.of (CircleMappingTorus phi)) (n : ℕ)
    (sourceRead : IntegralSingularHomology n
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus phi))).obj
          ((Opens.map f).obj (mappingTorusVertexOpen phi) ⊓
            (Opens.map f).obj (mappingTorusEdgeOpen phi))) →+
      IntegralSingularHomology n F)
    (D : BinaryOpenCover.DegreeOnePullbackCoverComparison f
      (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n
      sourceRead (lowOverlapRead phi n)) :
    sourceRead.comp
        ((BinaryOpenCover.openCoverHomologyComparisonOfCover
          (BinaryOpenCover.pullback_open_cover f
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
            (mappingTorusOpenCover phi))).boundaryHom n) =
      (circleMappingTorusWangPresentationOfCover phi n).boundary := by
  rw [BinaryOpenCover.degreeOnePullbackCoverComparison_boundary f
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
    (mappingTorusOpenCover phi) n sourceRead (lowOverlapRead phi n) D]
  exact lowOverlapRead_comp_boundary phi n

end MappingTorusDegreeOneCoverComparison

end SphereSixComplex

end

end
