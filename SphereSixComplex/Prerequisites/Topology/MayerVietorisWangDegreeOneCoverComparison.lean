module

public import SphereSixComplex.Prerequisites.Topology.CanonicalProductWangBoundaryNaturality

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



/-- The pullback of a binary open cover is again a cover. -/
public theorem pullback_open_cover {X Y : TopCat} (f : X ⟶ Y)
    (U V : Opens Y) (hcover : U ⊔ V = ⊤) :
    (Opens.map f).obj U ⊔ (Opens.map f).obj V = ⊤ := by
  change (Opens.map f).obj (U ⊔ V) = ⊤
  rw [hcover]
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


end MappingTorusDegreeOneCoverComparison

end SphereSixComplex

end

end
