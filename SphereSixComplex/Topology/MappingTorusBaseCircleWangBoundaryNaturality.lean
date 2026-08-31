module

public import SphereSixComplex.Topology.MappingTorusBaseCircleWangNaturality

/-!
# The degree-zero Wang coordinate under the base-circle projection

The projection from a mapping torus to the identity mapping torus of a point preserves both
ordered overlap legs.  This identifies the degree-zero Wang boundary coordinate with the
corresponding coordinate after projection, without choosing an orientation of the target circle.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Topology TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.MappingTorusBaseCircleWangBoundaryNaturality

open BinaryOpenCover MappingTorusBaseCircleWangNaturality
open MappingTorusDegreeOneCoverComparison
open Topology.CanonicalProductWangBoundaryNaturality

variable {F : Type} [TopologicalSpace F]

public theorem pointMappingTorusProjection_overlap_mem (phi : F ≃ₜ F)
    (z : ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))) :
    pointMappingTorusProjection phi z.1 ∈
      vertexPiece (fun _ : Unit ↦ Homeomorph.refl Unit) ∩
        edgePiece (fun _ : Unit ↦ Homeomorph.refl Unit) := by
  constructor
  · change z.1 ∈ (Opens.map (TopCat.ofHom (pointMappingTorusProjection phi))).obj
        (mappingTorusVertexOpen (Homeomorph.refl Unit))
    rw [pointMappingTorusProjection_vertexOpen]
    exact z.2.1
  · change z.1 ∈ (Opens.map (TopCat.ofHom (pointMappingTorusProjection phi))).obj
        (mappingTorusEdgeOpen (Homeomorph.refl Unit))
    rw [pointMappingTorusProjection_edgeOpen]
    exact z.2.2

/-- The restriction of the point projection to the literal vertex--edge overlap. -/
public def pointMappingTorusProjectionOverlapMap (phi : F ≃ₜ F) :
    C(↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)),
      ↥(vertexPiece (fun _ : Unit ↦ Homeomorph.refl Unit) ∩
        edgePiece (fun _ : Unit ↦ Homeomorph.refl Unit))) where
  toFun z := ⟨pointMappingTorusProjection phi z.1,
    pointMappingTorusProjection_overlap_mem phi z⟩
  continuous_toFun := Continuous.subtype_mk
    ((pointMappingTorusProjection phi).continuous.comp continuous_subtype_val)
    (pointMappingTorusProjection_overlap_mem phi)

/-- On the low overlap leg, the point projection is the constant map on the fibre. -/
public theorem pointMappingTorusProjectionOverlapMap_comp_lowPt (phi : F ≃ₜ F) :
    (pointMappingTorusProjectionOverlapMap phi).comp
        (overlapPt (fun _ : Unit ↦ phi) uQuarter_mem_overlapBand ()) =
      (overlapPt (fun _ : Unit ↦ Homeomorph.refl Unit) uQuarter_mem_overlapBand ()).comp
        (ContinuousMap.const F ()) := by
  ext x
  rfl

/-- On the high overlap leg, the point projection is the constant map on the fibre. -/
public theorem pointMappingTorusProjectionOverlapMap_comp_highPt (phi : F ≃ₜ F) :
    (pointMappingTorusProjectionOverlapMap phi).comp
        (overlapPt (fun _ : Unit ↦ phi) uThreeQuarters_mem_overlapBand ()) =
      (overlapPt (fun _ : Unit ↦ Homeomorph.refl Unit)
        uThreeQuarters_mem_overlapBand ()).comp (ContinuousMap.const F ()) := by
  ext x
  rfl

public theorem openIntersectionMapOfPullbackEqualities_mem
    {X Y : TopCat} (f : X ⟶ Y) (U V : Opens Y) (U' V' : Opens X)
    (hU : (Opens.map f).obj U = U') (hV : (Opens.map f).obj V = V')
    (z : (Opens.toTopCat X).obj (U' ⊓ V')) : f z.1 ∈ U ⊓ V := by
  constructor
  · have hz : z.1 ∈ U' := z.2.1
    change z.1 ∈ (Opens.map f).obj U
    simpa only [hU] using hz
  · have hz : z.1 ∈ V' := z.2.2
    change z.1 ∈ (Opens.map f).obj V
    simpa only [hV] using hz

/-- The direct restriction between named intersections identified as pullbacks. -/
public def openIntersectionMapOfPullbackEqualities
    {X Y : TopCat} (f : X ⟶ Y) (U V : Opens Y) (U' V' : Opens X)
    (hU : (Opens.map f).obj U = U') (hV : (Opens.map f).obj V = V') :
    (Opens.toTopCat X).obj (U' ⊓ V') ⟶ (Opens.toTopCat Y).obj (U ⊓ V) :=
  TopCat.ofHom
    { toFun := fun z ↦ ⟨f z.1,
        openIntersectionMapOfPullbackEqualities_mem f U V U' V' hU hV z⟩
      continuous_toFun :=
        (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

/-- The map on the named intersections of the standard mapping-torus covers. -/
public def pointMappingTorusProjectionOpenIntersectionMap (phi : F ≃ₜ F) :
    (Opens.toTopCat (TopCat.of (CircleMappingTorus phi))).obj
        (mappingTorusVertexOpen phi ⊓ mappingTorusEdgeOpen phi) ⟶
      (Opens.toTopCat (TopCat.of
        (CircleMappingTorus (Homeomorph.refl Unit)))).obj
        (mappingTorusVertexOpen (Homeomorph.refl Unit) ⊓
          mappingTorusEdgeOpen (Homeomorph.refl Unit)) :=
  openIntersectionMapOfPullbackEqualities
    (TopCat.ofHom (pointMappingTorusProjection phi))
    (mappingTorusVertexOpen (Homeomorph.refl Unit))
    (mappingTorusEdgeOpen (Homeomorph.refl Unit))
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
    (pointMappingTorusProjection_vertexOpen phi)
    (pointMappingTorusProjection_edgeOpen phi)

public theorem openIntersectionPullbackHomologyMap_transport_eq_map
    {X Y : TopCat} (f : X ⟶ Y) (U V : Opens Y) (U' V' : Opens X)
    (hU : (Opens.map f).obj U = U') (hV : (Opens.map f).obj V = V') (n : ℕ) :
    (by
      rw [← hU, ← hV]
      exact openIntersectionPullbackHomologyMap f U V n) =
      (integralHomologyFunctor n).map
        (openIntersectionMapOfPullbackEqualities f U V U' V' hU hV) := by
  subst U'
  subst V'
  rfl

public theorem pointMappingTorusProjectionIntersectionHomologyMap_eq_map
    (phi : F ≃ₜ F) (n : ℕ) :
    pointMappingTorusProjectionIntersectionHomologyMap phi n =
      (integralHomologyFunctor n).map
        (pointMappingTorusProjectionOpenIntersectionMap phi) := by
  exact openIntersectionPullbackHomologyMap_transport_eq_map
    (TopCat.ofHom (pointMappingTorusProjection phi))
    (mappingTorusVertexOpen (Homeomorph.refl Unit))
    (mappingTorusEdgeOpen (Homeomorph.refl Unit))
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
    (pointMappingTorusProjection_vertexOpen phi)
    (pointMappingTorusProjection_edgeOpen phi) n

public theorem pointMappingTorusProjectionOpenIntersectionMap_legacy
    (phi : F ≃ₜ F) :
    (TopCat.isoOfHomeo (opensIntersectionHomeomorph
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi))).hom ≫
      pointMappingTorusProjectionOpenIntersectionMap phi ≫
      (TopCat.isoOfHomeo (opensIntersectionHomeomorph
        (mappingTorusVertexOpen (Homeomorph.refl Unit))
        (mappingTorusEdgeOpen (Homeomorph.refl Unit)))).inv =
      TopCat.ofHom (pointMappingTorusProjectionOverlapMap phi) := by
  ext z
  rfl

/-- The map on literal overlap homology obtained from the categorical pullback map. -/
public noncomputable def pointMappingTorusProjectionLegacyIntersectionMap
    (phi : F ≃ₜ F) (n : ℕ) :
    IntegralSingularHomology n
        ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi)) →+
      IntegralSingularHomology n
        ↥(vertexPiece (fun _ : Unit ↦ Homeomorph.refl Unit) ∩
          edgePiece (fun _ : Unit ↦ Homeomorph.refl Unit)) :=
  ConcreteCategory.hom
    ((opensIntersectionHomologyIso
        (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).hom ≫
      pointMappingTorusProjectionIntersectionHomologyMap phi n ≫
      (opensIntersectionHomologyIso
        (mappingTorusVertexOpen (Homeomorph.refl Unit))
        (mappingTorusEdgeOpen (Homeomorph.refl Unit)) n).inv)

/-- The transported categorical overlap map is the homology map of the literal restriction. -/
public theorem pointMappingTorusProjectionLegacyIntersectionMap_apply
    (phi : F ≃ₜ F) (n : ℕ)
    (x : IntegralSingularHomology n
      ↥(vertexPiece (fun _ : Unit ↦ phi) ∩ edgePiece (fun _ : Unit ↦ phi))) :
    pointMappingTorusProjectionLegacyIntersectionMap phi n x =
      integralSingularHomologyMap n (pointMappingTorusProjectionOverlapMap phi) x := by
  unfold pointMappingTorusProjectionLegacyIntersectionMap
  rw [pointMappingTorusProjectionIntersectionHomologyMap_eq_map]
  have hcat := congrArg (integralHomologyFunctor n).map
    (pointMappingTorusProjectionOpenIntersectionMap_legacy phi)
  simp only [Functor.map_comp] at hcat
  exact DFunLike.congr_fun (congrArg ConcreteCategory.hom hcat) x

/-- The point projection carries both ordered overlap legs through the constant fibre map. -/
public theorem pointMappingTorusProjectionLegacyIntersectionMap_overlapEquiv
    (phi : F ≃ₜ F) (n : ℕ) (x y : IntegralSingularHomology n F) :
    pointMappingTorusProjectionLegacyIntersectionMap phi n
        (overlapEquiv (fun _ : Unit ↦ phi) n
          ((fun _ : Unit ↦ x), fun _ : Unit ↦ y)) =
      overlapEquiv (fun _ : Unit ↦ Homeomorph.refl Unit) n
        ((fun _ : Unit ↦ integralSingularHomologyMap n (ContinuousMap.const F ()) x),
          fun _ : Unit ↦
            integralSingularHomologyMap n (ContinuousMap.const F ()) y) := by
  rw [pointMappingTorusProjectionLegacyIntersectionMap_apply]
  change integralSingularHomologyMap n (pointMappingTorusProjectionOverlapMap phi)
      (overlapLegSum (fun _ : Unit ↦ phi) n
        ((fun _ : Unit ↦ x), fun _ : Unit ↦ y)) =
    overlapLegSum (fun _ : Unit ↦ Homeomorph.refl Unit) n
      ((fun _ : Unit ↦ integralSingularHomologyMap n (ContinuousMap.const F ()) x),
        fun _ : Unit ↦ integralSingularHomologyMap n (ContinuousMap.const F ()) y)
  rw [overlapLegSum_apply, overlapLegSum_apply]
  simp only [Fintype.sum_unique]
  rw [map_add]
  congr 1
  · rw [integralSingularHomologyMap_comp_wang,
      pointMappingTorusProjectionOverlapMap_comp_lowPt]
    rw [← integralSingularHomologyMap_comp_wang]
  · rw [integralSingularHomologyMap_comp_wang,
      pointMappingTorusProjectionOverlapMap_comp_highPt]
    rw [← integralSingularHomologyMap_comp_wang]

/-- On either pair of ordered overlap coordinates, the target low-leg reading is the image of
the source low coordinate under the constant fibre map. -/
public theorem pointMappingTorusProjection_lowOverlapRead_overlapEquiv
    (phi : F ≃ₜ F) (n : ℕ) (x y : IntegralSingularHomology n F) :
    lowOverlapRead (Homeomorph.refl Unit) n
        (ConcreteCategory.hom
          (pointMappingTorusProjectionIntersectionHomologyMap phi n)
          (ConcreteCategory.hom
            (opensIntersectionHomologyIso
              (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).hom
            (overlapEquiv (fun _ : Unit ↦ phi) n
              ((fun _ : Unit ↦ x), fun _ : Unit ↦ y)))) =
      integralSingularHomologyMap n (ContinuousMap.const F ()) x := by
  have h := pointMappingTorusProjectionLegacyIntersectionMap_overlapEquiv phi n x y
  unfold pointMappingTorusProjectionLegacyIntersectionMap at h
  change ConcreteCategory.hom
      (opensIntersectionHomologyIso
        (mappingTorusVertexOpen (Homeomorph.refl Unit))
        (mappingTorusEdgeOpen (Homeomorph.refl Unit)) n).inv
        (ConcreteCategory.hom
          (pointMappingTorusProjectionIntersectionHomologyMap phi n)
          (ConcreteCategory.hom
            (opensIntersectionHomologyIso
              (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).hom
            (overlapEquiv (fun _ : Unit ↦ phi) n
              ((fun _ : Unit ↦ x), fun _ : Unit ↦ y)))) = _ at h
  unfold lowOverlapRead
  simp only [AddMonoidHom.comp_apply]
  rw [h]
  change (((overlapEquiv (fun _ : Unit ↦ Homeomorph.refl Unit) n).symm
    (overlapEquiv (fun _ : Unit ↦ Homeomorph.refl Unit) n
      ((fun _ : Unit ↦ integralSingularHomologyMap n (ContinuousMap.const F ()) x),
        fun _ : Unit ↦ integralSingularHomologyMap n (ContinuousMap.const F ()) y))).1 ()) = _
  rw [AddEquiv.symm_apply_apply]

/-- The low-overlap reader recovers the first literal overlap coordinate. -/
public theorem lowOverlapRead_opensIntersectionHomologyIso_overlapEquiv
    (phi : F ≃ₜ F) (n : ℕ) (x y : IntegralSingularHomology n F) :
    lowOverlapRead phi n
        (ConcreteCategory.hom
          (opensIntersectionHomologyIso
            (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n).hom
          (overlapEquiv (fun _ : Unit ↦ phi) n
            ((fun _ : Unit ↦ x), fun _ : Unit ↦ y))) = x := by
  let I := opensIntersectionHomologyIso
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n
  have hI : ConcreteCategory.hom I.inv
      (ConcreteCategory.hom I.hom
        (overlapEquiv (fun _ : Unit ↦ phi) n
          ((fun _ : Unit ↦ x), fun _ : Unit ↦ y))) =
      overlapEquiv (fun _ : Unit ↦ phi) n
        ((fun _ : Unit ↦ x), fun _ : Unit ↦ y) :=
    ConcreteCategory.congr_hom I.inv_hom_id _
  unfold lowOverlapRead
  simp only [AddMonoidHom.comp_apply]
  change (((overlapEquiv (fun _ : Unit ↦ phi) n).symm
    (ConcreteCategory.hom I.inv
      (ConcreteCategory.hom I.hom
        (overlapEquiv (fun _ : Unit ↦ phi) n
          ((fun _ : Unit ↦ x), fun _ : Unit ↦ y))))).1 ()) = x
  rw [hI, AddEquiv.symm_apply_apply]

/-- The ordered low-overlap reading commutes with the point projection in every degree. -/
public theorem pointMappingTorusProjection_lowOverlapRead_naturality
    (phi : F ≃ₜ F) (n : ℕ)
    (z : IntegralSingularHomology n
      ((Opens.toTopCat (TopCat.of (CircleMappingTorus phi))).obj
        (mappingTorusVertexOpen phi ⊓ mappingTorusEdgeOpen phi))) :
    lowOverlapRead (Homeomorph.refl Unit) n
        (ConcreteCategory.hom
          (pointMappingTorusProjectionIntersectionHomologyMap phi n) z) =
      integralSingularHomologyMap n (ContinuousMap.const F ())
        (lowOverlapRead phi n z) := by
  let I := opensIntersectionHomologyIso
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) n
  let p := (overlapEquiv (fun _ : Unit ↦ phi) n).symm
    (ConcreteCategory.hom I.inv z)
  let x := p.1 ()
  let y := p.2 ()
  have hp : p = ((fun _ : Unit ↦ x), fun _ : Unit ↦ y) := by
    apply Prod.ext <;> funext i <;> cases i <;> rfl
  have hw : overlapEquiv (fun _ : Unit ↦ phi) n
      ((fun _ : Unit ↦ x), fun _ : Unit ↦ y) =
      ConcreteCategory.hom I.inv z := by
    rw [← hp]
    exact (overlapEquiv (fun _ : Unit ↦ phi) n).apply_symm_apply _
  have hz : ConcreteCategory.hom I.hom
      (overlapEquiv (fun _ : Unit ↦ phi) n
        ((fun _ : Unit ↦ x), fun _ : Unit ↦ y)) = z := by
    rw [hw]
    exact ConcreteCategory.congr_hom I.hom_inv_id z
  rw [← hz, pointMappingTorusProjection_lowOverlapRead_overlapEquiv,
    lowOverlapRead_opensIntersectionHomologyIso_overlapEquiv]

/-- The degree-zero Wang boundary is natural under projection to the identity mapping torus of a
point, with the ordered low overlap fixing the sign. -/
public theorem pointMappingTorusProjection_wangBoundary_naturality
    (phi : F ≃ₜ F)
    (z : IntegralSingularHomology 1 (CircleMappingTorus phi)) :
    (circleMappingTorusWangPresentationOfCover (Homeomorph.refl Unit) 0).boundary
        (integralSingularHomologyMap 1 (pointMappingTorusProjection phi) z) =
      integralSingularHomologyMap 0 (ContinuousMap.const F ())
        ((circleMappingTorusWangPresentationOfCover phi 0).boundary z) := by
  have hnat := pointMappingTorusProjection_boundary_naturality phi
  have hz := DFunLike.congr_fun (congrArg ConcreteCategory.hom hnat) z
  calc
    _ = lowOverlapRead (Homeomorph.refl Unit) 0
        ((mappingTorusOpenCoverHomologyComparison (Homeomorph.refl Unit)).boundaryHom 0
          (integralSingularHomologyMap 1 (pointMappingTorusProjection phi) z)) := by
      exact (DFunLike.congr_fun
        (lowOverlapRead_comp_boundary (Homeomorph.refl Unit) 0) _).symm
    _ = lowOverlapRead (Homeomorph.refl Unit) 0
        (ConcreteCategory.hom (pointMappingTorusProjectionIntersectionHomologyMap phi 0)
          ((mappingTorusOpenCoverHomologyComparison phi).boundaryHom 0 z)) := by
      congr 1
      exact hz.symm
    _ = integralSingularHomologyMap 0 (ContinuousMap.const F ())
        (lowOverlapRead phi 0
          ((mappingTorusOpenCoverHomologyComparison phi).boundaryHom 0 z)) :=
      pointMappingTorusProjection_lowOverlapRead_naturality phi 0 _
    _ = _ := by
      have hs := DFunLike.congr_fun (lowOverlapRead_comp_boundary phi 0) z
      change lowOverlapRead phi 0
          ((mappingTorusOpenCoverHomologyComparison phi).boundaryHom 0 z) =
        (circleMappingTorusWangPresentationOfCover phi 0).boundary z at hs
      rw [hs]

end SphereSixComplex.MappingTorusBaseCircleWangBoundaryNaturality

end

end
