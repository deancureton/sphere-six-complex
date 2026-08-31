module

public import SphereSixComplex.Topology.MayerVietorisWangDegreeOneCoverComparison
public import SphereSixComplex.Topology.PaperSectionSevenCuspMeridianProjectionCompletion

/-!
# Naturality of the degree-zero Wang boundary under the base-circle projection

The mapping-torus projection to its base is realized first as a map to the mapping torus of the
identity of a point.  It preserves the standard vertex--edge cover and its two ordered overlap
legs, reducing the sign of the degree-zero Wang boundary to the corresponding calculation for
the identity mapping torus of a point.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Topology TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.MappingTorusBaseCircleWangNaturality

open BinaryOpenCover MappingTorusDegreeOneCoverComparison
open Topology.CanonicalProductWangBoundaryNaturality

variable {F : Type} [TopologicalSpace F]

/-- The cylinder-coordinate projection respects the mapping-torus endpoint relation. -/
public theorem pointMappingTorusProjection_respects (phi : F ≃ₜ F)
    (p q : Unit × unitInterval × F)
    (h : finiteBouquetMappingTorusSetoid (fun _ : Unit ↦ phi) p q) :
    Quotient.mk (finiteBouquetMappingTorusSetoid
        (fun _ : Unit ↦ Homeomorph.refl Unit)) ((), p.2.1, ()) =
      Quotient.mk (finiteBouquetMappingTorusSetoid
        (fun _ : Unit ↦ Homeomorph.refl Unit)) ((), q.2.1, ()) := by
  induction h with
  | rel x y hxy =>
      apply Quotient.sound
      apply Relation.EqvGen.rel
      rcases hxy with hxy | hxy | hxy
      · exact Or.inl ⟨Subsingleton.elim _ _,
          congrArg (fun z : unitInterval × F ↦ (z.1, ())) hxy.2⟩
      · exact Or.inr (Or.inl ⟨hxy.1, hxy.2.1, Subsingleton.elim _ _⟩)
      · exact Or.inr (Or.inr ⟨hxy.1, hxy.2.1, Subsingleton.elim _ _⟩)
  | refl x => rfl
  | symm x y hxy ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- The map from a circle mapping torus to the identity mapping torus of a point, retaining only
the oriented cylinder coordinate. -/
public def pointMappingTorusProjection (phi : F ≃ₜ F) :
    C(CircleMappingTorus phi, CircleMappingTorus (Homeomorph.refl Unit)) where
  toFun := Quotient.lift
    (fun p : Unit × unitInterval × F ↦
      Quotient.mk (finiteBouquetMappingTorusSetoid
        (fun _ : Unit ↦ Homeomorph.refl Unit)) ((), p.2.1, ()))
    (pointMappingTorusProjection_respects phi)
  continuous_toFun := continuous_quot_lift
    (pointMappingTorusProjection_respects phi)
    (continuous_quot_mk.comp
      (continuous_const.prodMk
        ((continuous_fst.comp continuous_snd).prodMk continuous_const)))

@[simp]
public theorem pointMappingTorusProjection_cylinderProjection (phi : F ≃ₜ F)
    (p : unitInterval × F) :
    pointMappingTorusProjection phi (circleMappingTorusCylinderProjection phi p) =
      circleMappingTorusCylinderProjection (Homeomorph.refl Unit) (p.1, ()) :=
  rfl

/-- After projecting the point mapping torus to its base circle, the point projection is the
original base-circle projection. -/
public theorem pointMappingTorusProjection_baseCircle (phi : F ≃ₜ F) :
    (circleMappingTorusBaseCircleProjection (Homeomorph.refl Unit)).comp
        (pointMappingTorusProjection phi) =
      circleMappingTorusBaseCircleProjection phi := by
  apply ContinuousMap.ext
  intro z
  induction z using Quotient.inductionOn with
  | _ p => rfl

/-- The point projection maps the marked source fibre to the marked point fibre. -/
public theorem pointMappingTorusProjection_fiberInclusion (phi : F ≃ₜ F) :
    (pointMappingTorusProjection phi).comp
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) =
      (finiteBouquetMappingTorusFiberInclusion
        (fun _ : Unit ↦ Homeomorph.refl Unit)).comp
          (ContinuousMap.const F ()) := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- The point projection pulls the target vertex member back to the source vertex member. -/
public theorem pointMappingTorusProjection_vertexOpen (phi : F ≃ₜ F) :
    (Opens.map (TopCat.ofHom (pointMappingTorusProjection phi))).obj
        (mappingTorusVertexOpen (Homeomorph.refl Unit)) =
      mappingTorusVertexOpen phi := by
  ext z
  induction z using Quotient.inductionOn with
  | _ p =>
    change pointMappingTorusProjection phi (bouquetMk (fun _ : Unit ↦ phi) p) ∈
        vertexPiece (fun _ : Unit ↦ Homeomorph.refl Unit) ↔
      bouquetMk (fun _ : Unit ↦ phi) p ∈ vertexPiece (fun _ : Unit ↦ phi)
    rw [show pointMappingTorusProjection phi (bouquetMk (fun _ : Unit ↦ phi) p) =
        bouquetMk (fun _ : Unit ↦ Homeomorph.refl Unit) ((), p.2.1, ()) by rfl,
      vertexPiece, vertexPiece, mem_bouquetPiece_mk_iff _ vertexBand_ends,
      mem_bouquetPiece_mk_iff _ vertexBand_ends]

/-- The point projection pulls the target edge member back to the source edge member. -/
public theorem pointMappingTorusProjection_edgeOpen (phi : F ≃ₜ F) :
    (Opens.map (TopCat.ofHom (pointMappingTorusProjection phi))).obj
        (mappingTorusEdgeOpen (Homeomorph.refl Unit)) =
      mappingTorusEdgeOpen phi := by
  ext z
  induction z using Quotient.inductionOn with
  | _ p =>
    change pointMappingTorusProjection phi (bouquetMk (fun _ : Unit ↦ phi) p) ∈
        edgePiece (fun _ : Unit ↦ Homeomorph.refl Unit) ↔
      bouquetMk (fun _ : Unit ↦ phi) p ∈ edgePiece (fun _ : Unit ↦ phi)
    rw [show pointMappingTorusProjection phi (bouquetMk (fun _ : Unit ↦ phi) p) =
        bouquetMk (fun _ : Unit ↦ Homeomorph.refl Unit) ((), p.2.1, ()) by rfl,
      edgePiece, edgePiece, mem_bouquetPiece_mk_iff _ edgeBand_ends,
      mem_bouquetPiece_mk_iff _ edgeBand_ends]

/-- The map on the standard cover overlaps, transported along the two pullback equalities. -/
public noncomputable def pointMappingTorusProjectionIntersectionHomologyMap
    (phi : F ≃ₜ F) (n : ℕ) :
    (integralHomologyFunctor n).obj
        ((Opens.toTopCat (TopCat.of (CircleMappingTorus phi))).obj
          (mappingTorusVertexOpen phi ⊓ mappingTorusEdgeOpen phi)) ⟶
      (integralHomologyFunctor n).obj
        ((Opens.toTopCat (TopCat.of
          (CircleMappingTorus (Homeomorph.refl Unit)))).obj
          (mappingTorusVertexOpen (Homeomorph.refl Unit) ⊓
            mappingTorusEdgeOpen (Homeomorph.refl Unit))) := by
  rw [← pointMappingTorusProjection_vertexOpen phi,
    ← pointMappingTorusProjection_edgeOpen phi]
  exact openIntersectionPullbackHomologyMap
    (TopCat.ofHom (pointMappingTorusProjection phi))
    (mappingTorusVertexOpen (Homeomorph.refl Unit))
    (mappingTorusEdgeOpen (Homeomorph.refl Unit)) n

/-- Transporting the canonical binary-cover comparison along equalities of both ordered opens
recovers the canonical comparison for the transported cover. -/
public theorem openCoverHomologyComparisonOfCover_transport
    {X : TopCat} {U V U' V' : Opens X} (hU : U = U') (hV : V = V')
    (hcover : U ⊔ V = ⊤) (hcover' : U' ⊔ V' = ⊤) :
    (by
      rw [← hU, ← hV]
      exact openCoverHomologyComparisonOfCover hcover) =
      openCoverHomologyComparisonOfCover hcover' := by
  subst U'
  subst V'
  rfl

/-- Pullback naturality, with its source cover transported along equalities to a named ordered
cover. -/
public theorem openCoverHomologyComparisonOfCover_boundary_pullback_transport
    {X Y : TopCat} (f : X ⟶ Y) (U V : Opens Y) (U' V' : Opens X)
    (hU : (Opens.map f).obj U = U') (hV : (Opens.map f).obj V = V')
    (hsource : U' ⊔ V' = ⊤) (htarget : U ⊔ V = ⊤) (n : ℕ) :
    (openCoverHomologyComparisonOfCover hsource).boundary n ≫
        (by
          rw [← hU, ← hV]
          exact openIntersectionPullbackHomologyMap f U V n) =
      (integralHomologyFunctor (n + 1)).map f ≫
        (openCoverHomologyComparisonOfCover htarget).boundary n := by
  subst U'
  subst V'
  exact OpenCoverHomologyComparison.boundary_pullback_naturality f U V
    (openCoverHomologyComparisonOfCover
      (pullback_open_cover f U V htarget))
    (openCoverHomologyComparisonOfCover htarget)
    (openCoverHomologyComparisonOfCover_pullbackNaturality f U V
      (pullback_open_cover f U V htarget) htarget) n

/-- The pullback comparison, transported to the literal standard source cover. -/
public noncomputable def pointMappingTorusProjectionPullbackComparison (phi : F ≃ₜ F) :
    OpenCoverHomologyComparison (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) := by
  rw [← pointMappingTorusProjection_vertexOpen phi,
    ← pointMappingTorusProjection_edgeOpen phi]
  exact openCoverHomologyComparisonOfCover
    (pullback_open_cover (TopCat.ofHom (pointMappingTorusProjection phi))
      (mappingTorusVertexOpen (Homeomorph.refl Unit))
      (mappingTorusEdgeOpen (Homeomorph.refl Unit))
      (mappingTorusOpenCover (Homeomorph.refl Unit)))

/-- Transporting the canonical pullback comparison does not change the canonical source
comparison. -/
public theorem pointMappingTorusProjectionPullbackComparison_eq (phi : F ≃ₜ F) :
    pointMappingTorusProjectionPullbackComparison phi =
      mappingTorusOpenCoverHomologyComparison phi := by
  exact openCoverHomologyComparisonOfCover_transport
    (pointMappingTorusProjection_vertexOpen phi)
    (pointMappingTorusProjection_edgeOpen phi)
    (pullback_open_cover (TopCat.ofHom (pointMappingTorusProjection phi))
      (mappingTorusVertexOpen (Homeomorph.refl Unit))
      (mappingTorusEdgeOpen (Homeomorph.refl Unit))
      (mappingTorusOpenCover (Homeomorph.refl Unit)))
    (mappingTorusOpenCover phi)

/-- Naturality of the canonical vertex--edge boundary under the projection to the point mapping
torus. -/
public theorem pointMappingTorusProjection_boundary_naturality (phi : F ≃ₜ F) :
    let f := TopCat.ofHom (pointMappingTorusProjection phi)
    (mappingTorusOpenCoverHomologyComparison phi).boundary 0 ≫
        pointMappingTorusProjectionIntersectionHomologyMap phi 0 =
      (integralHomologyFunctor 1).map f ≫
        (mappingTorusOpenCoverHomologyComparison
          (Homeomorph.refl Unit)).boundary 0 := by
  exact openCoverHomologyComparisonOfCover_boundary_pullback_transport
    (TopCat.ofHom (pointMappingTorusProjection phi))
    (mappingTorusVertexOpen (Homeomorph.refl Unit))
    (mappingTorusEdgeOpen (Homeomorph.refl Unit))
    (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi)
    (pointMappingTorusProjection_vertexOpen phi)
    (pointMappingTorusProjection_edgeOpen phi) (mappingTorusOpenCover phi)
    (mappingTorusOpenCover (Homeomorph.refl Unit)) 0

end SphereSixComplex.MappingTorusBaseCircleWangNaturality

end

end
