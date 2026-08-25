module

public import SphereSixComplex.Geometry.FourPieceStarGluing
public import SphereSixComplex.Geometry.GluingCompatibility
public import SphereSixComplex.ComplexStructure

/-!
# Biholomorphic star gluing

The standard complex-manifold gluing theorem says that complex manifolds glued along
biholomorphic open subsets inherit the atlas obtained by transporting the atlases of their
pieces.  This module states that formula-independent theorem for the four-piece star interface.
-/

open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing

noncomputable section

/-- Complex-manifold and biholomorphic-collar data on a four-piece star. -/
public structure BiholomorphicFourPieceStarData (A : FourPieceStarGluingData) where
  centralCharts : ChartedSpace ComplexModel A.central
  fillingCharts : ∀ i, ChartedSpace ComplexModel (A.filling i)
  centralManifold :
    letI := centralCharts
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ A.central
  fillingManifold :
    letI (i : Fin 3) := fillingCharts i
    ∀ i, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (A.filling i)
  /-- The analytic extension of each collar homeomorphism to an open partial diffeomorphism of
  the ambient pieces. -/
  collar :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) A.central (A.filling i) ∞
  collar_source :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, (collar i).source = A.centralCollar i
  collar_target :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i, (collar i).target = A.fillingCollar i
  collar_apply :
    letI := centralCharts
    letI (i : Fin 3) := fillingCharts i
    ∀ i (x : A.centralCollar i), collar i x.1 = (A.collarEquiv i x).1

namespace BiholomorphicFourPieceStarData

variable {A : FourPieceStarGluingData} (C : BiholomorphicFourPieceStarData A)

/-- The complex atlases of the central piece and three fillings, indexed by the star diagram. -/
@[instance_reducible] public def complexCharts :
    ∀ i, ChartedSpace ComplexModel (A.glueData.U i)
  | none => C.centralCharts
  | some i => C.fillingCharts i

end BiholomorphicFourPieceStarData


/-! ## Identifying the piece transitions with the collar data -/

/-- The overlap of the central piece with the `k`th filling is the `k`th central collar. -/
private theorem overlap_none_some (A : FourPieceStarGluingData) (k : Fin 3) :
    Set.range (A.glueData.toGlueData.f none (some k)) = (A.centralCollar k : Set A.central) :=
  TopologicalSpace.Opens.set_range_inclusion' _

/-- The overlap of the `k`th filling with the central piece is the `k`th filling collar. -/
private theorem overlap_some_none (A : FourPieceStarGluingData) (k : Fin 3) :
    Set.range (A.glueData.toGlueData.f (some k) none) = (A.fillingCollar k : Set (A.filling k)) :=
  TopologicalSpace.Opens.set_range_inclusion' _

/-- Two distinct fillings never overlap, since the attaching collars are disjoint. -/
private theorem overlap_some_some (A : FourPieceStarGluingData) {k l : Fin 3} (hkl : k ≠ l) :
    Set.range (A.glueData.toGlueData.f (some k) (some l)) = (∅ : Set (A.filling k)) := by
  refine (TopologicalSpace.Opens.set_range_inclusion' (A.overlap (some k) (some l))).trans ?_
  simp only [FourPieceStarGluingData.overlap, hkl, ite_false]
  rfl

namespace BiholomorphicFourPieceStarData

variable {A : FourPieceStarGluingData} (C : BiholomorphicFourPieceStarData A)

/-- Each of the four pieces is a complex manifold in its own atlas. -/
public theorem pieceManifold (hcollar : ∀ i, Nonempty (A.centralCollar i)) :
    letI := A.nonemptyPieceOfCollars hcollar
    letI := C.complexCharts
    ∀ i, IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ (A.glueData.U i) := by
  intro i
  cases i with
  | none => exact C.centralManifold
  | some k => exact C.fillingManifold k

end BiholomorphicFourPieceStarData

/-- Standard atlas compatibility for gluing complex manifolds along biholomorphic open subsets.

By `crossPieceGluingCompatible_of_pieceTransition_contMDiffOn` this reduces to smoothness of the
six transitions between distinct pieces, and each of those is identified here with the analytic
collar data: a central-to-filling transition is the given partial diffeomorphism, a
filling-to-central transition is its inverse, and a transition between two distinct fillings has
empty source because the attaching collars are disjoint. -/
public theorem establishedFourPieceBiholomorphicGluingAtlasCompatible
    (A : FourPieceStarGluingData)
    (hcollar : ∀ i, Nonempty (A.centralCollar i))
    (C : BiholomorphicFourPieceStarData A) :
    letI := A.nonemptyPieceOfCollars hcollar
    letI := C.complexCharts
    GluingAtlasCompatible (I := modelWithCornersSelf ℂ ComplexModel) (n := ∞) A.glueData := by
  letI := C.centralCharts
  letI (i : Fin 3) := C.fillingCharts i
  letI := A.nonemptyPieceOfCollars hcollar
  letI := C.complexCharts
  letI := C.pieceManifold hcollar
  refine gluingAtlasCompatible_of_crossPiece A.glueData ?_
  refine crossPieceGluingCompatible_of_pieceTransition_contMDiffOn A.glueData ?_
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => exact absurd rfl hij
      | some k =>
          have hsource : (pieceTransition A.glueData none (some k)).source =
              (C.collar k).source :=
            (pieceTransition_source A.glueData none (some k)).trans
              ((overlap_none_some A k).trans (C.collar_source k).symm)
          rw [hsource]
          refine ((C.collar k).contMDiffOn_toFun).congr ?_
          intro x hx
          have hx' : x ∈ (A.centralCollar k : Set A.central) := by
            rw [C.collar_source k] at hx
            exact hx
          have hpt : pieceTransition A.glueData none (some k) x =
              ((A.collarEquiv k ⟨x, hx'⟩ : A.fillingCollar k) : A.filling k) :=
            pieceTransition_apply A.glueData none (some k) (⟨x, hx'⟩ : A.centralCollar k)
          exact hpt.trans (C.collar_apply k ⟨x, hx'⟩).symm
  | some k =>
      cases j with
      | none =>
          have hsource : (pieceTransition A.glueData (some k) none).source =
              (C.collar k).target :=
            (pieceTransition_source A.glueData (some k) none).trans
              ((overlap_some_none A k).trans (C.collar_target k).symm)
          rw [hsource]
          refine ((C.collar k).contMDiffOn_invFun).congr ?_
          intro x hx
          have hx' : x ∈ (A.fillingCollar k : Set (A.filling k)) := by
            rw [C.collar_target k] at hx
            exact hx
          have hz : (((A.collarEquiv k).symm ⟨x, hx'⟩ : A.centralCollar k) : A.central) ∈
              (C.collar k).source := by
            rw [C.collar_source k]
            exact ((A.collarEquiv k).symm ⟨x, hx'⟩).2
          have hcollarApply : (C.collar k).toOpenPartialHomeomorph
              (((A.collarEquiv k).symm ⟨x, hx'⟩ : A.centralCollar k) : A.central) = x := by
            show C.collar k (((A.collarEquiv k).symm ⟨x, hx'⟩ : A.centralCollar k) : A.central) = x
            rw [C.collar_apply k ((A.collarEquiv k).symm ⟨x, hx'⟩)]
            change ((A.collarEquiv k) ((A.collarEquiv k).symm ⟨x, hx'⟩) : A.filling k) = x
            rw [Homeomorph.apply_symm_apply]
          have hinv : (C.collar k).toOpenPartialHomeomorph.symm x =
              (((A.collarEquiv k).symm ⟨x, hx'⟩ : A.centralCollar k) : A.central) := by
            have hleft := (C.collar k).toOpenPartialHomeomorph.left_inv hz
            rwa [hcollarApply] at hleft
          have hpt : pieceTransition A.glueData (some k) none x =
              (((A.collarEquiv k).symm ⟨x, hx'⟩ : A.centralCollar k) : A.central) :=
            pieceTransition_apply A.glueData (some k) none (⟨x, hx'⟩ : A.fillingCollar k)
          exact hpt.trans hinv.symm
      | some l =>
          have hkl : k ≠ l := fun h => hij (by rw [h])
          have hsource : (pieceTransition A.glueData (some k) (some l)).source = ∅ :=
            (pieceTransition_source A.glueData (some k) (some l)).trans
              (overlap_some_some A hkl)
          rw [hsource]
          intro y hy
          exact hy.elim

end

end SphereSixComplex.Geometry.EstablishedBiholomorphicStarGluing
