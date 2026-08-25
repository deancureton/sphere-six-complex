module

public import SphereSixComplex.Topology.SimplicialSingularComparison
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases

/-!
# The geometric realization of the boundary of the seven-simplex

This file isolates the canonical map from `|∂Δ[7]|` to the ordinary topological seven-simplex
and its compatibility with all eight codimension-one faces.  It also uses gauge rescaling to
identify the ordinary affine boundary with the project's unit six-sphere.  Thus the only missing
geometric-realization input is that realization of the simplicial subcomplex carries the expected
subspace topology and underlying boundary points.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Simplicial

namespace SphereSixComplex

/-- The ordinary boundary of a standard simplex: at least one barycentric coordinate vanishes. -/
public abbrev StandardSimplexBoundary (n : ℕ) :=
  {w : stdSimplex ℝ (Fin (n + 1)) // ∃ i, w i = 0}

/-- The canonical map from realization of the simplicial boundary into the ordinary standard
seven-simplex. -/
public noncomputable def boundarySevenRealizationToStdSimplex :
    C((SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type), stdSimplex ℝ (Fin 8)) :=
  ⟨fun x ↦ SimplexCategory.toTopHomeo (SimplexCategory.mk 7)
      (SSet.toTop.map (SSet.boundary 7).ι x),
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 7)).continuous.comp
      (SSet.toTop.map (SSet.boundary 7).ι).hom.continuous⟩

/-- On each simplicial face, the canonical realization map is the usual affine face inclusion. -/
public theorem boundarySevenRealizationToStdSimplex_face
    (i : Fin 8) (x : (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type)) :
    boundarySevenRealizationToStdSimplex
        (SSet.toTop.map (SSet.boundary.ι i) x) =
      stdSimplex.map i.succAbove
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x) := by
  unfold boundarySevenRealizationToStdSimplex
  change SimplexCategory.toTopHomeo (SimplexCategory.mk 7)
      (SSet.toTop.map (SSet.boundary 7).ι
        (SSet.toTop.map (SSet.boundary.ι i) x)) = _
  rw [← ConcreteCategory.comp_apply]
  rw [← SSet.toTop.map_comp]
  rw [SSet.boundary.ι_ι]
  exact SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i) x

/-- The ordinary affine inclusion of a codimension-one face lands in the topological boundary. -/
public noncomputable def standardSimplexFaceToBoundary
    (n : ℕ) (i : Fin (n + 2)) :
    C(stdSimplex ℝ (Fin (n + 1)), StandardSimplexBoundary (n + 1)) := by
  let f : C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
    ⟨stdSimplex.map i.succAbove, stdSimplex.continuous_map i.succAbove⟩
  refine ⟨fun w ↦ ⟨f w, ⟨i, ?_⟩⟩, f.continuous.subtype_mk _⟩
  classical
  change stdSimplex.map i.succAbove w i = 0
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro j hj
  exact (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2).elim

/-- The realization map restricted to every face agrees with the corresponding map to the
ordinary topological boundary, after forgetting the boundary witness. -/
public theorem boundarySevenRealizationToStdSimplex_face_eq_val
    (i : Fin 8) (x : (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type)) :
    boundarySevenRealizationToStdSimplex
        (SSet.toTop.map (SSet.boundary.ι i) x) =
      (standardSimplexFaceToBoundary 6 i
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x) :
          stdSimplex ℝ (Fin 8)) := by
  change boundarySevenRealizationToStdSimplex
      (SSet.toTop.map (SSet.boundary.ι i) x) =
    stdSimplex.map i.succAbove
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) x)
  exact boundarySevenRealizationToStdSimplex_face i x

/-- A chosen affine basis with eight vertices in seven-dimensional Euclidean space. -/
public noncomputable def boundarySevenAffineBasis :
    AffineBasis (Fin 8) ℝ (EuclideanSpace ℝ (Fin 7)) :=
  Classical.choice (AffineBasis.exists_affineBasis_of_finiteDimensional
    (k := ℝ) (V := EuclideanSpace ℝ (Fin 7))
    (P := EuclideanSpace ℝ (Fin 7)) (ι := Fin 8) (by simp))

/-- The compact convex body spanned by the chosen affine basis. -/
public def boundarySevenAffineBody : Set (EuclideanSpace ℝ (Fin 7)) :=
  convexHull ℝ (Set.range boundarySevenAffineBasis)

public theorem boundarySevenAffineBody_convex : Convex ℝ boundarySevenAffineBody :=
  convex_convexHull ℝ _

public theorem boundarySevenAffineBody_bounded : Bornology.IsBounded boundarySevenAffineBody := by
  unfold boundarySevenAffineBody
  rw [isBounded_convexHull]
  exact (Set.finite_range boundarySevenAffineBasis).isBounded

public theorem boundarySevenAffineBody_interior_nonempty :
    (interior boundarySevenAffineBody).Nonempty := by
  exact ⟨_, boundarySevenAffineBasis.centroid_mem_interior_convexHull⟩

/-- Barycentric coordinates identify the standard seven-simplex with the convex hull of the
chosen affine basis. -/
public noncomputable def stdSimplexHomeomorphBoundarySevenAffineBody :
    stdSimplex ℝ (Fin 8) ≃ₜ boundarySevenAffineBody where
  toFun w := ⟨Finset.univ.affineCombination ℝ boundarySevenAffineBasis w,
    affineCombination_mem_convexHull (fun i _ ↦ w.2.1 i) w.2.2⟩
  invFun x := ⟨fun i ↦ boundarySevenAffineBasis.coord i x,
    ⟨fun i ↦ by
        have hx : x.1 ∈ convexHull ℝ (Set.range boundarySevenAffineBasis) := by
          simpa only [boundarySevenAffineBody] using x.2
        rw [boundarySevenAffineBasis.convexHull_eq_nonneg_coord] at hx
        exact hx i,
      boundarySevenAffineBasis.sum_coord_apply_eq_one x⟩⟩
  left_inv w := by
    apply Subtype.ext
    ext i
    exact boundarySevenAffineBasis.coord_apply_combination_of_mem
      (Finset.mem_univ i) w.2.2
  right_inv x := by
    apply Subtype.ext
    exact boundarySevenAffineBasis.affineCombination_coord_eq_self x
  continuous_toFun := by
    apply Continuous.subtype_mk
    have h : Continuous (fun w : stdSimplex ℝ (Fin 8) ↦
        ∑ i, w i • boundarySevenAffineBasis i) := by
      apply continuous_finsetSum
      intro i hi
      exact ((continuous_apply i).comp continuous_subtype_val).smul continuous_const
    exact h.congr fun w ↦
      (Finset.univ.affineCombination_eq_linear_combination
        boundarySevenAffineBasis w w.2.2).symm
  continuous_invFun := by
    have h : Continuous (fun x : boundarySevenAffineBody ↦
        fun i ↦ boundarySevenAffineBasis.coord i x) := by
      apply continuous_pi
      intro i
      exact (continuous_barycentric_coord boundarySevenAffineBasis i).comp
        continuous_subtype_val
    exact h.subtype_mk _

/-- Gauge rescaling supplies an ambient homeomorphism carrying the affine-simplex frontier to the
unit sphere in seven-dimensional Euclidean space. -/
public noncomputable def boundarySevenAffineBodyGaugeHomeomorph :
    EuclideanSpace ℝ (Fin 7) ≃ₜ EuclideanSpace ℝ (Fin 7) :=
  Classical.choose (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    boundarySevenAffineBody_convex boundarySevenAffineBody_interior_nonempty
      boundarySevenAffineBody_bounded)

public theorem boundarySevenAffineBodyGaugeHomeomorph_frontier :
    boundarySevenAffineBodyGaugeHomeomorph '' frontier boundarySevenAffineBody =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1 :=
  (Classical.choose_spec (exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    boundarySevenAffineBody_convex boundarySevenAffineBody_interior_nonempty
      boundarySevenAffineBody_bounded)).2.2

public theorem boundarySevenAffineBody_closed : IsClosed boundarySevenAffineBody := by
  unfold boundarySevenAffineBody
  exact ((Set.finite_range boundarySevenAffineBasis).isCompact_convexHull ℝ).isClosed

/-- Under barycentric coordinates, belonging to the frontier is exactly the vanishing of at least
one standard-simplex coordinate. -/
public theorem stdSimplexHomeomorphBoundarySevenAffineBody_mem_frontier_iff
    (w : stdSimplex ℝ (Fin 8)) :
    (stdSimplexHomeomorphBoundarySevenAffineBody w :
        EuclideanSpace ℝ (Fin 7)) ∈
        frontier boundarySevenAffineBody ↔
      ∃ i, w i = 0 := by
  classical
  have hcoord (i : Fin 8) :
      boundarySevenAffineBasis.coord i
          (stdSimplexHomeomorphBoundarySevenAffineBody w) = w i :=
    boundarySevenAffineBasis.coord_apply_combination_of_mem
      (Finset.mem_univ i) w.2.2
  have hinter :
      (stdSimplexHomeomorphBoundarySevenAffineBody w :
          EuclideanSpace ℝ (Fin 7)) ∈
          interior boundarySevenAffineBody ↔
        ∀ i, 0 < w i := by
    have hset : interior boundarySevenAffineBody =
        {x | ∀ i, 0 < boundarySevenAffineBasis.coord i x} := by
      simpa only [boundarySevenAffineBody] using
        boundarySevenAffineBasis.interior_convexHull
    rw [hset]
    constructor
    · intro h i
      exact (hcoord i) ▸ h i
    · intro h i
      exact (hcoord i).symm ▸ h i
  rw [boundarySevenAffineBody_closed.frontier_eq]
  simp only [Set.mem_sdiff, (stdSimplexHomeomorphBoundarySevenAffineBody w).2,
    true_and, hinter]
  constructor
  · rw [not_forall]
    rintro ⟨i, hi⟩
    exact ⟨i, le_antisymm (le_of_not_gt hi) (w.2.1 i)⟩
  · rintro ⟨i, hi⟩ hall
    exact (ne_of_gt (hall i)) hi

/-- Flatten the frontier regarded as a subspace of the affine body to the same frontier regarded
as a subspace of the ambient Euclidean space. -/
public noncomputable def boundarySevenFrontierInBodyHomeomorphFrontier :
    {y : boundarySevenAffineBody //
      (y : EuclideanSpace ℝ (Fin 7)) ∈ frontier boundarySevenAffineBody} ≃ₜ
      frontier boundarySevenAffineBody where
  toFun y := ⟨y.1.1, y.2⟩
  invFun x := ⟨⟨x.1, by
      simpa only [boundarySevenAffineBody_closed.closure_eq] using
        (frontier_subset_closure x.2)⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk fun x ↦ by
      simpa only [boundarySevenAffineBody_closed.closure_eq] using
        (frontier_subset_closure x.2)

/-- The ordinary barycentric boundary of the standard seven-simplex is homeomorphic to the
frontier of a full-dimensional affine simplex in seven-dimensional Euclidean space. -/
public noncomputable def standardSimplexBoundarySevenHomeomorphAffineFrontier :
    StandardSimplexBoundary 7 ≃ₜ frontier boundarySevenAffineBody := by
  let e : StandardSimplexBoundary 7 ≃ₜ
      {y : boundarySevenAffineBody //
        (y : EuclideanSpace ℝ (Fin 7)) ∈ frontier boundarySevenAffineBody} :=
    stdSimplexHomeomorphBoundarySevenAffineBody.subtype
      (p := fun w : stdSimplex ℝ (Fin 8) ↦ ∃ i, w i = 0)
      (q := fun y : boundarySevenAffineBody ↦
        (y : EuclideanSpace ℝ (Fin 7)) ∈
        frontier boundarySevenAffineBody)
      (fun w ↦ (stdSimplexHomeomorphBoundarySevenAffineBody_mem_frontier_iff w).symm)
  exact e.trans boundarySevenFrontierInBodyHomeomorphFrontier

/-- Gauge rescaling restricts to a homeomorphism from the affine-simplex frontier to the unit
six-sphere. -/
public noncomputable def boundarySevenAffineFrontierHomeomorphSixSphere :
    frontier boundarySevenAffineBody ≃ₜ SixSphere :=
  boundarySevenAffineBodyGaugeHomeomorph.subtype fun x ↦ by
    constructor
    · intro hx
      rw [← boundarySevenAffineBodyGaugeHomeomorph_frontier]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← boundarySevenAffineBodyGaugeHomeomorph_frontier] at hx
      obtain ⟨y, hy, heq⟩ := hx
      have hxy : y = x := boundarySevenAffineBodyGaugeHomeomorph.injective heq
      simpa [hxy] using hy

/-- The ordinary topological boundary of the seven-simplex is the project's standard unit
six-sphere. -/
public noncomputable def standardSimplexBoundarySevenHomeomorphSixSphere :
    StandardSimplexBoundary 7 ≃ₜ SixSphere :=
  standardSimplexBoundarySevenHomeomorphAffineFrontier.trans
    boundarySevenAffineFrontierHomeomorphSixSphere

/-! ## The exact realization/subspace gap -/

/-- The boundary is categorically the multicoequalizer of its eight faces and their pairwise
intersections. -/
public theorem boundarySevenFaceMulticoequalizerDiagram :
    SSet.Subcomplex.MulticoequalizerDiagram (SSet.boundary 7)
      (fun i : Fin 8 ↦ SSet.stdSimplex.face {i}ᶜ)
      (fun i j : Fin 8 ↦ SSet.stdSimplex.face {i}ᶜ ⊓
        SSet.stdSimplex.face {j}ᶜ) where
  iSup_eq := (SSet.boundary_eq_iSup 7).symm
  eq_inf _ _ := rfl

/-- Since geometric realization is a left adjoint, realization of the boundary is the same
multicoequalizer of realized faces. -/
public noncomputable def boundarySevenRealizationIsColimitOfFaces :
    IsColimit
      (SSet.toTop.mapCocone
        (boundarySevenFaceMulticoequalizerDiagram.multicofork.map
          SSet.Subcomplex.toSSetFunctor)) :=
  isColimitOfPreserves SSet.toTop
    boundarySevenFaceMulticoequalizerDiagram.isColimit

/-- Every point of the realized boundary is represented by a point of one of its eight
codimension-one simplicial faces.  This is the point-set surjectivity part of the realized
multicoequalizer, extracted after forgetting the topology. -/
public theorem boundarySevenRealization_faceCovered
    (x : (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type)) :
    ∃ (i : Fin 8)
      (y : (SSet.toTop.obj
        (SSet.stdSimplex.face {i}ᶜ : SSet.Subcomplex (Δ[7] : SSet.{0})) : Type)),
      SSet.toTop.map (SSet.boundary.faceι i) y = x := by
  have h := isColimitOfPreserves (forget TopCat)
    boundarySevenRealizationIsColimitOfFaces
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit h x
  rcases j with l | i
  · let f := WalkingMultispan.Hom.fst
      (J := MultispanShape.prod (Fin 8)) l
    let y' := (((boundarySevenFaceMulticoequalizerDiagram.multispanIndex.map
      SSet.Subcomplex.toSSetFunctor).multispan ⋙ SSet.toTop) ⋙
        forget TopCat).map f y
    refine ⟨l.1, y', ?_⟩
    have hw := ((forget TopCat).mapCocone
      (SSet.toTop.mapCocone
        (boundarySevenFaceMulticoequalizerDiagram.multicofork.map
          SSet.Subcomplex.toSSetFunctor))).w f
    exact (ConcreteCategory.congr_hom hw y).trans hy
  · exact ⟨i, y, hy⟩

/-- Equivalently, every realized boundary point comes from an ordinary standard six-simplex via
one of the eight standard boundary maps. -/
public theorem boundarySevenRealization_standardFaceCovered
    (x : (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type)) :
    ∃ (i : Fin 8) (y : (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type)),
      SSet.toTop.map (SSet.boundary.ι i) y = x := by
  obtain ⟨i, y, hy⟩ := boundarySevenRealization_faceCovered x
  refine ⟨i, SSet.toTop.map (SSet.stdSimplex.faceSingletonComplIso i).inv y, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← SSet.toTop.map_comp,
    SSet.boundary.faceSingletonComplIso_inv_ι]
  exact hy

public theorem boundarySevenRealizationToStdSimplex_mem_boundary
    (x : (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type)) :
    ∃ i, boundarySevenRealizationToStdSimplex x i = 0 := by
  obtain ⟨i, y, rfl⟩ := boundarySevenRealization_standardFaceCovered x
  rw [boundarySevenRealizationToStdSimplex_face_eq_val]
  exact (standardSimplexFaceToBoundary 6 i
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y)).2

/-- The canonical realization map, now lifted to the ordinary zero-coordinate boundary.  The
landing condition follows from the face cover, so it requires no choice of a preferred face. -/
public noncomputable def boundarySevenRealizationToBoundary :
    C((SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type), StandardSimplexBoundary 7) :=
  ⟨fun x ↦ ⟨boundarySevenRealizationToStdSimplex x,
      boundarySevenRealizationToStdSimplex_mem_boundary x⟩,
    boundarySevenRealizationToStdSimplex.continuous.subtype_mk _⟩

@[simp]
public theorem boundarySevenRealizationToBoundary_val
    (x : (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type)) :
    (boundarySevenRealizationToBoundary x : stdSimplex ℝ (Fin 8)) =
      boundarySevenRealizationToStdSimplex x := rfl

/-- Every point of the ordinary barycentric boundary belongs to one of the standard affine
faces. -/
public theorem standardSimplexBoundarySeven_standardFaceCovered
    (w : StandardSimplexBoundary 7) :
    ∃ (i : Fin 8) (z : stdSimplex ℝ (Fin 7)),
      stdSimplex.map i.succAbove z = w.1 := by
  classical
  obtain ⟨i, hi⟩ := w.2
  let z : stdSimplex ℝ (Fin 7) := ⟨fun j ↦ w.1 (i.succAbove j),
    ⟨fun j ↦ w.1.2.1 (i.succAbove j), by
      have hsum := w.1.2.2
      change ∑ k, w.1 k = 1 at hsum
      rw [Fin.sum_univ_succAbove (fun k ↦ w.1 k) i, hi, zero_add] at hsum
      exact hsum⟩⟩
  refine ⟨i, z, ?_⟩
  apply stdSimplex.ext
  funext k
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i k
  · simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_eq_zero]
    · exact hi.symm
    · intro j hj
      exact (Fin.succAbove_ne k j (Finset.mem_filter.mp hj).2).elim
  · simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_eq_single j]
    · rfl
    · intro b hb hbj
      exact (hbj (Fin.succAbove_right_inj.mp (Finset.mem_filter.mp hb).2)).elim
    · simp

/-- The canonical map from the realized simplicial boundary onto the ordinary barycentric
boundary is surjective. -/
public theorem boundarySevenRealizationToBoundary_surjective :
    Function.Surjective boundarySevenRealizationToBoundary := by
  intro w
  obtain ⟨i, z, hz⟩ := standardSimplexBoundarySeven_standardFaceCovered w
  let y := (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).symm z
  refine ⟨SSet.toTop.map (SSet.boundary.ι i) y, ?_⟩
  apply Subtype.ext
  rw [boundarySevenRealizationToBoundary_val,
    boundarySevenRealizationToStdSimplex_face]
  change stdSimplex.map i.succAbove
    (SimplexCategory.toTopHomeo (SimplexCategory.mk 6) y) = w.1
  rw [Homeomorph.apply_symm_apply]
  exact hz

/-- The realized simplicial boundary is compact: it is a finite union of the continuous images of
the eight compact realized standard six-simplices. -/
public theorem boundarySevenRealization_isCompact_univ :
    IsCompact (Set.univ : Set (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type)) := by
  have hsource : IsCompact
      (Set.univ : Set (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type)) := by
    simpa only [Set.image_univ,
      (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).symm.surjective.range_eq]
      using (isCompact_univ.image
        (SimplexCategory.toTopHomeo (SimplexCategory.mk 6)).symm.continuous)
  have hface (i : Fin 8) : IsCompact
      (Set.range fun y : (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type) ↦
        SSet.toTop.map (SSet.boundary.ι i) y) :=
    by simpa only [Set.image_univ] using
      hsource.image (SSet.toTop.map (SSet.boundary.ι i)).hom.continuous
  have hcover : (⋃ i : Fin 8, Set.range fun y :
      (SSet.toTop.obj (Δ[6] : SSet.{0}) : Type) ↦
        SSet.toTop.map (SSet.boundary.ι i) y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := boundarySevenRealization_standardFaceCovered x
    exact Set.mem_iUnion.2 ⟨i, ⟨y, hy⟩⟩
  rw [← hcover]
  exact isCompact_iUnion hface

/-- Injectivity is the only remaining point-set condition needed to turn the canonical continuous
surjection into a homeomorphism. -/
public noncomputable def boundarySevenRealizationHomeomorphStandardBoundary_of_injective
    (hinj : Function.Injective boundarySevenRealizationToBoundary) :
    (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ StandardSimplexBoundary 7 := by
  letI : CompactSpace (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) :=
    isCompact_univ_iff.mp boundarySevenRealization_isCompact_univ
  exact (Equiv.ofBijective boundarySevenRealizationToBoundary
    ⟨hinj, boundarySevenRealizationToBoundary_surjective⟩).toHomeomorphOfContinuousClosed
      boundarySevenRealizationToBoundary.continuous
      boundarySevenRealizationToBoundary.continuous.isClosedMap

/-- The one missing topological realization theorem: the canonical map identifies realization of
the simplicial boundary with the ordinary zero-coordinate boundary, not merely face by face. -/
public def BoundarySevenRealizationIdentifiesStandardSimplexBoundary : Prop :=
  ∃ e : (SSet.toTop.obj (∂Δ[7] : SSet.{0}) : Type) ≃ₜ StandardSimplexBoundary 7,
    ∀ x, (e x : stdSimplex ℝ (Fin 8)) = boundarySevenRealizationToStdSimplex x

/-- The exact remaining content of the realization/subspace comparison is injectivity of the
canonical map.  Surjectivity, continuity, compactness of the source, and Hausdorffness of the
target have all been proved above. -/
public theorem boundarySevenRealizationIdentifiesStandardSimplexBoundary_iff_injective :
    BoundarySevenRealizationIdentifiesStandardSimplexBoundary ↔
      Function.Injective boundarySevenRealizationToBoundary := by
  constructor
  · rintro ⟨e, he⟩ x y hxy
    apply e.injective
    apply Subtype.ext
    rw [he x, he y]
    exact congr_arg Subtype.val hxy
  · intro hinj
    refine ⟨boundarySevenRealizationHomeomorphStandardBoundary_of_injective hinj, ?_⟩
    intro x
    rfl

/-- Equivalently, the remaining injectivity assertion says that geometric realization sends the
monomorphism from the simplicial boundary into the representable seven-simplex to an injective
continuous map. -/
public theorem boundarySevenRealizationToBoundary_injective_iff_realizedInclusion :
    Function.Injective boundarySevenRealizationToBoundary ↔
      Function.Injective (SSet.toTop.map
        (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι) := by
  constructor
  · intro h x y hxy
    apply h
    apply Subtype.ext
    rw [boundarySevenRealizationToBoundary_val,
      boundarySevenRealizationToBoundary_val]
    exact congr_arg (SimplexCategory.toTopHomeo (SimplexCategory.mk 7)) hxy
  · intro h x y hxy
    apply h
    apply (SimplexCategory.toTopHomeo (SimplexCategory.mk 7)).injective
    change boundarySevenRealizationToStdSimplex x =
      boundarySevenRealizationToStdSimplex y
    exact congr_arg Subtype.val hxy

/-- Once the realization functor's face-colimit is identified with the ordinary closed face
cover, the desired realization/sphere homeomorphism follows from the concrete affine geometry
proved above. -/
public theorem boundarySevenRealizationHomeomorphSixSphere_of_identifiesBoundary
    (h : BoundarySevenRealizationIdentifiesStandardSimplexBoundary) :
    BoundarySevenRealizationHomeomorphSixSphere := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.trans standardSimplexBoundarySevenHomeomorphSixSphere⟩

/-- A final reduction of the desired homeomorphism to the sole missing face-gluing statement:
different face representatives with the same ordinary barycentric point represent the same point
of geometric realization. -/
public theorem boundarySevenRealizationHomeomorphSixSphere_of_injective
    (hinj : Function.Injective boundarySevenRealizationToBoundary) :
    BoundarySevenRealizationHomeomorphSixSphere :=
  boundarySevenRealizationHomeomorphSixSphere_of_identifiesBoundary
    (boundarySevenRealizationIdentifiesStandardSimplexBoundary_iff_injective.mpr hinj)

/-- Therefore it is enough to supply the currently absent theorem that realization preserves
injectivity for this simplicial subcomplex inclusion. -/
public theorem boundarySevenRealizationHomeomorphSixSphere_of_realizedInclusion_injective
    (hinj : Function.Injective (SSet.toTop.map
      (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι)) :
    BoundarySevenRealizationHomeomorphSixSphere :=
  boundarySevenRealizationHomeomorphSixSphere_of_injective
    (boundarySevenRealizationToBoundary_injective_iff_realizedInclusion.mpr hinj)

end SphereSixComplex
