module

public import SphereSixComplex.Topology.BoundarySevenReflectionDegreeFromSubdivision
public import SphereSixComplex.Topology.SingularAffineSubdivision

/-!
# Affine realization of the proper-face nerve

Every vertex of the proper-face nerve is sent to the barycenter of the corresponding face of
the standard seven-simplex.  On a flag of faces we extend affinely.  Because all faces in a flag
are contained in its largest (proper) face, this affine simplex lands in the ordinary boundary.
The resulting compatible family of singular simplices gives a canonical continuous map from the
geometric realization of the proper-face nerve to the standard simplex boundary.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap Opposite PartialOrder Set Simplicial

namespace SphereSixComplex

/-- The barycenter of a proper face, regarded as a point of the ambient standard simplex. -/
public noncomputable def boundarySevenProperFaceBarycenter
    (s : BoundarySevenProperFace) : stdSimplex ℝ (Fin 8) :=
  nonemptyFiniteChainBarycenter
    (boundarySevenProperFaceToNonemptyFiniteChain s)

@[simp]
public theorem boundarySevenProperFaceBarycenter_apply
    (s : BoundarySevenProperFace) (i : Fin 8) :
    boundarySevenProperFaceBarycenter s i =
      if i ∈ s.1 then (s.1.card : ℝ)⁻¹ else 0 := by
  rw [boundarySevenProperFaceBarycenter,
    nonemptyFiniteChainBarycenter_apply]
  have hcard : (s.1.image ULift.up).card = s.1.card :=
    Finset.card_image_of_injective s.1 ULift.up_injective
  have hcardReal : ((s.1.image ULift.up).card : ℝ) = (s.1.card : ℝ) :=
    congrArg Nat.cast hcard
  simp only [boundarySevenProperFaceToNonemptyFiniteChain,
    Finset.mem_image, ULift.up_inj, exists_eq_right]
  rw [hcardReal]

/-- Barycenters of proper faces are natural under every permutation of the eight vertices. -/
public theorem boundarySevenProperFaceBarycenter_permute
    (sigma : Equiv.Perm (Fin 8)) (s : BoundarySevenProperFace) :
    boundarySevenProperFaceBarycenter
        (boundarySevenProperFacePerm sigma s) =
      stdSimplex.map sigma (boundarySevenProperFaceBarycenter s) := by
  ext i
  rw [boundarySevenProperFaceBarycenter_apply,
    stdSimplex_map_equiv_apply,
    boundarySevenProperFaceBarycenter_apply]
  have hcard : (s.1.map sigma.toEmbedding).card = s.1.card :=
    Finset.card_map sigma.toEmbedding
  simp [boundarySevenProperFacePerm, hcard]

/-- The affine vertex-permutation homeomorphism of the ordinary boundary as a morphism in
`TopCat`. -/
public noncomputable def standardSimplexBoundaryPermTopMap
    (sigma : Equiv.Perm (Fin 8)) :
    TopCat.of (StandardSimplexBoundary 7) ⟶
      TopCat.of (StandardSimplexBoundary 7) :=
  TopCat.ofHom
    ⟨standardSimplexBoundaryPermHomeomorph sigma,
      (standardSimplexBoundaryPermHomeomorph sigma).continuous⟩

/-- The affine extension of the face barycenters along a flag, with codomain the ambient
standard simplex. -/
public noncomputable def boundarySevenProperFaceAffineFlagAmbientMap
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k) :
    C(stdSimplex ℝ (Fin (k + 1)), stdSimplex ℝ (Fin 8)) :=
  ⟨stdSimplexAffineCombination
      (fun j ↦ boundarySevenProperFaceBarycenter (F.obj j)),
    continuous_stdSimplexAffineCombination _⟩

/-- Every affine flag simplex is supported in its largest proper face and therefore lands in
the boundary. -/
public theorem boundarySevenProperFaceAffineFlagAmbientMap_mem_boundary
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) :
    ∃ i, boundarySevenProperFaceAffineFlagAmbientMap k F w i = 0 := by
  have hproper := (F.obj (Fin.last k)).2.2
  have hex : ∃ i, i ∉ (F.obj (Fin.last k)).1 := by
    by_contra h
    apply hproper
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  change (∑ j, w j * boundarySevenProperFaceBarycenter (F.obj j) i) = 0
  apply Finset.sum_eq_zero
  intro j hj
  have hjle : F.obj j ≤ F.obj (Fin.last k) :=
    leOfHom (F.map (homOfLE (Fin.le_last j)))
  have hij : i ∉ (F.obj j).1 := fun hij ↦ hi (hjle hij)
  rw [boundarySevenProperFaceBarycenter_apply, if_neg hij, mul_zero]

/-- The affine flag simplex, intrinsically valued in the ordinary simplex boundary. -/
public noncomputable def boundarySevenProperFaceAffineFlagMap
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k) :
    C(stdSimplex ℝ (Fin (k + 1)), StandardSimplexBoundary 7) :=
  ⟨fun w ↦ ⟨boundarySevenProperFaceAffineFlagAmbientMap k F w,
      boundarySevenProperFaceAffineFlagAmbientMap_mem_boundary k F w⟩,
    (boundarySevenProperFaceAffineFlagAmbientMap k F).continuous.subtype_mk _⟩

@[simp]
public theorem boundarySevenProperFaceAffineFlagMap_val
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k)
    (w : stdSimplex ℝ (Fin (k + 1))) :
    (boundarySevenProperFaceAffineFlagMap k F w : stdSimplex ℝ (Fin 8)) =
      boundarySevenProperFaceAffineFlagAmbientMap k F w :=
  rfl

/-- Restricting a flag along a simplex-category morphism agrees with restricting its affine
simplex along the corresponding affine map. -/
public theorem boundarySevenProperFaceAffineFlagMap_naturality
    {n m : SimplexCategory} (f : n ⟶ m)
    (F : ComposableArrows BoundarySevenProperFace m.len) :
    boundarySevenProperFaceAffineFlagMap n.len
        (F.whiskerLeft (SimplexCategory.toCat.map f).toFunctor) =
      (boundarySevenProperFaceAffineFlagMap m.len F).comp
        ⟨stdSimplex.map f, by continuity⟩ := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  change stdSimplexAffineCombination
      (fun j ↦ boundarySevenProperFaceBarycenter
        ((F.whiskerLeft (SimplexCategory.toCat.map f).toFunctor).obj j)) w =
    stdSimplexAffineCombination
      (fun j ↦ boundarySevenProperFaceBarycenter (F.obj j))
        (stdSimplex.map f w)
  rw [stdSimplexAffineCombination_map]
  rfl

/-- Affine realization of flags commutes with every permutation of the original vertices. -/
public theorem boundarySevenProperFaceAffineFlagMap_permute
    (sigma : Equiv.Perm (Fin 8)) (k : ℕ)
    (F : ComposableArrows BoundarySevenProperFace k) :
    boundarySevenProperFaceAffineFlagMap k
        ((boundarySevenProperFaceNervePermIso sigma).hom.app
          (Opposite.op (SimplexCategory.mk k)) F) =
      (⟨standardSimplexBoundaryPermHomeomorph sigma,
        (standardSimplexBoundaryPermHomeomorph sigma).continuous⟩ :
          C(StandardSimplexBoundary 7, StandardSimplexBoundary 7)).comp
          (boundarySevenProperFaceAffineFlagMap k F) := by
  apply ContinuousMap.ext
  intro w
  apply Subtype.ext
  change stdSimplexAffineCombination
      (fun j ↦ boundarySevenProperFaceBarycenter
        (boundarySevenProperFacePerm sigma (F.obj j))) w =
    stdSimplex.map sigma
      (stdSimplexAffineCombination
        (fun j ↦ boundarySevenProperFaceBarycenter (F.obj j)) w)
  rw [stdSimplex_map_affineCombination]
  apply congrArg (fun p ↦ stdSimplexAffineCombination p w)
  funext j
  exact boundarySevenProperFaceBarycenter_permute sigma (F.obj j)

/-- A flag of proper faces as a singular simplex of the ordinary boundary. -/
public noncomputable def boundarySevenProperFaceAffineSingularSimplex
    (k : ℕ) (F : ComposableArrows BoundarySevenProperFace k) :
    (TopCat.toSSet.obj (TopCat.of (StandardSimplexBoundary 7))).obj
      (Opposite.op (SimplexCategory.mk k)) :=
  (TopCat.toSSetObjEquiv _ _).symm
    (boundarySevenProperFaceAffineFlagMap k F)

/-- The affine flag construction is a morphism from the proper-face nerve to the singular
simplicial set of the ordinary boundary. -/
public noncomputable def boundarySevenProperFaceAffineSingularMap :
    BoundarySevenProperFaceNerve ⟶
      TopCat.toSSet.obj (TopCat.of (StandardSimplexBoundary 7)) where
  app n := ↾fun F ↦ boundarySevenProperFaceAffineSingularSimplex n.unop.len F
  naturality n m f := by
    ext F
    apply (TopCat.toSSetObjEquiv _ _).injective
    exact boundarySevenProperFaceAffineFlagMap_naturality f.unop F

/-- The affine singular map is equivariant for every vertex permutation. -/
public theorem boundarySevenProperFaceAffineSingularMap_equivariant
    (sigma : Equiv.Perm (Fin 8)) :
    (boundarySevenProperFaceNervePermIso sigma).hom ≫
        boundarySevenProperFaceAffineSingularMap =
      boundarySevenProperFaceAffineSingularMap ≫
        TopCat.toSSet.map (standardSimplexBoundaryPermTopMap sigma) := by
  ext n F
  apply (TopCat.toSSetObjEquiv _ _).injective
  exact boundarySevenProperFaceAffineFlagMap_permute sigma n.unop.len F

/-- The continuous affine-barycentric realization map, obtained from the compatible singular
simplices by the geometric-realization/singular-set adjunction. -/
public noncomputable def boundarySevenProperFaceRealizationMap :
    SSet.toTop.obj BoundarySevenProperFaceNerve ⟶
      TopCat.of (StandardSimplexBoundary 7) :=
  (sSetTopAdj.homEquiv BoundarySevenProperFaceNerve
    (TopCat.of (StandardSimplexBoundary 7))).symm
      boundarySevenProperFaceAffineSingularMap

/-- By construction, the adjoint of the affine realization map is the explicit affine singular
map on flags. -/
public theorem boundarySevenProperFaceRealizationMap_adjunct :
    sSetTopAdj.unit.app BoundarySevenProperFaceNerve ≫
        TopCat.toSSet.map boundarySevenProperFaceRealizationMap =
      boundarySevenProperFaceAffineSingularMap := by
  change (sSetTopAdj.homEquiv BoundarySevenProperFaceNerve
      (TopCat.of (StandardSimplexBoundary 7)))
        boundarySevenProperFaceRealizationMap =
    boundarySevenProperFaceAffineSingularMap
  exact Equiv.apply_symm_apply _ boundarySevenProperFaceAffineSingularMap

/-- The same adjunction identity in `homEquiv` form. -/
public theorem boundarySevenProperFaceRealizationMap_homEquiv :
    (sSetTopAdj.homEquiv BoundarySevenProperFaceNerve
      (TopCat.of (StandardSimplexBoundary 7)))
        boundarySevenProperFaceRealizationMap =
      boundarySevenProperFaceAffineSingularMap :=
  Equiv.apply_symm_apply _ boundarySevenProperFaceAffineSingularMap

/-- The canonical simplicial-to-singular comparison followed by the singular chain map of the
affine realization is exactly the explicit affine flag chain map. -/
public theorem boundarySevenProperFaceCanonicalComparison_comp_realizationChainMap :
    simplicialToRealizationSingularChainMap BoundarySevenProperFaceNerve
        (AddCommGrpCat.of ℤ) ≫
      SSet.chainComplexMap
        (TopCat.toSSet.map boundarySevenProperFaceRealizationMap)
        (AddCommGrpCat.of ℤ) =
    SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
      (AddCommGrpCat.of ℤ) := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have h := F.congr_map boundarySevenProperFaceRealizationMap_adjunct
  rw [Functor.map_comp] at h
  exact h

/-- The intrinsic proper-face fundamental chain transported by the canonical comparison and
the realization map is the explicit affine singular fundamental chain. -/
public theorem boundarySevenProperFaceFundamentalChain_comparison_realization :
    (boundarySevenProperFaceFundamentalChain ≫
      (simplicialToRealizationSingularChainMap BoundarySevenProperFaceNerve
        (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map boundarySevenProperFaceRealizationMap)
          (AddCommGrpCat.of ℤ)).f 6 =
      boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
          (AddCommGrpCat.of ℤ)).f 6 := by
  simp only [Category.assoc]
  have h := congrArg (fun f ↦ f.f 6)
    boundarySevenProperFaceCanonicalComparison_comp_realizationChainMap
  change
    (simplicialToRealizationSingularChainMap BoundarySevenProperFaceNerve
      (AddCommGrpCat.of ℤ)).f 6 ≫
        (SSet.chainComplexMap
          (TopCat.toSSet.map boundarySevenProperFaceRealizationMap)
          (AddCommGrpCat.of ℤ)).f 6 =
      (SSet.chainComplexMap boundarySevenProperFaceAffineSingularMap
        (AddCommGrpCat.of ℤ)).f 6 at h
  rw [h]

/-- The remaining point-set statement needed to promote the explicit affine realization map to
a homeomorphism.  It contains no chain-level or equivariance condition. -/
public def BoundarySevenProperFaceAffineRealizationHomeomorphismInput : Prop :=
  IsCompact (Set.univ : Set
      (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) ∧
    Function.Bijective boundarySevenProperFaceRealizationMap

/-- Compactness of the finite order-complex realization and bijectivity of the affine map promote
it to the desired explicit homeomorphism. -/
public noncomputable def boundarySevenProperFaceRealizationHomeomorph_of_input
    (h : BoundarySevenProperFaceAffineRealizationHomeomorphismInput) :
    (SSet.toTop.obj BoundarySevenProperFaceNerve : Type) ≃ₜ
      StandardSimplexBoundary 7 := by
  letI : CompactSpace (SSet.toTop.obj BoundarySevenProperFaceNerve : Type) :=
    isCompact_univ_iff.mp h.1
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective boundarySevenProperFaceRealizationMap h.2)
    boundarySevenProperFaceRealizationMap.hom.continuous

@[simp]
public theorem boundarySevenProperFaceRealizationHomeomorph_of_input_apply
    (h : BoundarySevenProperFaceAffineRealizationHomeomorphismInput)
    (x : (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) :
    boundarySevenProperFaceRealizationHomeomorph_of_input h x =
      boundarySevenProperFaceRealizationMap x :=
  rfl

/-- The continuous affine realization map is equivariant for every vertex permutation. -/
public theorem boundarySevenProperFaceRealizationMap_equivariant
    (sigma : Equiv.Perm (Fin 8)) :
    SSet.toTop.map (boundarySevenProperFaceNervePermIso sigma).hom ≫
        boundarySevenProperFaceRealizationMap =
      boundarySevenProperFaceRealizationMap ≫
        standardSimplexBoundaryPermTopMap sigma := by
  apply (sSetTopAdj.homEquiv BoundarySevenProperFaceNerve
    (TopCat.of (StandardSimplexBoundary 7))).injective
  rw [sSetTopAdj.homEquiv_naturality_left,
    sSetTopAdj.homEquiv_naturality_right,
    boundarySevenProperFaceRealizationMap_homEquiv]
  exact boundarySevenProperFaceAffineSingularMap_equivariant sigma

/-- In particular the affine realization intertwines the proper-face transposition with the
explicit affine reflection of the ordinary simplex boundary. -/
public theorem boundarySevenProperFaceRealizationMap_reflection_equivariant :
    SSet.toTop.map boundarySevenProperFaceNerveReflectionIso.hom ≫
        boundarySevenProperFaceRealizationMap =
      boundarySevenProperFaceRealizationMap ≫
        standardSimplexBoundaryPermTopMap boundarySevenReflectionPermutation := by
  exact boundarySevenProperFaceRealizationMap_equivariant
    boundarySevenReflectionPermutation

/-- Once the sole point-set triangulation input is supplied, the resulting explicit
homeomorphism is equivariant for every vertex permutation. -/
public theorem boundarySevenProperFaceRealizationHomeomorph_of_input_equivariant
    (h : BoundarySevenProperFaceAffineRealizationHomeomorphismInput)
    (sigma : Equiv.Perm (Fin 8))
    (x : (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) :
    boundarySevenProperFaceRealizationHomeomorph_of_input h
        (SSet.toTop.map (boundarySevenProperFaceNervePermIso sigma).hom x) =
      standardSimplexBoundaryPermHomeomorph sigma
        (boundarySevenProperFaceRealizationHomeomorph_of_input h x) := by
  change boundarySevenProperFaceRealizationMap
      (SSet.toTop.map (boundarySevenProperFaceNervePermIso sigma).hom x) =
    standardSimplexBoundaryPermHomeomorph sigma
      (boundarySevenProperFaceRealizationMap x)
  exact ConcreteCategory.congr_hom
    (boundarySevenProperFaceRealizationMap_equivariant sigma) x

/-- Reflection equivariance of the conditional explicit homeomorphism. -/
public theorem
    boundarySevenProperFaceRealizationHomeomorph_of_input_reflection_equivariant
    (h : BoundarySevenProperFaceAffineRealizationHomeomorphismInput)
    (x : (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) :
    boundarySevenProperFaceRealizationHomeomorph_of_input h
        (SSet.toTop.map boundarySevenProperFaceNerveReflectionIso.hom x) =
      standardSimplexBoundaryPermHomeomorph boundarySevenReflectionPermutation
        (boundarySevenProperFaceRealizationHomeomorph_of_input h x) :=
  boundarySevenProperFaceRealizationHomeomorph_of_input_equivariant h
    boundarySevenReflectionPermutation x

end SphereSixComplex
