module

public import SphereSixComplex.Topology.SubdivisionVertexPermutationFundamentalChain
public import SphereSixComplex.Topology.BoundarySevenReflectionEquivariantModel

/-!
# The reflection sign on the subdivided boundary fundamental chain

The boundary of the signed maximal-flag fundamental chain of the subdivided seven-simplex is
an explicit degree-six cycle supported on its proper faces.  This file proves, without any
topological comparison assumption, that reindexing the eight vertices acts on that boundary
chain by the ordinary permutation sign.  In particular the transposition of vertices zero and
one negates it.

The final definitions isolate only the remaining transport statement: that this explicit
subdivided boundary cycle represents the already selected generator used by the canonical
simplicial-to-singular comparison.  Once that naturality statement is supplied, the equivariant
radial homeomorphism turns the chain calculation into degree `-1` and literal negation on
`H₆(S⁶; ℤ)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap PartialOrder Simplicial

namespace SphereSixComplex

/-- The explicit boundary fundamental chain in the nonempty-face nerve model of the
barycentrically subdivided seven-simplex. -/
public noncomputable def subdividedSevenBoundaryFundamentalChain :
    AddCommGrpCat.of ℤ ⟶
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 7)).chainComplex
        (AddCommGrpCat.of ℤ)).X 6 :=
  subdividedSimplexFundamentalChain 7 ≫
    ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 7)).chainComplex
      (AddCommGrpCat.of ℤ)).d 7 6

/-- Every vertex permutation acts on the explicit subdivided boundary fundamental chain by its
ordinary sign.  This is the boundary restriction of the top-dimensional maximal-flag formula. -/
public theorem subdividedSevenBoundaryFundamentalChain_vertexPerm
    (sigma : Equiv.Perm (Fin 8)) :
    subdividedSevenBoundaryFundamentalChain ≫
        (SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
          (AddCommGrpCat.of ℤ)).f 6 =
      permutationSignInteger sigma • subdividedSevenBoundaryFundamentalChain := by
  let F := SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
    (AddCommGrpCat.of ℤ)
  change (subdividedSimplexFundamentalChain 7 ≫ _) ≫ F.f 6 = _
  rw [Category.assoc]
  rw [← F.comm 7 6]
  rw [← Category.assoc, subdividedSimplexFundamentalChain_vertexPerm]
  simp only [Preadditive.zsmul_comp]
  rfl

/-- The vertex transposition `(0 1)` negates the explicit subdivided boundary fundamental
chain. -/
public theorem subdividedSevenBoundaryFundamentalChain_reflection :
    subdividedSevenBoundaryFundamentalChain ≫
        (SSet.chainComplexMap
          (simplexSubdivisionVertexPermMap boundarySevenReflectionPermutation)
          (AddCommGrpCat.of ℤ)).f 6 =
      -subdividedSevenBoundaryFundamentalChain := by
  rw [subdividedSevenBoundaryFundamentalChain_vertexPerm,
    permutationSignInteger, boundarySevenReflectionPermutation_sign]
  norm_num

/-- The explicit boundary fundamental chain is a cycle. -/
public theorem subdividedSevenBoundaryFundamentalChain_isCycle :
    subdividedSevenBoundaryFundamentalChain ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 7)).chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 = 0 := by
  change (subdividedSimplexFundamentalChain 7 ≫ _) ≫ _ = 0
  rw [Category.assoc]
  simp

/-- The boundary chain is exactly the alternating sum of the subdivided codimension-one faces.
In particular this identifies the chain-level restriction to the proper faces of the
seven-simplex, without appealing to a general subdivision-of-a-subcomplex theorem. -/
public theorem subdividedSevenBoundaryFundamentalChain_eq_alternatingProperFaces :
    subdividedSevenBoundaryFundamentalChain =
      subdividedSimplexAlternatingFaceChain 6 := by
  exact barycentricFundamentalBoundaryIdentity 6

/-- Regard a nonempty subset of the vertices of a facet as a proper face of the ambient
seven-simplex. -/
public noncomputable def subdividedFacetToBoundarySevenProperFace
    (p : Fin 8)
    (s : NonemptyFiniteChains (ULift.{0} (Fin 7))) :
    BoundarySevenProperFace := by
  let t : Finset (Fin 8) :=
    s.finset.image (fun i ↦ p.succAbove i.down)
  refine ⟨t, Finset.image_nonempty.mpr s.nonempty, ?_⟩
  intro ht
  have hp : p ∈ t := by rw [ht]; simp
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hp
  exact (Fin.succAbove_ne p i.down) hi

@[simp]
public theorem subdividedFacetToBoundarySevenProperFace_val
    (p : Fin 8)
    (s : NonemptyFiniteChains (ULift.{0} (Fin 7))) :
    (subdividedFacetToBoundarySevenProperFace p s).1 =
      s.finset.image (fun i ↦ p.succAbove i.down) :=
  rfl

/-- The monotone facet-to-proper-face map underlying the subdivision restriction. -/
public noncomputable def subdividedFacetToBoundarySevenProperFaceHom
    (p : Fin 8) :
    PartOrd.of (NonemptyFiniteChains (ULift.{0} (Fin 7))) ⟶
      PartOrd.of BoundarySevenProperFace :=
  PartOrd.ofHom
    { toFun := subdividedFacetToBoundarySevenProperFace p
      monotone' := by
        intro s t hst
        change s.finset.image (fun i ↦ p.succAbove i.down) ⊆
          t.finset.image (fun i ↦ p.succAbove i.down)
        exact Finset.image_mono _ hst }

/-- Include the proper-face poset into the full nonempty-face poset. -/
public noncomputable def boundarySevenProperFaceToNonemptyFiniteChain
    (s : BoundarySevenProperFace) :
    NonemptyFiniteChains (ULift.{0} (Fin 8)) where
  finset := s.1.image ULift.up
  nonempty := Finset.image_nonempty.mpr s.2.1
  comparable := fun _ _ ↦ le_total _ _

/-- The monotone inclusion of proper faces into all nonempty faces. -/
public noncomputable def boundarySevenProperFaceInclusionHom :
    PartOrd.of BoundarySevenProperFace ⟶
      PartOrd.of (NonemptyFiniteChains (ULift.{0} (Fin 8))) :=
  PartOrd.ofHom
    { toFun := boundarySevenProperFaceToNonemptyFiniteChain
      monotone' := by
        intro s t hst
        change s.1.image ULift.up ⊆ t.1.image ULift.up
        exact Finset.image_mono _ hst }

/-- A subdivided facet maps into the proper-face nerve. -/
public noncomputable def subdividedFacetToBoundarySevenProperFaceNerveMap
    (p : Fin 8) :
    SimplexCategory.sd.{0}.obj (SimplexCategory.mk 6) ⟶
      BoundarySevenProperFaceNerve :=
  PartOrd.nerveFunctor.map (subdividedFacetToBoundarySevenProperFaceHom p)

/-- The simplicial inclusion of the proper-face nerve into the full subdivision nerve. -/
public noncomputable def boundarySevenProperFaceNerveInclusion :
    BoundarySevenProperFaceNerve ⟶
      SimplexCategory.sd.{0}.obj (SimplexCategory.mk 7) :=
  PartOrd.nerveFunctor.map boundarySevenProperFaceInclusionHom

/-- Reindexing proper faces and then including them agrees with first including them and then
reindexing all nonempty faces. -/
public theorem boundarySevenProperFacePerm_comp_inclusionHom
    (sigma : Equiv.Perm (Fin 8)) :
    (PartOrd.Iso.mk (boundarySevenProperFacePermOrderIso sigma)).hom ≫
        boundarySevenProperFaceInclusionHom =
      boundarySevenProperFaceInclusionHom ≫
        (PartOrd.Iso.mk
          (nonemptyFiniteChainsVertexPermOrderIso sigma)).hom := by
  apply PartOrd.ext
  intro s
  apply NonemptyFiniteChains.ext
  ext i
  rcases i with ⟨i⟩
  simp [boundarySevenProperFaceInclusionHom,
    boundarySevenProperFaceToNonemptyFiniteChain,
    boundarySevenProperFacePermOrderIso,
    boundarySevenProperFacePerm,
    nonemptyFiniteChainsVertexPermOrderIso,
    nonemptyFiniteChainsVertexPerm]
  constructor
  · intro hi
    exact ⟨sigma.symm i, hi, sigma.apply_symm_apply i⟩
  · rintro ⟨a, ha, hai⟩
    have haeq : a = sigma.symm i := by
      apply sigma.injective
      simpa using hai
    simpa [haeq] using ha

/-- The proper-face nerve inclusion is equivariant for every vertex permutation. -/
public theorem boundarySevenProperFaceNerveInclusion_equivariant
    (sigma : Equiv.Perm (Fin 8)) :
    (boundarySevenProperFaceNervePermIso sigma).hom ≫
        boundarySevenProperFaceNerveInclusion =
      boundarySevenProperFaceNerveInclusion ≫
        simplexSubdivisionVertexPermMap sigma := by
  change
    PartOrd.nerveFunctor.map
        (PartOrd.Iso.mk (boundarySevenProperFacePermOrderIso sigma)).hom ≫
      PartOrd.nerveFunctor.map boundarySevenProperFaceInclusionHom =
    PartOrd.nerveFunctor.map boundarySevenProperFaceInclusionHom ≫
      PartOrd.nerveFunctor.map
        (PartOrd.Iso.mk
          (nonemptyFiniteChainsVertexPermOrderIso sigma)).hom
  rw [← Functor.map_comp, ← Functor.map_comp,
    boundarySevenProperFacePerm_comp_inclusionHom]

/-- Facet inclusion followed by the proper-face inclusion is the usual subdivision of the
monotone face map. -/
public theorem subdividedFacetToBoundarySevenProperFaceNerveMap_comp_inclusion
    (p : Fin 8) :
    subdividedFacetToBoundarySevenProperFaceNerveMap p ≫
        boundarySevenProperFaceNerveInclusion =
      SimplexCategory.sd.{0}.map (SimplexCategory.δ p) := by
  change PartOrd.nerveFunctor.map (subdividedFacetToBoundarySevenProperFaceHom p) ≫
      PartOrd.nerveFunctor.map boundarySevenProperFaceInclusionHom =
    PartOrd.nerveFunctor.map
      (PartOrd.nonemptyFiniteChainsFunctor.map
        (SimplexCategory.toPartOrd.map (SimplexCategory.δ p)))
  rw [← Functor.map_comp]
  apply congrArg PartOrd.nerveFunctor.map
  apply PartOrd.ext
  intro s
  have hface (j : ULift.{0} (Fin 7)) :
      (SimplexCategory.toPartOrd.map (SimplexCategory.δ p)).hom j =
        ULift.up (p.succAbove j.down) := by
    rcases j with ⟨j⟩
    rfl
  apply NonemptyFiniteChains.ext
  ext i
  rcases i with ⟨i⟩
  simp [subdividedFacetToBoundarySevenProperFaceHom,
    boundarySevenProperFaceInclusionHom,
    boundarySevenProperFaceToNonemptyFiniteChain,
    subdividedFacetToBoundarySevenProperFace,
    PartOrd.nonemptyFiniteChainsFunctor,
    NonemptyFiniteChains.map]
  constructor
  · rintro ⟨x, hx, hxi⟩
    refine ⟨x, hx, ?_⟩
    subst i
    rfl
  · rintro ⟨x, hx, hxi⟩
    refine ⟨x, hx, ?_⟩
    exact congrArg ULift.down hxi

/-- The boundary fundamental chain written intrinsically in the proper-face nerve. -/
public noncomputable def boundarySevenProperFaceFundamentalChain :
    AddCommGrpCat.of ℤ ⟶
      (BoundarySevenProperFaceNerve.chainComplex (AddCommGrpCat.of ℤ)).X 6 :=
  ∑ p : Fin 8, (-1 : ℤ) ^ p.val •
    (subdividedSimplexFundamentalChain 6 ≫
      (SSet.chainComplexMap
        (subdividedFacetToBoundarySevenProperFaceNerveMap p)
        (AddCommGrpCat.of ℤ)).f 6)

/-- Inclusion of the intrinsic proper-face fundamental chain is the explicit boundary of the
subdivided seven-simplex. -/
public theorem boundarySevenProperFaceFundamentalChain_comp_inclusion :
    boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 =
      subdividedSevenBoundaryFundamentalChain := by
  rw [subdividedSevenBoundaryFundamentalChain_eq_alternatingProperFaces,
    boundarySevenProperFaceFundamentalChain,
    subdividedSimplexAlternatingFaceChain, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Preadditive.zsmul_comp, Category.assoc]
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hmap := F.congr_map
    (subdividedFacetToBoundarySevenProperFaceNerveMap_comp_inclusion p)
  rw [Functor.map_comp] at hmap
  have hn := congrArg (fun k ↦ k.f 6) hmap
  change
    (SSet.chainComplexMap (subdividedFacetToBoundarySevenProperFaceNerveMap p)
      (AddCommGrpCat.of ℤ)).f 6 ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 =
      (SSet.chainComplexMap (SimplexCategory.sd.map (SimplexCategory.δ p))
        (AddCommGrpCat.of ℤ)).f 6 at hn
  rw [hn]

/-- The intrinsic proper-face fundamental chain has the expected permutation action after the
literal proper-face inclusion.  Thus no support or face-restriction compatibility remains in
the degree calculation. -/
public theorem boundarySevenProperFaceFundamentalChain_vertexPerm_after_inclusion
    (sigma : Equiv.Perm (Fin 8)) :
    (boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap (boundarySevenProperFaceNervePermIso sigma).hom
          (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 =
      (permutationSignInteger sigma •
        boundarySevenProperFaceFundamentalChain) ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 := by
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hmap := F.congr_map
    (boundarySevenProperFaceNerveInclusion_equivariant sigma)
  rw [Functor.map_comp, Functor.map_comp] at hmap
  have hn := congrArg (fun k ↦ k.f 6) hmap
  change
    (SSet.chainComplexMap (boundarySevenProperFaceNervePermIso sigma).hom
      (AddCommGrpCat.of ℤ)).f 6 ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 =
      (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
        (AddCommGrpCat.of ℤ)).f 6 ≫
        (SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
          (AddCommGrpCat.of ℤ)).f 6 at hn
  calc
    _ = (boundarySevenProperFaceFundamentalChain ≫
          (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
            (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
          (AddCommGrpCat.of ℤ)).f 6 := by
      simp only [Category.assoc]
      rw [hn]
    _ = subdividedSevenBoundaryFundamentalChain ≫
        (SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
          (AddCommGrpCat.of ℤ)).f 6 := by
      rw [boundarySevenProperFaceFundamentalChain_comp_inclusion]
    _ = permutationSignInteger sigma •
        subdividedSevenBoundaryFundamentalChain :=
      subdividedSevenBoundaryFundamentalChain_vertexPerm sigma
    _ = _ := by
      rw [Preadditive.zsmul_comp,
        boundarySevenProperFaceFundamentalChain_comp_inclusion]

/-- For the reflection, the intrinsic proper-face fundamental chain is negated after inclusion
in the full subdivision nerve. -/
public theorem boundarySevenProperFaceFundamentalChain_reflection_after_inclusion :
    (boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveReflectionIso.hom
          (AddCommGrpCat.of ℤ)).f 6) ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 =
      (-boundarySevenProperFaceFundamentalChain) ≫
        (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
          (AddCommGrpCat.of ℤ)).f 6 := by
  simpa [boundarySevenProperFaceNerveReflectionIso, permutationSignInteger,
    boundarySevenReflectionPermutation_sign] using
    boundarySevenProperFaceFundamentalChain_vertexPerm_after_inclusion
      boundarySevenReflectionPermutation

/-- Exact remaining bridge from the unconditional subdivision calculation to the degree
formula used by the project.  It asks only that the chosen comparison orientation transport the
explicit signed subdivided boundary generator with the permutation action computed above. -/
public def BoundarySevenSubdivisionGeneratorDegreeTransport
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) : Prop :=
  ∀ (sigma : Equiv.Perm (Fin 8)) (z : ℤ),
    subdividedSevenBoundaryFundamentalChain ≫
        (SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
          (AddCommGrpCat.of ℤ)).f 6 =
      z • subdividedSevenBoundaryFundamentalChain →
    sixSphereHomologicalDegree
        (sixSphereTopHomologyAddEquivOfStandardBoundaryComparison hcomparison e)
        (boundarySevenPermutationSphereMap e sigma) = z

/-- The subdivision-generator transport statement is exactly strong enough to discharge the
uniform vertex-permutation degree formula; the sign conversion is purely algebraic. -/
public theorem boundarySevenVertexPermutationDegreeFormula_of_subdivisionGeneratorTransport
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere)
    (htransport : BoundarySevenSubdivisionGeneratorDegreeTransport hcomparison e) :
    BoundarySevenVertexPermutationDegreeFormula hcomparison e := by
  intro sigma
  rw [htransport sigma (permutationSignInteger sigma)
    (subdividedSevenBoundaryFundamentalChain_vertexPerm sigma)]
  rfl

/-- For the explicit reflection-equivariant radial model, the remaining generator-transport
statement implies that coordinate reflection has homological degree `-1`. -/
public theorem sixSphereCoordinateReflection_degree_neg_one_of_subdivisionGeneratorTransport
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (htransport : BoundarySevenSubdivisionGeneratorDegreeTransport hcomparison
      boundarySevenReflectionEquivariantHomeomorph) :
    sixSphereHomologicalDegree
        (sixSphereTopHomologyAddEquivOfStandardBoundaryComparison hcomparison
          boundarySevenReflectionEquivariantHomeomorph)
        sixSphereCoordinateReflectionMap = -1 := by
  let e := boundarySevenReflectionEquivariantHomeomorph
  have hreflectionMap : boundarySevenPermutationSphereMap e
      boundarySevenReflectionPermutation = sixSphereCoordinateReflectionMap := by
    apply ContinuousMap.ext
    intro x
    change e (standardSimplexBoundaryPermHomeomorph
      boundarySevenReflectionPermutation (e.symm x)) = _
    rw [boundarySevenReflectionEquivariantHomeomorph_equivariant (e.symm x),
      e.apply_symm_apply]
  rw [← hreflectionMap]
  exact htransport boundarySevenReflectionPermutation (-1)
    (by simpa using subdividedSevenBoundaryFundamentalChain_reflection)

/-- Consequently, the same exact transport statement makes coordinate reflection literal
negation on top integral homology. -/
public theorem sixSphereCoordinateReflection_homology_negation_of_subdivisionGeneratorTransport
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (htransport : BoundarySevenSubdivisionGeneratorDegreeTransport hcomparison
      boundarySevenReflectionEquivariantHomeomorph) :
    sixSphereTopIntegralHomologyMap sixSphereCoordinateReflectionMap =
      -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere) := by
  apply sixSphereTopIntegralHomologyMap_eq_neg_of_degree_eq_neg_one
    (sixSphereTopHomologyAddEquivOfStandardBoundaryComparison hcomparison
      boundarySevenReflectionEquivariantHomeomorph)
  exact sixSphereCoordinateReflection_degree_neg_one_of_subdivisionGeneratorTransport
    hcomparison htransport

end SphereSixComplex
