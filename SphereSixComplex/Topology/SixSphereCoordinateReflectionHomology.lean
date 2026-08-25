module

public import SphereSixComplex.Topology.SixSphereCoordinateReflectionLinear
public import SphereSixComplex.Topology.SixSphereAntipodalReflectionDegree
public import SphereSixComplex.Topology.SixSphereTopHomologyComputed
public import Mathlib.AlgebraicTopology.SimplicialSet.Subdivision
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Coordinate reflection on top homology

The barycentric subdivision of the boundary of a simplex has a permutation-equivariant model:
the nerve of the poset of its nonempty proper vertex subsets.  This file constructs that poset
model and its action by every permutation of the eight vertices.  In particular the transposition
of vertices zero and one is an honest order automorphism after subdivision and has sign `-1`.

Mathlib currently defines `SSet.sd`, and identifies subdivision of a representable simplex with
the nerve of nonempty chains, but deliberately leaves as a TODO the natural comparison from
`SSet.sd.obj X` to the nerve of the poset of nondegenerate simplices of a general `X`.  Thus it
does not yet identify `SSet.sd.obj (boundary (Delta[7]))` with the proper-face nerve below.  The
last theorem isolates the missing result as a uniform vertex-permutation degree formula plus an
equivariant boundary--sphere model; it does not assume the desired coordinate-reflection sign.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap Simplicial

namespace SphereSixComplex

/-- The vertices of the barycentric subdivision of the boundary of the seven-simplex: nonempty
proper subsets of its eight vertices, ordered by inclusion. -/
public abbrev BoundarySevenProperFace :=
  {s : Finset (Fin 8) // s.Nonempty ∧ s ≠ Finset.univ}

/-- A permutation of the eight original vertices sends proper faces to proper faces. -/
public noncomputable def boundarySevenProperFacePerm
    (sigma : Equiv.Perm (Fin 8)) (s : BoundarySevenProperFace) :
    BoundarySevenProperFace := by
  refine ⟨s.1.map sigma.toEmbedding, Finset.map_nonempty.mpr s.2.1, ?_⟩
  intro hfull
  apply s.2.2
  apply Finset.eq_univ_iff_forall.mpr
  intro i
  have hi : sigma i ∈ s.1.map sigma.toEmbedding := by
    rw [hfull]
    exact Finset.mem_univ _
  exact (Finset.mem_map' sigma.toEmbedding).mp hi

@[simp]
public theorem boundarySevenProperFacePerm_val
    (sigma : Equiv.Perm (Fin 8)) (s : BoundarySevenProperFace) :
    (boundarySevenProperFacePerm sigma s).1 = s.1.map sigma.toEmbedding :=
  rfl

@[simp]
public theorem boundarySevenProperFacePerm_mem
    (sigma : Equiv.Perm (Fin 8)) (s : BoundarySevenProperFace) (i : Fin 8) :
    i ∈ (boundarySevenProperFacePerm sigma s).1 ↔ sigma.symm i ∈ s.1 := by
  exact Finset.mem_map_equiv

/-- Permuting vertices is an order automorphism of the proper-face poset. -/
public noncomputable def boundarySevenProperFacePermOrderIso
    (sigma : Equiv.Perm (Fin 8)) :
    BoundarySevenProperFace ≃o BoundarySevenProperFace where
  toFun := boundarySevenProperFacePerm sigma
  invFun := boundarySevenProperFacePerm sigma.symm
  left_inv s := by
    apply Subtype.ext
    ext i
    simp
  right_inv s := by
    apply Subtype.ext
    ext i
    simp
  map_rel_iff' := by
    intro s t
    change s.1.map sigma.toEmbedding ⊆ t.1.map sigma.toEmbedding ↔ s.1 ⊆ t.1
    exact Finset.map_subset_map

/-- The proper-face order complex, the expected barycentric subdivision model of `boundary
(Delta[7])`. -/
public abbrev BoundarySevenProperFaceNerve : SSet.{0} :=
  PartOrd.nerveFunctor.obj (PartOrd.of BoundarySevenProperFace)

/-- Mathlib's available representable case: subdivision of the full standard seven-simplex is
the nerve of its nonempty finite chains. -/
public noncomputable def standardSevenSubdivisionNerveIso :
    SSet.sd.obj (Δ[7] : SSet.{0}) ≅
      SimplexCategory.sd.obj (SimplexCategory.mk 7) :=
  SSet.stdSimplex.sdIso.app (SimplexCategory.mk 7)

/-- The exact boundary case not presently supplied by `SSet.sd`: subdivision of the simplicial
boundary should be the order complex of nonempty proper faces.  The representable isomorphism
above does not restrict automatically because Mathlib has no general subdivision-to-
nondegenerate-simplex-poset comparison yet. -/
public def BoundarySevenSubdivisionProperFaceNerveComparison : Prop :=
  Nonempty (SSet.sd.obj (∂Δ[7] : SSet.{0}) ≅ BoundarySevenProperFaceNerve)

/-- Every vertex permutation is an honest simplicial automorphism of the proper-face nerve. -/
public noncomputable def boundarySevenProperFaceNervePermIso
    (sigma : Equiv.Perm (Fin 8)) :
    BoundarySevenProperFaceNerve ≅ BoundarySevenProperFaceNerve :=
  PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (boundarySevenProperFacePermOrderIso sigma))

/-- The transposition corresponding to an orientation-reversing simplex symmetry. -/
public def boundarySevenReflectionPermutation : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1

/-- The reflection permutation is odd. -/
public theorem boundarySevenReflectionPermutation_sign :
    Equiv.Perm.sign boundarySevenReflectionPermutation = -1 := by
  apply Equiv.Perm.sign_swap
  decide

/-- Its action on the proper-face nerve is a concrete simplicial automorphism. -/
public noncomputable def boundarySevenProperFaceNerveReflectionIso :
    BoundarySevenProperFaceNerve ≅ BoundarySevenProperFaceNerve :=
  boundarySevenProperFaceNervePermIso boundarySevenReflectionPermutation

/-- The affine action of a vertex permutation on the ordinary simplex boundary, conjugated by a
chosen boundary--sphere homeomorphism. -/
public noncomputable def boundarySevenPermutationSphereMap
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere)
    (sigma : Equiv.Perm (Fin 8)) : C(SixSphere, SixSphere) :=
  ⟨e.symm.trans ((standardSimplexBoundaryPermHomeomorph sigma).trans e),
    (e.symm.trans ((standardSimplexBoundaryPermHomeomorph sigma).trans e)).continuous⟩

/-- An equivariant boundary model identifies the vertex transposition with the analytic
coordinate reflection. -/
public def BoundarySevenReflectionEquivariant (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    Prop :=
  ∀ x : StandardSimplexBoundary 7,
    e (standardSimplexBoundaryPermHomeomorph
        boundarySevenReflectionPermutation x) =
      sixSphereCoordinateReflectionMap (e x)

/-- Use the canonical realization-to-boundary homeomorphism, a specified boundary--sphere model,
and the completed finite top-cycle orientation to transport the comparison generator to `S⁶`. -/
public noncomputable def sixSphereTopHomologyAddEquivOfStandardBoundaryComparison
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) :
    IntegralSingularHomology 6 SixSphere ≃+ ℤ :=
  sixSphereTopHomologyAddEquivOfBoundaryComparison hcomparison
    ((boundarySevenRealizationHomeomorphStandardBoundary_of_injective
      boundarySevenRealizationToBoundary_injective).trans e)
    (Classical.choice boundarySevenSimplicialTopHomologyOrientation)

/-- The uniform comparison theorem that barycentric subdivision is expected to supply: every
vertex permutation acts on the transported top generator by its ordinary permutation sign.
Unlike the desired reflection assertion, this statement is formulated for the explicit affine
action of every permutation and records the missing equivariant simplicial--singular naturality. -/
public def BoundarySevenVertexPermutationDegreeFormula
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) : Prop :=
  ∀ sigma : Equiv.Perm (Fin 8),
    sixSphereHomologicalDegree
        (sixSphereTopHomologyAddEquivOfStandardBoundaryComparison hcomparison e)
        (boundarySevenPermutationSphereMap e sigma) =
      ((Equiv.Perm.sign sigma : ℤˣ) : ℤ)

/-- On an infinite-cyclic top homology group, degree `-1` for any self-map forces its induced
endomorphism to be literal negation. -/
public theorem sixSphereTopIntegralHomologyMap_eq_neg_of_degree_eq_neg_one
    (orientation : IntegralSingularHomology 6 SixSphere ≃+ ℤ)
    (f : C(SixSphere, SixSphere))
    (hdegree : sixSphereHomologicalDegree orientation f = -1) :
    sixSphereTopIntegralHomologyMap f =
      -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere) := by
  let H := IntegralSingularHomology 6 SixSphere
  let fH : H →+ H := sixSphereTopIntegralHomologyMap f
  let fZ : ℤ →+ ℤ := orientation.toAddMonoidHom.comp
    (fH.comp orientation.symm.toAddMonoidHom)
  have hf (z : ℤ) : orientation (fH (orientation.symm z)) = -z := by
    change fZ z = -z
    rw [intAddHom_apply_eq_mul_apply_one]
    change z * sixSphereHomologicalDegree orientation f = -z
    rw [hdegree]
    simp
  apply AddMonoidHom.ext
  intro x
  apply orientation.injective
  have hx := hf (orientation x)
  rw [orientation.symm_apply_apply] at hx
  simpa using hx

/-- The strongest current reduction.  The canonical integral comparison may be supplied as an
explicit hypothesis.  A permutation-equivariant subdivision comparison and an equivariant
boundary model then force coordinate reflection to induce `-id` on `H₆`; no reflection sign is
assumed. -/
public theorem sixSphereCoordinateReflection_homology_of_boundarySubdivision
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere)
    (hequivariant : BoundarySevenReflectionEquivariant e)
    (hpermutations : BoundarySevenVertexPermutationDegreeFormula hcomparison e) :
    sixSphereTopIntegralHomologyMap sixSphereCoordinateReflectionMap =
      -AddMonoidHom.id (IntegralSingularHomology 6 SixSphere) := by
  let orientation :=
    sixSphereTopHomologyAddEquivOfStandardBoundaryComparison hcomparison e
  have hreflectionMap : boundarySevenPermutationSphereMap e
      boundarySevenReflectionPermutation = sixSphereCoordinateReflectionMap := by
    apply ContinuousMap.ext
    intro x
    change e (standardSimplexBoundaryPermHomeomorph
      boundarySevenReflectionPermutation (e.symm x)) = _
    rw [hequivariant (e.symm x), e.apply_symm_apply]
  apply sixSphereTopIntegralHomologyMap_eq_neg_of_degree_eq_neg_one orientation
  rw [← hreflectionMap]
  rw [hpermutations boundarySevenReflectionPermutation,
    boundarySevenReflectionPermutation_sign]
  rfl

end SphereSixComplex
