module

public import SphereSixComplex.Topology.BoundarySevenProperFaceRealizationBijective
public import SphereSixComplex.Topology.BoundarySevenStrictFlagCommonRestrictionProof
public import SphereSixComplex.Topology.BoundarySevenFlagRealizationCommonFace

/-!
# Global injectivity of the proper-face affine realization

Nondegenerate flag simplices cover the realization.  Equal affine images of two such
representatives have a common positive-face restriction, and functoriality of geometric
realization identifies the two representatives.
-/

@[expose] public section

noncomputable section

open CategoryTheory Opposite PartialOrder Simplicial

namespace SphereSixComplex

/-- The affine realization of the proper-face nerve is globally injective. -/
public theorem boundarySevenProperFaceRealizationMap_injective :
    Function.Injective boundarySevenProperFaceRealizationMap := by
  intro x y hxy
  obtain ⟨s, xs, hxs⟩ :=
    boundarySevenProperFaceRealization_nondegenerateFlagCovered x
  obtain ⟨t, yt, hyt⟩ :=
    boundarySevenProperFaceRealization_nondegenerateFlagCovered y
  let w : stdSimplex ℝ (Fin (s.dim + 1)) :=
    SimplexCategory.toTopHomeo (SimplexCategory.mk s.dim) xs
  let v : stdSimplex ℝ (Fin (t.dim + 1)) :=
    SimplexCategory.toTopHomeo (SimplexCategory.mk t.dim) yt
  have hw : (SimplexCategory.toTopHomeo (SimplexCategory.mk s.dim)).symm w = xs :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk s.dim)).symm_apply_apply xs
  have hv : (SimplexCategory.toTopHomeo (SimplexCategory.mk t.dim)).symm v = yt :=
    (SimplexCategory.toTopHomeo (SimplexCategory.mk t.dim)).symm_apply_apply yt
  have hF : StrictMono s.simplex.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.simplex).mp s.2
  have hG : StrictMono t.simplex.obj :=
    (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono t.simplex).mp t.2
  have haffine :
      boundarySevenProperFaceAffineFlagMap s.dim s.simplex w =
        boundarySevenProperFaceAffineFlagMap t.dim t.simplex v := by
    calc
      boundarySevenProperFaceAffineFlagMap s.dim s.simplex w =
          boundarySevenProperFaceRealizationMap
            (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
              ((SimplexCategory.toTopHomeo
                (SimplexCategory.mk s.dim)).symm w)) :=
        (boundarySevenProperFaceRealizationMap_flag s.dim s.simplex w).symm
      _ = boundarySevenProperFaceRealizationMap
            (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex) xs) := by rw [hw]
      _ = boundarySevenProperFaceRealizationMap x := congrArg
        boundarySevenProperFaceRealizationMap hxs
      _ = boundarySevenProperFaceRealizationMap y := hxy
      _ = boundarySevenProperFaceRealizationMap
            (SSet.toTop.map (SSet.yonedaEquiv.symm t.simplex) yt) :=
        congrArg boundarySevenProperFaceRealizationMap hyt.symm
      _ = boundarySevenProperFaceRealizationMap
            (SSet.toTop.map (SSet.yonedaEquiv.symm t.simplex)
              ((SimplexCategory.toTopHomeo
                (SimplexCategory.mk t.dim)).symm v)) := by rw [hv]
      _ = boundarySevenProperFaceAffineFlagMap t.dim t.simplex v :=
        boundarySevenProperFaceRealizationMap_flag t.dim t.simplex v
  obtain ⟨r, f, g, u, hfu, hgu, hflags⟩ :=
    boundarySevenStrictFlagCommonRestriction
      s.dim t.dim s.simplex t.simplex w v hF hG haffine
  have hrepresentatives := boundarySevenFlagRealization_eq_of_commonRestriction
    s.simplex t.simplex f g hflags u
  rw [hfu, hgu, hw, hv] at hrepresentatives
  exact hxs.symm.trans (hrepresentatives.trans hyt)

/-- The affine realization of the proper-face nerve is bijective. -/
public theorem boundarySevenProperFaceRealizationMap_bijective :
    Function.Bijective boundarySevenProperFaceRealizationMap :=
  ⟨boundarySevenProperFaceRealizationMap_injective,
    boundarySevenProperFaceRealizationMap_surjective⟩

/-- The compactness-and-bijectivity input for the affine realization homeomorphism is proved
without additional assumptions. -/
public theorem boundarySevenProperFaceAffineRealizationHomeomorphismInput_proof :
    BoundarySevenProperFaceAffineRealizationHomeomorphismInput :=
  ⟨boundarySevenProperFaceRealization_isCompact,
    boundarySevenProperFaceRealizationMap_bijective⟩

/-- The unconditional affine barycentric homeomorphism from the proper-face realization to the
ordinary boundary of the seven-simplex. -/
public noncomputable def boundarySevenProperFaceRealizationHomeomorph :
    (SSet.toTop.obj BoundarySevenProperFaceNerve : Type) ≃ₜ
      StandardSimplexBoundary 7 :=
  boundarySevenProperFaceRealizationHomeomorph_of_input
    boundarySevenProperFaceAffineRealizationHomeomorphismInput_proof

@[simp]
public theorem boundarySevenProperFaceRealizationHomeomorph_apply
    (x : (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) :
    boundarySevenProperFaceRealizationHomeomorph x =
      boundarySevenProperFaceRealizationMap x :=
  rfl

/-- The unconditional affine barycentric homeomorphism is equivariant for every permutation of
the eight vertices. -/
public theorem boundarySevenProperFaceRealizationHomeomorph_equivariant
    (sigma : Equiv.Perm (Fin 8))
    (x : (SSet.toTop.obj BoundarySevenProperFaceNerve : Type)) :
    boundarySevenProperFaceRealizationHomeomorph
        (SSet.toTop.map (boundarySevenProperFaceNervePermIso sigma).hom x) =
      standardSimplexBoundaryPermHomeomorph sigma
        (boundarySevenProperFaceRealizationHomeomorph x) :=
  boundarySevenProperFaceRealizationHomeomorph_of_input_equivariant
    boundarySevenProperFaceAffineRealizationHomeomorphismInput_proof sigma x

end SphereSixComplex
