module

public import SphereSixComplex.Topology.BoundarySevenProperFaceSubdivisionBridge
public import Mathlib.CategoryTheory.Limits.MonoCoprod

/-!
# Chain-level preliminaries for the boundary-seven generator transport

This file proves the degreewise monomorphism and cycle facts needed to transport the explicit
subdivided boundary generator through the proper-face nerve.  It deliberately contains no
normalization or affine-realization comparison.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

/-- A simplicial map which is injective in degree `n` induces a monomorphism on degree-`n`
integral simplicial chains. -/
public theorem chainComplexMap_f_mono_of_app_injective
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ)
    (hf : Function.Injective
      (f.app (Opposite.op (SimplexCategory.mk n)))) :
    Mono ((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n) := by
  change Mono (Sigma.map'
    (f := fun _ : X.obj (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ)
    (g := fun _ : Y.obj (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ)
    (f.app (Opposite.op (SimplexCategory.mk n)))
    (fun _ ↦ 𝟙 (AddCommGrpCat.of ℤ)))
  exact MonoCoprod.mono_map'_of_injective
    (fun _ : Y.obj (Opposite.op (SimplexCategory.mk n)) ↦ AddCommGrpCat.of ℤ)
    (f.app (Opposite.op (SimplexCategory.mk n))) hf

/-- The literal inclusion of proper faces into all nonempty faces is injective on simplices in
every degree. -/
public theorem boundarySevenProperFaceNerveInclusion_app_injective (n : ℕ) :
    Function.Injective
      ((boundarySevenProperFaceNerveInclusion).app
        (Opposite.op (SimplexCategory.mk n))) := by
  intro F G hFG
  refine ComposableArrows.ext (fun i ↦ ?_) (fun _ _ ↦ by subsingleton)
  have hi := congrArg (fun H ↦ H.obj i) hFG
  apply Subtype.ext
  have hi' := congrArg NonemptyFiniteChains.finset hi
  change (F.obj i).1.image ULift.up = (G.obj i).1.image ULift.up at hi'
  exact Finset.image_injective ULift.up_injective hi'

/-- The proper-face nerve inclusion is degreewise monic on integral simplicial chains. -/
public theorem boundarySevenProperFaceNerveInclusion_chainComplexMap_f_mono (n : ℕ) :
    Mono ((SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
      (AddCommGrpCat.of ℤ)).f n) :=
  chainComplexMap_f_mono_of_app_injective
    boundarySevenProperFaceNerveInclusion n
      (boundarySevenProperFaceNerveInclusion_app_injective n)

/-- Any scalar action on the explicit subdivided boundary chain pulls back to the intrinsic
proper-face fundamental chain. -/
public theorem boundarySevenProperFaceFundamentalChain_eq_zsmul_of_subdivided
    (sigma : Equiv.Perm (Fin 8)) (z : ℤ)
    (h : subdividedSevenBoundaryFundamentalChain ≫
          (SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
            (AddCommGrpCat.of ℤ)).f 6 =
        z • subdividedSevenBoundaryFundamentalChain) :
    boundarySevenProperFaceFundamentalChain ≫
        (SSet.chainComplexMap (boundarySevenProperFaceNervePermIso sigma).hom
          (AddCommGrpCat.of ℤ)).f 6 =
      z • boundarySevenProperFaceFundamentalChain := by
  let I := (SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
    (AddCommGrpCat.of ℤ)).f 6
  let P := (SSet.chainComplexMap (boundarySevenProperFaceNervePermIso sigma).hom
    (AddCommGrpCat.of ℤ)).f 6
  let Q := (SSet.chainComplexMap (simplexSubdivisionVertexPermMap sigma)
    (AddCommGrpCat.of ℤ)).f 6
  have hmap := ((SSet.chainComplexFunctor AddCommGrpCat).obj
    (AddCommGrpCat.of ℤ)).congr_map
      (boundarySevenProperFaceNerveInclusion_equivariant sigma)
  rw [Functor.map_comp, Functor.map_comp] at hmap
  have hn := congrArg (fun k ↦ k.f 6) hmap
  change P ≫ I = I ≫ Q at hn
  let _ : Mono I :=
    boundarySevenProperFaceNerveInclusion_chainComplexMap_f_mono 6
  apply (cancel_mono I).1
  calc
    (boundarySevenProperFaceFundamentalChain ≫ P) ≫ I =
        boundarySevenProperFaceFundamentalChain ≫ (P ≫ I) :=
      Category.assoc _ _ _
    _ = boundarySevenProperFaceFundamentalChain ≫ (I ≫ Q) := by rw [hn]
    _ = (boundarySevenProperFaceFundamentalChain ≫ I) ≫ Q :=
      (Category.assoc _ _ _).symm
    _ = subdividedSevenBoundaryFundamentalChain ≫ Q := by
      rw [boundarySevenProperFaceFundamentalChain_comp_inclusion]
    _ = z • subdividedSevenBoundaryFundamentalChain := h
    _ = (z • boundarySevenProperFaceFundamentalChain) ≫ I := by
      rw [Preadditive.zsmul_comp,
        boundarySevenProperFaceFundamentalChain_comp_inclusion]

/-- The intrinsic proper-face fundamental chain is a cycle. -/
public theorem boundarySevenProperFaceFundamentalChain_isCycle :
    boundarySevenProperFaceFundamentalChain ≫
        (BoundarySevenProperFaceNerve.chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 = 0 := by
  let I := SSet.chainComplexMap boundarySevenProperFaceNerveInclusion
    (AddCommGrpCat.of ℤ)
  let _ : Mono (I.f 5) :=
    boundarySevenProperFaceNerveInclusion_chainComplexMap_f_mono 5
  apply (cancel_mono (I.f 5)).1
  calc
    (boundarySevenProperFaceFundamentalChain ≫
          (BoundarySevenProperFaceNerve.chainComplex
            (AddCommGrpCat.of ℤ)).d 6 5) ≫ I.f 5 =
        boundarySevenProperFaceFundamentalChain ≫
          ((BoundarySevenProperFaceNerve.chainComplex
            (AddCommGrpCat.of ℤ)).d 6 5 ≫ I.f 5) :=
      Category.assoc _ _ _
    _ = boundarySevenProperFaceFundamentalChain ≫
        (I.f 6 ≫
          ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 7)).chainComplex
            (AddCommGrpCat.of ℤ)).d 6 5) := by
      rw [I.comm 6 5]
    _ = (boundarySevenProperFaceFundamentalChain ≫ I.f 6) ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 7)).chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 :=
      (Category.assoc _ _ _).symm
    _ = subdividedSevenBoundaryFundamentalChain ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 7)).chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 := by
      rw [boundarySevenProperFaceFundamentalChain_comp_inclusion]
    _ = 0 := subdividedSevenBoundaryFundamentalChain_isCycle
    _ = 0 ≫ I.f 5 := by simp

/-- The simplicial boundary inclusion is injective on simplices in every degree. -/
public theorem boundarySevenInclusion_app_injective (n : ℕ) :
    Function.Injective
      (((SSet.boundary 7 : SSet.Subcomplex (SSet.stdSimplex.obj
        (SimplexCategory.mk 7))).ι).app
          (Opposite.op (SimplexCategory.mk n))) :=
  Subtype.val_injective

/-- The simplicial boundary inclusion is degreewise monic on integral chains. -/
public theorem boundarySevenInclusion_chainComplexMap_f_mono (n : ℕ) :
    Mono ((SSet.chainComplexMap
      ((SSet.boundary 7 : SSet.Subcomplex (SSet.stdSimplex.obj
        (SimplexCategory.mk 7))).ι)
      (AddCommGrpCat.of ℤ)).f n) :=
  chainComplexMap_f_mono_of_app_injective
    (SSet.boundary 7 : SSet.Subcomplex
      (SSet.stdSimplex.obj (SimplexCategory.mk 7))).ι n
      (boundarySevenInclusion_app_injective n)

/-- The intrinsic alternating facet chain in `∂Δ[7]` is a cycle. -/
public theorem boundarySevenOriginalFundamentalChain_isCycle :
    boundarySevenOriginalFundamentalChain ≫
        ((∂Δ[7] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 = 0 := by
  let j := (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
  let I := SSet.chainComplexMap j (AddCommGrpCat.of ℤ)
  let _ : Mono (I.f 5) := boundarySevenInclusion_chainComplexMap_f_mono 5
  apply (cancel_mono (I.f 5)).1
  calc
    (boundarySevenOriginalFundamentalChain ≫
          ((∂Δ[7] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d 6 5) ≫ I.f 5 =
        boundarySevenOriginalFundamentalChain ≫
          (((∂Δ[7] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d 6 5 ≫ I.f 5) :=
      Category.assoc _ _ _
    _ = boundarySevenOriginalFundamentalChain ≫
        (I.f 6 ≫
          ((Δ[7] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d 6 5) := by
      rw [I.comm 6 5]
    _ = (boundarySevenOriginalFundamentalChain ≫ I.f 6) ≫
        ((Δ[7] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 :=
      (Category.assoc _ _ _).symm
    _ = standardSevenOriginalBoundaryChain ≫
        ((Δ[7] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 := by
      rw [boundarySevenOriginalFundamentalChain_comp_boundaryInclusion]
    _ = (standardSevenTopSimplexChain ≫
          ((Δ[7] : SSet.{0}).chainComplex
            (AddCommGrpCat.of ℤ)).d 7 6) ≫
        ((Δ[7] : SSet.{0}).chainComplex
          (AddCommGrpCat.of ℤ)).d 6 5 := rfl
    _ = 0 := by
      rw [Category.assoc,
        HomologicalComplex.d_comp_d, comp_zero]
    _ = 0 ≫ I.f 5 := by simp

end SphereSixComplex
