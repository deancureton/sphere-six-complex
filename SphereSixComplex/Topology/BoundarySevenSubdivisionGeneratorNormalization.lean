module

public import SphereSixComplex.Topology.BoundarySevenSubdivisionGeneratorComparison

/-!
# Normalization of the boundary-seven fundamental generator

This file identifies the concrete unnormalized top simplex with the generator selected by
the normalized-chain colimit used in the top-homology orientation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The unique unnormalized top simplex maps to the inverse of the canonical normalized
degree-seven orientation isomorphism. -/
public theorem standardSevenTopSimplexChain_toNormalized :
    standardSevenTopSimplexChain ≫
        ((Δ[7] : SSet.{0}).toNormalizedChainComplex
          (AddCommGrpCat.of ℤ)).f 7 =
      standardSevenNormalizedChainsXSevenIsoInt.inv := by
  rw [standardSevenTopSimplexChain,
    SSet.ιChainComplex_toNormalizedChainComplex_f]
  let top : (Δ[7] : SSet.{0}).nonDegenerate 7 :=
    ⟨SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 7)),
      SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate 7⟩
  let _ : Unique ((Δ[7] : SSet.{0}).nonDegenerate 7) :=
    { default := top
      uniq := fun x ↦ by
        apply Subtype.ext
        have hx := x.2
        have hx' : x.1 ∈
            ({SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 7))} :
              Set ((Δ[7] : SSet.{0}).obj
                (Opposite.op (SimplexCategory.mk 7)))) := by
          rw [← SSet.stdSimplex.nonDegenerate_top_dim]
          exact hx
        simpa [top] using hx' }
  let P := (Δ[7] : SSet.{0}).isColimitCofanNormalizedChainComplex
    (AddCommGrpCat.of ℤ) 7
  let Q := Cofan.isColimitMkOfUnique (Iso.refl (AddCommGrpCat.of ℤ))
    ((Δ[7] : SSet.{0}).nonDegenerate 7)
  have h := IsColimit.comp_coconePointUniqueUpToIso_inv P Q
    (Discrete.mk (default : (Δ[7] : SSet.{0}).nonDegenerate 7))
  change (Δ[7] : SSet.{0}).ιNormalizedChainComplex
      (standardSimplexTopSimplex 7) =
    (P.coconePointUniqueUpToIso Q).inv
  have hdefault :
      (default : (Δ[7] : SSet.{0}).nonDegenerate 7).1 =
        standardSimplexTopSimplex 7 := by
    rfl
  rw [← hdefault]
  simpa [P, Q] using h.symm

/-- The exactness isomorphism from the unique normalized seven-simplex to degree-six cycles
includes as the normalized top differential. -/
@[reassoc]
public theorem standardSevenNormalizedChainsXSevenIsoTopCycles_hom_ι :
    standardSevenNormalizedChainsXSevenIsoTopCycles.hom ≫
        kernel.ι (StandardSevenNormalizedIntegralChains.d 6 5) =
      StandardSevenNormalizedIntegralChains.d 7 6 := by
  let _ : Mono (StandardSevenNormalizedIntegralChains.d 7 6) :=
    standardSeven_normalized_d_seven_six_mono
  have h₆ := standardSeven_normalizedChains_exactAt 6 (by omega)
  have h₆' : (StandardSevenNormalizedIntegralChains.sc' 7 6 5).Exact :=
    ShortComplex.exact_of_iso
      (StandardSevenNormalizedIntegralChains.isoSc' 7 6 5 (by simp) (by simp)) h₆
  let _ : Mono (StandardSevenNormalizedIntegralChains.sc' 7 6 5).f := by
    change Mono (StandardSevenNormalizedIntegralChains.d 7 6)
    exact standardSeven_normalized_d_seven_six_mono
  change (IsLimit.conePointUniqueUpToIso h₆'.fIsKernel
      (limit.isLimit (parallelPair
        (StandardSevenNormalizedIntegralChains.d 6 5) 0))).hom ≫
      limit.π (parallelPair (StandardSevenNormalizedIntegralChains.d 6 5) 0)
        WalkingParallelPair.zero =
    StandardSevenNormalizedIntegralChains.d 7 6
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

set_option backward.isDefEq.respectTransparency false in
/-- The canonical cycle-kernel comparison commutes with the inclusions into normalized
degree six. -/
@[reassoc]
theorem boundarySevenTopCyclesIsoStandardSevenTopCycles_hom_ι :
    boundarySevenTopCyclesIsoStandardSevenTopCycles.hom ≫
        kernel.ι (StandardSevenNormalizedIntegralChains.d 6 5) =
      kernel.ι (BoundarySevenNormalizedIntegralChains.d 6 5) ≫
        (SSet.normalizedChainComplexMap
          (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
          (AddCommGrpCat.of ℤ)).f 6 := by
  let f := SSet.normalizedChainComplexMap
    (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
      (AddCommGrpCat.of ℤ)
  let φ := (HomologicalComplex.shortComplexFunctor' AddCommGrpCat
    (ComplexShape.down ℕ) 7 6 5).map f
  change (((BoundarySevenNormalizedIntegralChains.sc' 7 6 5).cyclesIsoKernel).inv ≫
      ShortComplex.cyclesMap φ ≫
      ((StandardSevenNormalizedIntegralChains.sc' 7 6 5).cyclesIsoKernel).hom) ≫
        kernel.ι (StandardSevenNormalizedIntegralChains.d 6 5) =
    kernel.ι (BoundarySevenNormalizedIntegralChains.d 6 5) ≫ f.f 6
  have hB :
      ((StandardSevenNormalizedIntegralChains.sc' 7 6 5).cyclesIsoKernel).hom ≫
          kernel.ι (StandardSevenNormalizedIntegralChains.d 6 5) =
        (StandardSevenNormalizedIntegralChains.sc' 7 6 5).iCycles := by
    apply kernel.lift_ι
  have hmap := ShortComplex.cyclesMap_i φ
  have hmap' :
      ShortComplex.cyclesMap φ ≫
          (StandardSevenNormalizedIntegralChains.sc' 7 6 5).iCycles =
        (BoundarySevenNormalizedIntegralChains.sc' 7 6 5).iCycles ≫ f.f 6 := by
    exact hmap
  have hA :
      ((BoundarySevenNormalizedIntegralChains.sc' 7 6 5).cyclesIsoKernel).inv ≫
          (BoundarySevenNormalizedIntegralChains.sc' 7 6 5).iCycles =
        kernel.ι (BoundarySevenNormalizedIntegralChains.d 6 5) := by
    apply ShortComplex.liftCycles_i
  simp only [Category.assoc]
  rw [hB, hmap']
  rw [← Category.assoc, hA]

/-- Transporting the standard cycle kernel back to the boundary and then including the
boundary normalized chains is the standard kernel inclusion. -/
@[reassoc]
public theorem boundarySevenTopCyclesIsoStandardSevenTopCycles_inv_ι :
    boundarySevenTopCyclesIsoStandardSevenTopCycles.inv ≫
        kernel.ι (BoundarySevenNormalizedIntegralChains.d 6 5) ≫
        (SSet.normalizedChainComplexMap
          (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
          (AddCommGrpCat.of ℤ)).f 6 =
      kernel.ι (StandardSevenNormalizedIntegralChains.d 6 5) := by
  rw [← cancel_epi boundarySevenTopCyclesIsoStandardSevenTopCycles.hom]
  simp only [Iso.hom_inv_id_assoc,
    boundarySevenTopCyclesIsoStandardSevenTopCycles_hom_ι]

/-- The ordinary boundary of the unique seven-simplex normalizes to the boundary of its
canonical normalized generator. -/
public theorem standardSevenOriginalBoundaryChain_toNormalized :
    standardSevenOriginalBoundaryChain ≫
        ((Δ[7] : SSet.{0}).toNormalizedChainComplex
          (AddCommGrpCat.of ℤ)).f 6 =
      standardSevenNormalizedChainsXSevenIsoInt.inv ≫
        StandardSevenNormalizedIntegralChains.d 7 6 := by
  let F := (Δ[7] : SSet.{0}).toNormalizedChainComplex
    (AddCommGrpCat.of ℤ)
  change (standardSevenTopSimplexChain ≫ _) ≫ F.f 6 = _
  rw [Category.assoc, ← F.comm 7 6, ← Category.assoc,
    standardSevenTopSimplexChain_toNormalized]

/-- The intrinsic alternating boundary chain normalizes to the canonical generator used by
the degree-six orientation of `∂Δ[7]`. -/
public theorem boundarySevenOriginalFundamentalChain_toNormalized :
    boundarySevenOriginalFundamentalChain ≫
        ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
          (AddCommGrpCat.of ℤ)).f 6 =
      boundarySevenNormalizedOrientationGenerator ≫
        kernel.ι (BoundarySevenNormalizedIntegralChains.d 6 5) := by
  let j := (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
  let g := SSet.normalizedChainComplexMap j (AddCommGrpCat.of ℤ)
  let e₆ := boundarySevenNormalizedChainsXIsoStandard 6 (by omega)
  let _ : IsIso (g.f 6) := by
    change IsIso e₆.hom
    infer_instance
  rw [← cancel_mono (g.f 6)]
  have hnat := congrArg (fun k ↦ k.f 6)
    (SSet.toNormalizedChainComplex_normalizedChainComplexMap
      (f := j) (R := AddCommGrpCat.of ℤ))
  calc
    (boundarySevenOriginalFundamentalChain ≫
          ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
            (AddCommGrpCat.of ℤ)).f 6) ≫ g.f 6 =
        boundarySevenOriginalFundamentalChain ≫
          (((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
              (AddCommGrpCat.of ℤ)).f 6 ≫ g.f 6) :=
      Category.assoc _ _ _
    _ = boundarySevenOriginalFundamentalChain ≫
          ((SSet.chainComplexMap j (AddCommGrpCat.of ℤ)).f 6 ≫
            ((Δ[7] : SSet.{0}).toNormalizedChainComplex
              (AddCommGrpCat.of ℤ)).f 6) := by
      exact congrArg (fun k ↦ boundarySevenOriginalFundamentalChain ≫ k) hnat
    _ = (boundarySevenOriginalFundamentalChain ≫
          (SSet.chainComplexMap j (AddCommGrpCat.of ℤ)).f 6) ≫
            ((Δ[7] : SSet.{0}).toNormalizedChainComplex
              (AddCommGrpCat.of ℤ)).f 6 :=
      (Category.assoc _ _ _).symm
    _ = standardSevenOriginalBoundaryChain ≫
          ((Δ[7] : SSet.{0}).toNormalizedChainComplex
            (AddCommGrpCat.of ℤ)).f 6 := by
      rw [boundarySevenOriginalFundamentalChain_comp_boundaryInclusion]
    _ = standardSevenNormalizedChainsXSevenIsoInt.inv ≫
          StandardSevenNormalizedIntegralChains.d 7 6 :=
      standardSevenOriginalBoundaryChain_toNormalized
    _ = standardSevenNormalizedChainsXSevenIsoInt.inv ≫
          standardSevenNormalizedChainsXSevenIsoTopCycles.hom ≫
            kernel.ι (StandardSevenNormalizedIntegralChains.d 6 5) := by
      rw [standardSevenNormalizedChainsXSevenIsoTopCycles_hom_ι]
    _ = (boundarySevenNormalizedOrientationGenerator ≫
          kernel.ι (BoundarySevenNormalizedIntegralChains.d 6 5)) ≫
            g.f 6 := by
      rw [boundarySevenNormalizedOrientationGenerator]
      have h := congrArg
        (fun k ↦ standardSevenNormalizedChainsXSevenIsoInt.inv ≫
          standardSevenNormalizedChainsXSevenIsoTopCycles.hom ≫ k)
        boundarySevenTopCyclesIsoStandardSevenTopCycles_inv_ι.symm
      simpa only [Category.assoc] using h

end SphereSixComplex
