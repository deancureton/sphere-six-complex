module

public import SphereSixComplex.Topology.BoundarySevenReflectionDegreeFromSubdivision
public import SphereSixComplex.Topology.SimplicialSixSphereTopHomologyKernel
public import SphereSixComplex.Topology.SingularSubdivisionIteration
public import SphereSixComplex.Topology.SimplicialSingularComparison

/-!
# The boundary-seven generator and barycentric subdivision

This file records the algebraic part of the comparison between the generator used in the
normalized-chain computation of `H₆(∂Δ[7]; ℤ)` and the explicit maximal-flag chain in the
barycentric subdivision.  No geometric proper-face realization is used here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The chain represented by the unique top simplex of the standard seven-simplex. -/
public noncomputable def standardSevenTopSimplexChain :
    AddCommGrpCat.of ℤ ⟶
      ((Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).X 7 :=
  (Δ[7] : SSet.{0}).ιChainComplex (standardSimplexTopSimplex 7)

/-- Its ordinary simplicial boundary.  This is the unnormalized representative of the
generator from which `standardSevenTopCyclesIsoInt`, and hence the boundary orientation, is
constructed. -/
public noncomputable def standardSevenOriginalBoundaryChain :
    AddCommGrpCat.of ℤ ⟶
      ((Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).X 6 :=
  standardSevenTopSimplexChain ≫
    ((Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).d 7 6

/-- The same alternating boundary, formed intrinsically in `∂Δ[7]` from its eight facet
inclusions. -/
public noncomputable def boundarySevenOriginalFundamentalChain :
    AddCommGrpCat.of ℤ ⟶
      ((∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)).X 6 :=
  ∑ i : Fin 8, (-1 : ℤ) ^ i.val •
    ((Δ[6] : SSet.{0}).ιChainComplex (standardSimplexTopSimplex 6) ≫
      (SSet.chainComplexMap (SSet.boundary.ι i)
        (AddCommGrpCat.of ℤ)).f 6)

/-- The intrinsic alternating-face chain becomes the ordinary boundary of the unique
seven-simplex after applying the boundary inclusion. -/
public theorem boundarySevenOriginalFundamentalChain_comp_boundaryInclusion :
    boundarySevenOriginalFundamentalChain ≫
        (SSet.chainComplexMap
          ((SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι)
          (AddCommGrpCat.of ℤ)).f 6 =
      standardSevenOriginalBoundaryChain := by
  rw [boundarySevenOriginalFundamentalChain, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [standardSevenOriginalBoundaryChain, standardSevenTopSimplexChain,
    SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hcomp := congrArg (fun k ↦ k.f 6)
    (F.map_comp (SSet.boundary.ι i)
      ((SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι))
  have hface := congrArg
    (fun f ↦ f.app (Opposite.op (SimplexCategory.mk 6))
      (standardSimplexTopSimplex 6))
    (yonedaEquiv_symm_standardSimplexTopSimplex_delta 6 i)
  calc
    _ = (Δ[6] : SSet.{0}).ιChainComplex (standardSimplexTopSimplex 6) ≫
        (F.map (SSet.boundary.ι i ≫
          (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι)).f 6 := by
      exact congrArg
        (fun k ↦ (Δ[6] : SSet.{0}).ιChainComplex
          (standardSimplexTopSimplex 6) ≫ k) hcomp.symm
    _ = (Δ[6] : SSet.{0}).ιChainComplex (standardSimplexTopSimplex 6) ≫
        (F.map (SSet.stdSimplex.δ i)).f 6 := by rw [SSet.boundary.ι_ι]
    _ = _ := by
      rw [SSet.ι_chainComplexMap_f]
      congr 1

/-- Canonical barycentric subdivision sends the universal top simplex to the transported
maximal-flag fundamental chain. -/
public theorem standardSevenTopSimplexChain_barycentricSubdivision :
    standardSevenTopSimplexChain ≫
        (barycentricSubdivisionChainMapCanonical (Δ[7] : SSet.{0})).f 7 =
      subdividedStandardSimplexFundamentalChain 7 := by
  rw [standardSevenTopSimplexChain,
    barycentricSubdivisionChainMapCanonical_f,
    iota_barycentricSubdivisionComponent]
  unfold barycentricSubdivisionSimplexChain
  have hid : SSet.yonedaEquiv.symm (standardSimplexTopSimplex 7) =
      𝟙 (Δ[7] : SSet.{0}) := by
    apply SSet.yonedaEquiv.injective
    change standardSimplexTopSimplex 7 = SSet.yonedaEquiv (𝟙 (Δ[7] : SSet.{0}))
    rfl
  rw [hid]
  simp

/-- Subdivision carries the original boundary of the unique seven-simplex to the boundary of
the explicit maximal-flag chain in Mathlib's left-Kan-extension model of `sd Δ[7]`. -/
public theorem standardSevenOriginalBoundaryChain_barycentricSubdivision :
    standardSevenOriginalBoundaryChain ≫
        (barycentricSubdivisionChainMapCanonical (Δ[7] : SSet.{0})).f 6 =
      subdividedSevenBoundaryFundamentalChain ≫
        (SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 7))
          (AddCommGrpCat.of ℤ)).f 6 := by
  let F := barycentricSubdivisionChainMapCanonical (Δ[7] : SSet.{0})
  let G := SSet.chainComplexMap
    (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 7))
    (AddCommGrpCat.of ℤ)
  change (standardSevenTopSimplexChain ≫ _) ≫ F.f 6 =
    (subdividedSimplexFundamentalChain 7 ≫ _) ≫ G.f 6
  rw [Category.assoc, ← F.comm 7 6, ← Category.assoc,
    standardSevenTopSimplexChain_barycentricSubdivision]
  change (subdividedSimplexFundamentalChain 7 ≫ G.f 7) ≫ _ = _
  have hcomm := G.comm 7 6
  rw [Category.assoc]
  exact congrArg (fun k ↦ subdividedSimplexFundamentalChain 7 ≫ k) hcomm

/-- The intrinsic boundary chain has the promised explicit subdivision after including
`sd (∂Δ[7])` into `sd Δ[7]`.  Thus no subcomplex-realization theorem is needed for the
chain-level generator comparison. -/
public theorem boundarySevenOriginalFundamentalChain_barycentricSubdivision_comp_inclusion :
    (boundarySevenOriginalFundamentalChain ≫
        (barycentricSubdivisionChainMapCanonical (∂Δ[7] : SSet.{0})).f 6) ≫
      (SSet.chainComplexMap
        (SSet.sd.map
          ((SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι))
        (AddCommGrpCat.of ℤ)).f 6 =
      subdividedSevenBoundaryFundamentalChain ≫
        (SSet.chainComplexMap
          (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 7))
          (AddCommGrpCat.of ℤ)).f 6 := by
  let j := (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
  have hnat := congrArg (fun k ↦ k.f 6)
    (barycentricSubdivisionChainMapCanonical_naturality j)
  calc
    _ = boundarySevenOriginalFundamentalChain ≫
        ((barycentricSubdivisionChainMapCanonical (∂Δ[7] : SSet.{0})).f 6 ≫
          (SSet.chainComplexMap (SSet.sd.map j)
            (AddCommGrpCat.of ℤ)).f 6) := Category.assoc _ _ _
    _ = boundarySevenOriginalFundamentalChain ≫
        ((SSet.chainComplexMap j (AddCommGrpCat.of ℤ)).f 6 ≫
          (barycentricSubdivisionChainMapCanonical (Δ[7] : SSet.{0})).f 6) := by
      exact congrArg (fun k ↦ boundarySevenOriginalFundamentalChain ≫ k) hnat.symm
    _ = (boundarySevenOriginalFundamentalChain ≫
          (SSet.chainComplexMap j (AddCommGrpCat.of ℤ)).f 6) ≫
        (barycentricSubdivisionChainMapCanonical (Δ[7] : SSet.{0})).f 6 :=
      (Category.assoc _ _ _).symm
    _ = standardSevenOriginalBoundaryChain ≫
        (barycentricSubdivisionChainMapCanonical (Δ[7] : SSet.{0})).f 6 := by
      rw [boundarySevenOriginalFundamentalChain_comp_boundaryInclusion]
    _ = _ := standardSevenOriginalBoundaryChain_barycentricSubdivision

/-- The generator actually used by `boundarySevenNormalizedTopCyclesOrientation`: first take
the generator of the unique normalized seven-simplex, apply its boundary (the exactness
isomorphism), then transport that cycle back from `Δ[7]` to `∂Δ[7]`. -/
public noncomputable def boundarySevenNormalizedOrientationGenerator :
    AddCommGrpCat.of ℤ ⟶
      kernel (BoundarySevenNormalizedIntegralChains.d 6 5) :=
  standardSevenNormalizedChainsXSevenIsoInt.inv ≫
    standardSevenNormalizedChainsXSevenIsoTopCycles.hom ≫
      boundarySevenTopCyclesIsoStandardSevenTopCycles.inv

/-- The preceding map is precisely the inverse of the top-cycle orientation equivalence used
in the proof of `boundarySevenSimplicialTopHomologyOrientation`. -/
public theorem boundarySevenNormalizedOrientationGenerator_eq_orientation_inv :
    boundarySevenNormalizedOrientationGenerator =
      (boundarySevenTopCyclesIsoStandardSevenTopCycles ≪≫
        standardSevenTopCyclesIsoInt).inv := by
  rfl

/-- Barycentric subdivision followed by the maximum-last-vertex map induces the identity on
integral homology, in every degree. -/
public theorem barycentricSubdivision_lastVertex_homologyMap
    (X : SSet.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap
        (barycentricSubdivisionChainMapCanonical X) n ≫
      HomologicalComplex.homologyMap (subdivisionLastVertexChainMap X) n =
        𝟙 ((X.chainComplex (AddCommGrpCat.of ℤ)).homology n) := by
  rw [← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap (barycentricSubdivisionEndomorphism X) n = _
  simpa [barycentricSubdivisionEndomorphismIterate] using
    barycentricSubdivisionEndomorphismIterate_homologyMap X 1 n

/-- The canonical simplicial-to-realization-singular comparison is natural. -/
public theorem simplicialToRealizationSingularChainMap_naturality
    {K L : SSet.{0}} (f : K ⟶ L) (R : AddCommGrpCat) :
    SSet.chainComplexMap f R ≫ simplicialToRealizationSingularChainMap L R =
      simplicialToRealizationSingularChainMap K R ≫
        SSet.chainComplexMap
          (TopCat.toSSet.map (SSet.toTop.map f)) R := by
  unfold simplicialToRealizationSingularChainMap
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact (SSet.chainComplexFunctor AddCommGrpCat).obj R |>.congr_map
    (sSetTopAdj.unit.naturality f)

/-- The exact remaining geometric assertion after the algebraic comparison in this file.  It
is deliberately kept equal to the previously isolated transport proposition: what remains is
to show that realization followed by the chosen radial sphere equivalence takes this generator
to degree `+1`. -/
public def BoundarySevenSubdivisionGeneratorGeometricCompatibility
    (hcomparison : SimplicialToSingularComparisonQuasiIsomorphism
      (∂Δ[7] : SSet.{0}) (AddCommGrpCat.of ℤ))
    (e : StandardSimplexBoundary 7 ≃ₜ SixSphere) : Prop :=
  BoundarySevenSubdivisionGeneratorDegreeTransport hcomparison e

end SphereSixComplex
