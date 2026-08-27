module

public import SphereSixComplex.Topology.WangHomologyPresentationProof

/-!
# Wang presentations for bundles over finite bouquets

The algebra of four consecutive maps in a Wang long exact sequence, the explicit finite-bouquet
mapping torus and the structure `FiniteBouquetMappingTorusWangSequence` are defined in
`WangHomologyPresentationDefs`, and are re-exported here, so every module path using them is
unchanged.

The Wang exact sequence of the finite-bouquet mapping torus is no longer assumed.  It is
constructed in `WangHomologyPresentationProof` as
`finiteBouquetMappingTorusWangSequenceOfCover`, from the Mayer--Vietoris sequence of the explicit
vertex/edge open cover of the mapping torus, with its boundary exposed as the corresponding leg
of that Mayer--Vietoris boundary.

This file assembles the two presentations built from it, `finiteBouquetMappingTorusWangPresentation`
and `circleMappingTorusWangPresentation`, under the names used throughout the development.  In
particular, any four consecutive exact maps in a Wang sequence give a short exact presentation of
the middle group as an extension of monodromy coinvariants by monodromy invariants.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex

section FiniteBouquet

variable {ι F : Type}
  [Fintype ι] [Inhabited ι] [TopologicalSpace ι] [DiscreteTopology ι] [TopologicalSpace F]

/-- The general algebraic Wang presentation supplied by the constructed topological theorem. -/
public def finiteBouquetMappingTorusWangPresentation (φ : ι → F ≃ₜ F) (k : ℕ) :
    WangHomologyPresentation
      (ι → IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) (FiniteBouquetMappingTorus φ))
      (ι → IntegralSingularHomology k F)
      (IntegralSingularHomology k F) :=
  let W := finiteBouquetMappingTorusWangSequenceOfCover φ k
  { highDifference := finiteBouquetMonodromyDifference φ (k + 1)
    inclusion := integralSingularHomologyMap (k + 1)
      (finiteBouquetMappingTorusFiberInclusion φ)
    boundary := W.boundary
    lowDifference := finiteBouquetMonodromyDifference φ k
    exact_highDifference_inclusion := W.exact_highDifference_inclusion
    exact_inclusion_boundary := W.exact_inclusion_boundary
    exact_boundary_lowDifference := W.exact_boundary_lowDifference }

/-- The degree-one homology presentation, using the induced maps on `H₁` and `H₀`. -/
public abbrev finiteBouquetMappingTorusHOnePresentation (φ : ι → F ≃ₜ F) :=
  finiteBouquetMappingTorusWangPresentation φ 0

/-- The degree-two homology presentation, using the induced maps on `H₂` and `H₁`. -/
public abbrev finiteBouquetMappingTorusHTwoPresentation (φ : ι → F ≃ₜ F) :=
  finiteBouquetMappingTorusWangPresentation φ 1

end FiniteBouquet

section Circle

variable {F : Type} [TopologicalSpace F]

/-- The circle Wang sequence, derived from the constructed finite-bouquet Wang sequence. -/
public def circleMappingTorusWangPresentation (φ : F ≃ₜ F) (k : ℕ) :
    WangHomologyPresentation
      (IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) F)
      (IntegralSingularHomology (k + 1) (CircleMappingTorus φ))
      (IntegralSingularHomology k F)
      (IntegralSingularHomology k F) :=
  circleMappingTorusWangPresentationOfCover φ k

/-- The degree-one circle-bundle presentation from the induced `H₁` and `H₀` monodromies. -/
public abbrev circleMappingTorusHOnePresentation (φ : F ≃ₜ F) :=
  circleMappingTorusWangPresentation φ 0

/-- The degree-two circle-bundle presentation from the induced `H₂` and `H₁` monodromies. -/
public abbrev circleMappingTorusHTwoPresentation (φ : F ≃ₜ F) :=
  circleMappingTorusWangPresentation φ 1

end Circle

end SphereSixComplex
