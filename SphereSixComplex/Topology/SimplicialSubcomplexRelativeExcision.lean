module

public import SphereSixComplex.Topology.BinaryOpenCoverChains
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SphereSixComplex

public theorem simplicialSubcomplexUnionSquare {X : SSet} (U V : X.Subcomplex) :
    SSet.Subcomplex.BicartSq (U ⊓ V) U V (U ⊔ V) where
  inf_eq := rfl
  sup_eq := rfl

public theorem simplicialSubcomplexChainUnionSquare {X : SSet} (U V : X.Subcomplex) :
    IsPushout
      (BinaryOpenCover.integralSimplicialChains.map
        (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₁₂))
      (BinaryOpenCover.integralSimplicialChains.map
        (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₁₃))
      (BinaryOpenCover.integralSimplicialChains.map
        (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₂₄))
      (BinaryOpenCover.integralSimplicialChains.map
        (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₃₄)) :=
  (simplicialSubcomplexUnionSquare U V).isPushout.map BinaryOpenCover.integralSimplicialChains

public def simplicialSubcomplexRelativeExcisionMap {X : SSet} (U V : X.Subcomplex) :=
  cokernel.map
    (BinaryOpenCover.integralSimplicialChains.map
      (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₁₂))
    (BinaryOpenCover.integralSimplicialChains.map
      (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₃₄))
    (BinaryOpenCover.integralSimplicialChains.map
      (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₁₃))
    (BinaryOpenCover.integralSimplicialChains.map
      (SSet.Subcomplex.homOfLE (simplicialSubcomplexUnionSquare U V).le₂₄))
    (simplicialSubcomplexChainUnionSquare U V).w

public instance simplicialSubcomplexRelativeExcisionMap_isIso {X : SSet} (U V : X.Subcomplex) :
    IsIso (simplicialSubcomplexRelativeExcisionMap U V) :=
  isIso_cokernel_map_of_isPushout (simplicialSubcomplexChainUnionSquare U V)

public def simplicialSubcomplexRelativeExcisionIso {X : SSet} (U V : X.Subcomplex) :=
  asIso (simplicialSubcomplexRelativeExcisionMap U V)

end SphereSixComplex
