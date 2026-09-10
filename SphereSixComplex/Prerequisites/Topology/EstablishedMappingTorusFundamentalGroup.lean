module

public import SphereSixComplex.Prerequisites.Topology.MappingTorusHNNSurjectivityProof

/-!
# Mapping-torus fundamental group

The canonical HNN comparison is proved surjective by the explicit two-piece van Kampen argument,
and hence gives the standard mapping-torus fundamental-group universal property.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- The canonical HNN comparison is surjective. -/
public theorem mappingTorusHNNToFundamentalGroup_surjective
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    Function.Surjective (mappingTorusHNNToFundamentalGroup phi x delta) :=
  mappingTorusHNNToFundamentalGroup_surjective_proof phi x delta

/-- The canonical HNN comparison is bijective. -/
public theorem mappingTorusHNNToFundamentalGroup_bijective
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    Function.Bijective (mappingTorusHNNToFundamentalGroup phi x delta) :=
  ⟨mappingTorusHNNToFundamentalGroup_injective phi x delta,
    mappingTorusHNNToFundamentalGroup_surjective phi x delta⟩

public noncomputable def establishedMappingTorusFundamentalGroupUP_vanKampen
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    MappingTorusFundamentalGroupUP phi x delta :=
  mappingTorusFundamentalGroupUP_of_bijective phi x delta
    (mappingTorusHNNToFundamentalGroup_bijective phi x delta)

/-- The standard HNN-extension presentation of the fundamental group of a mapping torus. -/
public noncomputable def mappingTorusFundamentalGroupUP
    {F : Type} [TopologicalSpace F] [PathConnectedSpace F]
    (phi : F ≃ₜ F) (x : F) (delta : Path (phi x) x) :
    MappingTorusFundamentalGroupUP phi x delta :=
  mappingTorusFundamentalGroupUP_of_bijective phi x delta
    (mappingTorusHNNToFundamentalGroup_bijective phi x delta)

end SphereSixComplex
