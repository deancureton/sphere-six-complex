module

public import SphereSixComplex.Prerequisites.Geometry.Gluing.OpenEmbeddingStar

@[expose] public section
noncomputable section
namespace SphereSixComplex.OpenEmbeddingStarData

theorem fillingInclusion_toFilling (S : OpenEmbeddingStarData)
    (i : Fin 3) (q : S.collarSource i) :
    S.toFourPieceStarGluingData.glueData.toGlueData.ι (some i) (S.toFilling i q) =
      S.toFourPieceStarGluingData.glueData.toGlueData.ι none (S.toCentral i q) := by
  apply (S.toFourPieceStarGluingData.glueData.ι_eq_iff_rel
    (some i) none (S.toFilling i q) (S.toCentral i q)).mpr
  exact ⟨S.fillingCollarPoint i q, rfl, by
    change ((S.collarEquiv i).symm (S.fillingCollarPoint i q)).val = S.toCentral i q
    rw [S.collarEquiv_symm_toFilling]
    rfl⟩

end SphereSixComplex.OpenEmbeddingStarData
