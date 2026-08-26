module

public import SphereSixComplex.Topology.CollarProductVanishing
public import SphereSixComplex.Topology.FiniteCWModelVanishing
public import SphereSixComplex.Topology.PaperEllipticCollarFundamentalDomain
public import SphereSixComplex.Topology.SectionSevenStageTopDegree
public import SphereSixComplex.Topology.WangDimensionVanishing

/-!
# The elliptic collars' sixth homology

Both elliptic collars are realized as a radial interval times a mapping torus whose fibre is the
additive four-torus of the period family.  That fibre has a four-torus cell model, so it has no
fifth or sixth homology, and the two reductions -- discarding the contractible interval and reading
the mapping torus off the fibre through the Wang sequence -- leave nothing in degree six.

The general statement is separated out because it is what the cusp collar needs too, once its
fibre is known to be a four-torus.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex

/-- A space realized as a radial interval times a mapping torus with four-torus fibre has no sixth
integral singular homology. -/
public theorem subsingleton_homology_six_of_radialMappingTorus_fourTorusFibre
    {T : Type} [TopologicalSpace T] (M : FourTorusCellModel T) (φ : T ≃ₜ T) {r : ℝ} (hr : 0 < r)
    {Z : Type} [TopologicalSpace Z]
    (e : Z ≃ₜ OpenRadialInterval r × CircleMappingTorus φ) :
    Subsingleton (IntegralSingularHomology 6 Z) := by
  have hMT : Subsingleton (IntegralSingularHomology 6 (CircleMappingTorus φ)) :=
    subsingleton_homology_succ_finiteBouquetMappingTorus _ 5
      M.subsingleton_homology_six M.subsingleton_homology_five
  let _ : ContractibleSpace (OpenRadialInterval r) := contractibleSpace_openInterval hr
  exact OpenEmbeddingStarData.subsingleton_homology_of_homeomorph 6 e.symm
    (subsingleton_homology_prod_of_contractible _ _ 6 hMT)

namespace Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

/-- The order-three elliptic collar has no sixth integral singular homology. -/
public theorem subsingleton_homology_six_orderThreeCollar :
    Subsingleton (IntegralSingularHomology 6 (A.starCollarSourceType 1)) :=
  subsingleton_homology_six_of_radialMappingTorus_fourTorusFibre
    (EstablishedFiniteCWTopology.additiveTorusFourTorusCellModel _
      (ComplexTorus.FullRank.ofSetupInequalities _
        (AnalyticTorusFamily.parameterMap A.periods _).2))
    _ A.starSeparation.orderThree.radius_pos
    A.orderThreeCollarRadialMappingTorusHomeomorph

/-- The order-four elliptic collar has no sixth integral singular homology. -/
public theorem subsingleton_homology_six_orderFourCollar :
    Subsingleton (IntegralSingularHomology 6 (A.starCollarSourceType 2)) :=
  subsingleton_homology_six_of_radialMappingTorus_fourTorusFibre
    (EstablishedFiniteCWTopology.additiveTorusFourTorusCellModel _
      (ComplexTorus.FullRank.ofSetupInequalities _
        (AnalyticTorusFamily.parameterMap A.periods _).2))
    _ A.starSeparation.orderFour.radius_pos
    A.orderFourCollarRadialMappingTorusHomeomorph

/-- The Section 7 collar obligation for the actual star, reduced to the cusp collar alone: both
elliptic collars are already settled by their four-torus fibres. -/
public theorem subsingleton_homology_six_collarSource_of_cusp
    (hcusp : Subsingleton (IntegralSingularHomology 6 (A.starCollarSourceType 0)))
    (i : Fin 3) :
    Subsingleton (IntegralSingularHomology 6 (A.openEmbeddingStarData.collarSource i)) := by
  fin_cases i
  · exact hcusp
  · exact A.subsingleton_homology_six_orderThreeCollar
  · exact A.subsingleton_homology_six_orderFourCollar

end Geometry.PaperAnalyticData

end SphereSixComplex

end

end
