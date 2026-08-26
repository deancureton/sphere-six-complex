module

public import SphereSixComplex.Topology.CollarProductVanishing
public import SphereSixComplex.Topology.PaperSectionSevenLocalEulerModelAssembly
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

/-- A space realized as a radial interval times a mapping torus has no sixth integral singular
homology once its fibre has none in degrees five and six. -/
public theorem subsingleton_homology_six_of_radialMappingTorus
    {T : Type} [TopologicalSpace T] (φ : T ≃ₜ T) {r : ℝ} (hr : 0 < r)
    {Z : Type} [TopologicalSpace Z]
    (e : Z ≃ₜ OpenRadialInterval r × CircleMappingTorus φ)
    (h5 : Subsingleton (IntegralSingularHomology 5 T))
    (h6 : Subsingleton (IntegralSingularHomology 6 T)) :
    Subsingleton (IntegralSingularHomology 6 Z) := by
  have hMT : Subsingleton (IntegralSingularHomology 6 (CircleMappingTorus φ)) :=
    subsingleton_homology_succ_finiteBouquetMappingTorus _ 5 h6 h5
  let _ : ContractibleSpace (OpenRadialInterval r) := contractibleSpace_openInterval hr
  exact OpenEmbeddingStarData.subsingleton_homology_of_homeomorph 6 e.symm
    (subsingleton_homology_prod_of_contractible _ _ 6 hMT)

/-- The four-torus case: a cell model on the fibre supplies both vanishing hypotheses. -/
public theorem subsingleton_homology_six_of_radialMappingTorus_fourTorusFibre
    {T : Type} [TopologicalSpace T] (M : FourTorusCellModel T) (φ : T ≃ₜ T) {r : ℝ} (hr : 0 < r)
    {Z : Type} [TopologicalSpace Z]
    (e : Z ≃ₜ OpenRadialInterval r × CircleMappingTorus φ) :
    Subsingleton (IntegralSingularHomology 6 Z) :=
  subsingleton_homology_six_of_radialMappingTorus φ hr e
    M.subsingleton_homology_five M.subsingleton_homology_six

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

/-- The whole Section 7 top-degree obligation for the actual star, reduced to the cusp collar.

The local Euler models already supply the finiteness of the central piece and the three fillings,
and both elliptic collars are settled above, so the cusp collar's sixth homology is the only thing
still asked for. -/
public theorem sectionSevenStageTopDegreeVanishing_of_cuspCollar
    (M : A.SectionSevenLocalEulerModels)
    (hcusp : Subsingleton (IntegralSingularHomology 6 (A.starCollarSourceType 0))) :
    A.openEmbeddingStarData.SectionSevenStageTopDegreeVanishing :=
  A.openEmbeddingStarData.sectionSevenStageTopDegreeVanishing_of_localFinite
    M.localIntegralHomologyFiniteSix.1 M.localIntegralHomologyFiniteSix.2.1
    (A.subsingleton_homology_six_collarSource_of_cusp hcusp)

/-- The same for the production choice of local Euler models: the actual star's Section 7
top-degree obligation holds as soon as the cusp collar has no sixth homology. -/
public theorem sectionSevenStageTopDegreeVanishing_of_actualCuspCollar
    (hcusp : Subsingleton (IntegralSingularHomology 6 (A.starCollarSourceType 0))) :
    A.openEmbeddingStarData.SectionSevenStageTopDegreeVanishing :=
  A.sectionSevenStageTopDegreeVanishing_of_cuspCollar A.sectionSevenLocalEulerModels hcusp

end Geometry.PaperAnalyticData

end SphereSixComplex

end

end
