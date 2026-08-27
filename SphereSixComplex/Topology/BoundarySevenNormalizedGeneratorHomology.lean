module

public import SphereSixComplex.Topology.BoundarySevenSubdivisionGeneratorNormalization
public import SphereSixComplex.Topology.BoundarySevenSubdivisionGeneratorTransportPrelude

/-!
# The normalized boundary-seven generator in simplicial homology

This file packages the previously constructed normalization and top-cycle isomorphisms into an
explicit orientation of unnormalized simplicial homology.  It also verifies that the intrinsic
alternating facet chain represents the positive generator for that orientation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

public noncomputable abbrev BoundarySevenUnnormalizedIntegralChains :
    ChainComplex AddCommGrpCat ℕ :=
  (∂Δ[7] : SSet.{0}).chainComplex (AddCommGrpCat.of ℤ)

/-- The canonical composite identifying unnormalized degree-six simplicial homology of
`∂Δ[7]` with `ℤ`: normalize, identify normalized homology with its top cycle kernel,
and use the orientation coming from the unique normalized seven-simplex of `Δ[7]`. -/
public noncomputable def boundarySevenSimplicialHomologySixIsoInt :
    BoundarySevenUnnormalizedIntegralChains.homology 6 ≅ AddCommGrpCat.of ℤ := by
  let _ : QuasiIso ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
      (AddCommGrpCat.of ℤ)) := inferInstance
  exact isoOfQuasiIsoAt
      ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
        (AddCommGrpCat.of ℤ)) 6 ≪≫
    boundarySeven_normalizedHomologySixIsoTopCycles ≪≫
    boundarySevenTopCyclesIsoStandardSevenTopCycles ≪≫
    standardSevenTopCyclesIsoInt

/-- The explicit additive equivalence underlying
`boundarySevenSimplicialHomologySixIsoInt`. -/
public noncomputable def boundarySevenSimplicialHomologySixAddEquivInt :
    BoundarySevenUnnormalizedIntegralChains.homology 6 ≃+ ℤ :=
  boundarySevenSimplicialHomologySixIsoInt.addCommGroupIsoToAddEquiv

/-- The intrinsic alternating facet chain, lifted to the cycle object of the unnormalized
simplicial chain complex. -/
public noncomputable def boundarySevenOriginalFundamentalCycle :
    AddCommGrpCat.of ℤ ⟶ BoundarySevenUnnormalizedIntegralChains.cycles 6 :=
  BoundarySevenUnnormalizedIntegralChains.liftCycles
    boundarySevenOriginalFundamentalChain 5 (by simp)
      boundarySevenOriginalFundamentalChain_isCycle

@[reassoc (attr := simp)]
public theorem boundarySevenOriginalFundamentalCycle_iCycles :
    boundarySevenOriginalFundamentalCycle ≫
        BoundarySevenUnnormalizedIntegralChains.iCycles 6 =
      boundarySevenOriginalFundamentalChain := by
  rw [boundarySevenOriginalFundamentalCycle]
  apply HomologicalComplex.liftCycles_i

/-- The homology class represented by the intrinsic alternating facet chain. -/
public noncomputable def boundarySevenOriginalFundamentalHomologyClass :
    AddCommGrpCat.of ℤ ⟶ BoundarySevenUnnormalizedIntegralChains.homology 6 :=
  boundarySevenOriginalFundamentalCycle ≫
    BoundarySevenUnnormalizedIntegralChains.homologyπ 6

/-- A degree-six cycle followed by the standard homology--cycle-kernel composite is the
corresponding kernel element when degree seven vanishes. -/
private theorem cycle_homologySixIsoScTopCycles
    {A : AddCommGrpCat}
    (N : ChainComplex AddCommGrpCat ℕ)
    (hf : (N.sc' 7 6 5).f = 0)
    (c : A ⟶ N.cycles 6)
    (z : A ⟶ kernel ((N.sc' 7 6 5).g))
    (hz : c ≫ N.iCycles 6 = z ≫ kernel.ι ((N.sc' 7 6 5).g)) :
    c ≫ N.homologyπ 6 ≫
      (N.homologyIsoSc' 7 6 5 (by simp) (by simp) ≪≫
        ((N.sc' 7 6 5).asIsoHomologyπ hf).symm ≪≫
        (N.sc' 7 6 5).cyclesIsoKernel).hom = z := by
  apply (cancel_mono (kernel.ι ((N.sc' 7 6 5).g))).1
  simp only [Iso.trans_hom, Category.assoc]
  rw [N.π_homologyIsoSc'_hom_assoc]
  rw [Iso.symm_hom]
  rw [ShortComplex.homologyπ_comp_asIsoHomologyπ_inv_assoc]
  rw [ShortComplex.cyclesIsoKernel_hom]
  rw [kernel.lift_ι]
  rw [N.cyclesIsoSc'_hom_iCycles]
  exact hz

/-- A normalized cycle followed by the canonical normalized `H₆`--top-cycle isomorphism is
the corresponding element of the differential kernel. -/
private theorem normalizedCycle_homologySixIsoTopCycles
    {A : AddCommGrpCat}
    (c : A ⟶ BoundarySevenNormalizedIntegralChains.cycles 6)
    (z : A ⟶ kernel (BoundarySevenNormalizedIntegralChains.d 6 5))
    (hz : c ≫ BoundarySevenNormalizedIntegralChains.iCycles 6 =
      z ≫ kernel.ι (BoundarySevenNormalizedIntegralChains.d 6 5)) :
    c ≫ BoundarySevenNormalizedIntegralChains.homologyπ 6 ≫
        boundarySeven_normalizedHomologySixIsoTopCycles.hom = z := by
  let N := BoundarySevenNormalizedIntegralChains
  let S := N.sc' 7 6 5
  let hf : S.f = 0 :=
    boundarySeven_normalizedChains_degreeSeven_isZero.eq_of_src _ _
  change c ≫ N.homologyπ 6 ≫
      (N.homologyIsoSc' 7 6 5 (by simp) (by simp) ≪≫
        (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel).hom = z
  apply cycle_homologySixIsoScTopCycles N hf c z
  exact hz

/-- Normalization takes the lifted original boundary cycle to the distinguished normalized
orientation cycle, after passing from normalized homology to its top-cycle kernel. -/
public theorem boundarySevenOriginalFundamentalHomologyClass_normalized :
    boundarySevenOriginalFundamentalHomologyClass ≫
        HomologicalComplex.homologyMap
          ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
            (AddCommGrpCat.of ℤ)) 6 ≫
        boundarySeven_normalizedHomologySixIsoTopCycles.hom =
      boundarySevenNormalizedOrientationGenerator := by
  rw [boundarySevenOriginalFundamentalHomologyClass,
    Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
  apply normalizedCycle_homologySixIsoTopCycles
    (c := boundarySevenOriginalFundamentalCycle ≫
      HomologicalComplex.cyclesMap
        ((∂Δ[7] : SSet.{0}).toNormalizedChainComplex
          (AddCommGrpCat.of ℤ)) 6)
    (z := boundarySevenNormalizedOrientationGenerator)
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, boundarySevenOriginalFundamentalCycle_iCycles]
  exact boundarySevenOriginalFundamentalChain_toNormalized

/-- The class of the intrinsic alternating facet chain is the positive generator for the
explicit unnormalized simplicial-homology orientation. -/
public theorem boundarySevenOriginalFundamentalHomologyClass_isoInt :
    boundarySevenOriginalFundamentalHomologyClass ≫
        boundarySevenSimplicialHomologySixIsoInt.hom =
      𝟙 (AddCommGrpCat.of ℤ) := by
  let F := (∂Δ[7] : SSet.{0}).toNormalizedChainComplex
    (AddCommGrpCat.of ℤ)
  let E := boundarySevenTopCyclesIsoStandardSevenTopCycles ≪≫
    standardSevenTopCyclesIsoInt
  calc
    boundarySevenOriginalFundamentalHomologyClass ≫
          boundarySevenSimplicialHomologySixIsoInt.hom =
        (boundarySevenOriginalFundamentalHomologyClass ≫
          HomologicalComplex.homologyMap F 6 ≫
          boundarySeven_normalizedHomologySixIsoTopCycles.hom) ≫ E.hom := by
      dsimp only [F, E]
      simp only [boundarySevenSimplicialHomologySixIsoInt,
        Iso.trans_hom, isoOfQuasiIsoAt_hom, Category.assoc]
    _ = boundarySevenNormalizedOrientationGenerator ≫ E.hom := by
      rw [boundarySevenOriginalFundamentalHomologyClass_normalized]
    _ = 𝟙 (AddCommGrpCat.of ℤ) := by
      rw [boundarySevenNormalizedOrientationGenerator_eq_orientation_inv]
      exact Iso.inv_hom_id E

/-- Elementwise form: the homology class represented by
`boundarySevenOriginalFundamentalChain` maps to `1 ∈ ℤ`. -/
public theorem boundarySevenOriginalFundamentalHomologyClass_mapsToOne :
    boundarySevenSimplicialHomologySixAddEquivInt
        (boundarySevenOriginalFundamentalHomologyClass (1 : ℤ)) = 1 := by
  have h := ConcreteCategory.congr_hom
    boundarySevenOriginalFundamentalHomologyClass_isoInt (1 : ℤ)
  change boundarySevenSimplicialHomologySixIsoInt.hom.hom
    (boundarySevenOriginalFundamentalHomologyClass.hom (1 : ℤ)) = 1
  exact h

end SphereSixComplex
