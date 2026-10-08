module

public import SphereSixComplex.Cusp.FundamentalGroup.CentralNaturality
public import SphereSixComplex.Regular.Homology.Period
public import SphereSixComplex.Elliptic.DiscCircle.Homology

@[expose] public section
noncomputable section
open scoped ContinuousMap
open SphereSixComplex.Hurewicz.Chains
open SphereSixComplex.StandardCircleHomologyLiftDegree

namespace SphereSixComplex.Geometry.AnalyticData
open GlobalTorusFamily ComplexTorus

variable (A : AnalyticData)

theorem geometricCentralToCore_hurewicz
    (g : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    hurewiczFunction _ (A.geometricMarkedCentralToCoreEquiv g) =
      integralSingularHomologyMap 1
        ⟨A.openEmbeddingStarData.centralToEulerPieceHomeomorph,
          A.openEmbeddingStarData.centralToEulerPieceHomeomorph.continuous⟩
        (hurewiczFunction _ g) := by
  have h : hurewiczFunction _ (A.cuspCentralToCoreEquiv g) =
      integralSingularHomologyMap 1
          ⟨A.openEmbeddingStarData.centralToEulerPieceHomeomorph,
            A.openEmbeddingStarData.centralToEulerPieceHomeomorph.continuous⟩
        (hurewiczFunction _ g) := by
    unfold cuspCentralToCoreEquiv
    erw [hurewiczFunction_basePath, hurewiczFunction_homeomorphMulEquivOfEq]
    rfl
  refine Eq.trans ?_ h
  change Multiplicative.toAdd ((hurewiczPi1 _) (A.geometricMarkedCentralToCoreEquiv g)) =
    Multiplicative.toAdd ((hurewiczPi1 _) (A.cuspCentralToCoreEquiv g))
  congr 1
  simp only [geometricMarkedCentralToCoreEquiv, cuspToCoreEquiv,
    cuspCentralMarkingCorrection, MulEquiv.trans_apply, MulAut.conj_inv_apply,
    map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact inv_mul_cancel_comm _ _

theorem centralToStar_hurewicz
    (g : FundamentalGroup A.CentralFamily A.centralAffineBase) :
    hurewiczFunction A.vanKampenBase
      (A.actualVanKampenFourPieceCover.coreFundamentalGroupMap
        (A.cuspCentralNaturality.centralToCore g)) =
      integralSingularHomologyMap 1 (EllipticDiscCircle.centralInclusion A)
        (hurewiczFunction _ g) := by
  change hurewiczFunction _ (FundamentalGroup.map
    (CoveringSpace.subsetInclusion A.actualVanKampenFourPieceCover.core)
    ⟨A.vanKampenBase, A.actualVanKampenFourPieceCover.base_mem_core⟩
    (A.cuspCentralNaturality.centralToCore g)) = _
  rw [hurewiczFunction_map]
  change integralSingularHomologyMap 1 _
    (hurewiczFunction _ (A.geometricMarkedCentralToCoreEquiv g)) = _
  rw [A.geometricCentralToCore_hurewicz]
  erw [integralSingularHomologyMap_comp_wang]
  rfl

theorem cuspPeriod_homology_eq_translation (a : LatticeData.Lattice) :
    loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint a).map
      (regularFamilyQuotientMap A.periods).continuous) =
      hurewiczFunction A.centralAffineBase
        (Additive.toMul (A.centralAffineCorePiOneData.translation a)) := by
  change _ = hurewiczFunction A.cuspCentralBase
    (Additive.toMul (A.cuspCentralTranslation
      (SphereSixComplex.TriangleGroup.rhoLambda
        ((SphereSixComplex.TriangleGroup.g₁ * SphereSixComplex.TriangleGroup.g₂) ^
          A.geometricCentralCuspConjugatorExponent) a)))
  rw [A.cuspCentralTranslation_eq_periodLoop]
  change _ = loopHomologyClass (A.cuspCentralPeriodLoop _)
  have hp (b : LatticeData.Lattice) :
      loopHomologyClass (A.cuspCentralPeriodLoop b) =
        loopHomologyClass ((regularFamilyPeriodLoop A.periods A.cuspRegularCoverPoint b).map
          (regularFamilyQuotientMap A.periods).continuous) := by
    apply loopHomologyClass_eq_of_toContinuousMap_eq
    rfl
  rw [hp]
  exact (loopHomologyClass_regularFamilyPeriodLoop_rhoLambda A.periods
    A.cuspRegularCoverPoint _ a).symm

end SphereSixComplex.Geometry.AnalyticData
