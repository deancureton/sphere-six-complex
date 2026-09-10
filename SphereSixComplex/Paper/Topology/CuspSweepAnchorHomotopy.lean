module
public import SphereSixComplex.Paper.Topology.CuspFixedCircleSweep
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section
noncomputable section
open AlgebraicTopology
open scoped ContinuousMap
namespace SphereSixComplex.Geometry.PaperAnalyticData
open SphereSixComplex.Topology SphereSixComplex.StandardTorusHomology
open GlobalTorusFamily CuspPuncturedCollarBridge CuspRadialClutchingConstruction
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open ComplexTorus TorusFamily CuspPeriodExpansion
open SphereSixComplex.Topology.FixedTopologicalCircleWangBoundary
open SphereSixComplex.Topology.CircleProductIdentityMappingTorus
open SphereSixComplex.CyclicAngularFundamentalDomain
open SectionSevenEllipticTwoDiscCoverData

public def cuspFixedCircleSweepAnchors (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness)))) :
    C(OpenRadialInterval A.starCuspWitness.localWitness.radius × ℝ,
      C(UnitAddCircle × StdTorus 1, A.openEmbeddingStarData.collarSource 0)) := by
  let G := CuspRadialClutchingConstruction.actualCuspRadialClutchingData A.starCuspWitness
  let _ := G.fiberTopology
  let f := fixedLoopMappingTorusMap (cuspFiberClutching _) c
  exact ((⟨G.totalHomeomorph.symm, G.totalHomeomorph.symm.continuous⟩ : C(_, _)).comp
    ⟨fun p ↦ (p.1.1, f (p.2.1 + (p.1.2 : UnitAddCircle), p.2.2)), by fun_prop⟩).curry

public def cuspFixedCircleSweepAnchorHomotopy (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness))))
    {a b : OpenRadialInterval A.starCuspWitness.localWitness.radius × ℝ} (p : Path a b) :
    (A.cuspFixedCircleSweepAnchors c a).Homotopy
      (A.cuspFixedCircleSweepAnchors c b) where
  toFun z := A.cuspFixedCircleSweepAnchors c (p z.1) z.2
  continuous_toFun := continuous_eval.comp
    (((A.cuspFixedCircleSweepAnchors c).continuous.comp
      (p.continuous.comp continuous_fst)).prodMk continuous_snd)
  map_zero_left z := by rw [p.source]
  map_one_left z := by rw [p.target]

public theorem cuspFixedCircleSweep_homotopic_anchor (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness))))
    (b : OpenRadialInterval A.starCuspWitness.localWitness.radius × ℝ) :
    (cuspFixedCircleSweep A c).Homotopic (A.cuspFixedCircleSweepAnchors c b) := by
  let rho : OpenRadialInterval A.starCuspWitness.localWitness.radius :=
    ⟨A.starCuspWitness.localWitness.radius / 2, by
      have := A.starCuspWitness.localWitness.radius_pos
      constructor <;> linarith⟩
  let a := (rho, (0 : ℝ))
  have he : A.cuspFixedCircleSweepAnchors c a = cuspFixedCircleSweep A c := by
    ext z
    change A.actualCuspRadialClutchingData.totalHomeomorph.symm
      (rho, fixedLoopMappingTorusMap (cuspFiberClutching _) c
        (z.1 + ((0 : ℝ) : UnitAddCircle), z.2)) = _
    simp only [AddCircle.coe_zero, add_zero]
    rfl
  have hc : IsPathConnected (Set.Ioo (0 : ℝ) A.starCuspWitness.localWitness.radius) :=
    (convex_Ioo _ _).isPathConnected ⟨rho, rho.2⟩
  let : PathConnectedSpace (OpenRadialInterval A.starCuspWitness.localWitness.radius) :=
    isPathConnected_iff_pathConnectedSpace.mp hc
  let p := PathConnectedSpace.somePath a b
  rw [← he]
  exact ⟨A.cuspFixedCircleSweepAnchorHomotopy c p⟩

public theorem cuspFixedCircleSweepAnchors_real (A : PaperAnalyticData)
    (c : FixedTopologicalCircle (cuspFiberClutching (cuspBasePoint A.cuspCoordinate
      (markedCuspParameter A.starCuspWitness))))
    (b : OpenRadialInterval A.starCuspWitness.localWitness.radius × ℝ)
    (r : ℝ) (z : StdTorus 1) :
    A.cuspFixedCircleSweepAnchors c b ((r : UnitAddCircle), z) =
      actualCuspFullFibreSlice (A := A) (cuspParameterOfPolar b.1.1 (r + b.2))
        (by rw [norm_cuspQ_cuspParameterOfPolar _ _ b.1.2.1]; exact b.1.2.2) (c.1 z) := by
  have h := circleProductRealMappingTorusHomeomorph_real (X := StdTorus 1) (r + b.2, z)
  change circleProductRealMappingTorusHomeomorph (((r + b.2 : ℝ) : UnitAddCircle), z) = _ at h
  apply (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness
    (markedCuspParameter A.starCuspWitness)).injective
  change (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _)
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _).symm _) =
    (puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _)
      ((puncturedLocalCuspQuotientHomeomorph A.starCuspWitness _).symm _)
  erw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  apply Prod.ext
  · apply Subtype.ext
    exact (norm_cuspQ_cuspParameterOfPolar b.1.1 (r + b.2) b.1.2.1).symm
  · change realMappingTorusHomeomorph _
      (fixedLoopRealMappingTorusMap _ _
        (circleProductRealMappingTorusHomeomorph
          ((r : UnitAddCircle) + (b.2 : UnitAddCircle), z))) = _
    rw [← AddCircle.coe_add]
    rw [h, fixedLoopRealMappingTorusMap_mk]
    rfl

end SphereSixComplex.Geometry.PaperAnalyticData
end
end
