module

public import SphereSixComplex.Paper.Geometry.PaperLocalCuspFillingConnected
public import SphereSixComplex.Prerequisites.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Paper.Topology.SectionSevenMayerVietorisEuler
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Connectivity and overlap identification for the analytic star

The additive cusp radius cover is convex, so the punctured cusp quotient and collar are path
connected. The final overlap is identified with this actual collar, and the preceding union
with the elliptic interior.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContDiff Manifold

namespace SphereSixComplex

namespace Geometry.CuspCollar

open SphereSixComplex.Geometry
open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.InfiniteA2Toric
open SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions
open SphereSixComplex.Geometry.InfiniteA2Toric.QuantitativeRegions.BoundedPolydiscRegions

/-- The radial condition on the additive cusp cover is an affine half-space condition. -/
public theorem mem_additiveCuspRadiusCover_iff_halfSpace
    (r : ℝ) (hr : 0 < r) (p : AdditiveCuspCover) :
    p ∈ additiveCuspRadiusCover r ↔
      -2 * Real.pi * p.2.im < Real.log r := by
  change ‖cuspQ p.2‖ < r ↔ _
  rw [norm_cuspQ, ← Real.lt_log_iff_exp_lt hr]

/-- The additive cusp-radius cover is nonempty at every positive radius. -/
public theorem additiveCuspRadiusCover_nonempty (r : ℝ) (hr : 0 < r) :
    (additiveCuspRadiusCover r).Nonempty := by
  let c : ℝ := (|Real.log r| + 1) / (2 * Real.pi)
  let s : ℂ := (c : ℂ) * Complex.I
  refine ⟨(0, s), (mem_additiveCuspRadiusCover_iff_halfSpace r hr _).mpr ?_⟩
  rw [show s.im = c by simp [s],
    show c = (|Real.log r| + 1) / (2 * Real.pi) by rfl]
  have hcancel :
      -2 * Real.pi * ((|Real.log r| + 1) / (2 * Real.pi)) =
        -(|Real.log r| + 1) := by
    field_simp
  rw [hcancel]
  linarith [neg_abs_le (Real.log r)]

/-- The additive cusp-radius cover is convex as a real subset. -/
public theorem additiveCuspRadiusCover_convex (r : ℝ) (hr : 0 < r) :
    Convex ℝ (additiveCuspRadiusCover r) := by
  rw [show additiveCuspRadiusCover r =
      {p : AdditiveCuspCover | -2 * Real.pi * p.2.im < Real.log r} by
    ext p
    exact mem_additiveCuspRadiusCover_iff_halfSpace r hr p]
  apply convex_halfSpace_lt
  exact .mk (by intro x y; simp; ring) (by intro c x; simp; ring)

/-- The additive cusp-radius cover is path-connected. -/
public theorem additiveCuspRadiusCover_pathConnected (r : ℝ) (hr : 0 < r) :
    PathConnectedSpace (additiveCuspRadiusCover r) :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((additiveCuspRadiusCover_convex r hr).isPathConnected
      (additiveCuspRadiusCover_nonempty r hr))

/-- Removing the central toric fibre from a positive-radius local cusp carrier leaves a
path-connected space. -/
public theorem puncturedLocalCarrier_pathConnected
    (M : Model) (r : ℝ) (hr : 0 < r) :
    PathConnectedSpace {p : localCarrier M r // M.t p ≠ 0} := by
  let _ : PathConnectedSpace (additiveCuspRadiusCover r) :=
    additiveCuspRadiusCover_pathConnected r hr
  let _ : PathConnectedSpace
      (Quotient (Setoid.ker (denseCuspExponentialRadius r))) := inferInstance
  exact pathConnectedSpace_of_homeomorph (additiveToPuncturedLocalHomeomorph M r)

/-- The actual phase-action quotient of the punctured local cusp carrier is path-connected. -/
public theorem puncturedLocalCuspQuotient_pathConnected
    {E : FuchsianModularLift} {D : FuchsianPeriodData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    PathConnectedSpace (PuncturedLocalCuspQuotient W) := by
  let _ : PathConnectedSpace
      {p : localCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_pathConnected M W.localWitness.radius W.localWitness.radius_pos
  change PathConnectedSpace (Quotient (puncturedPsiOrbitRel W))
  infer_instance

end Geometry.CuspCollar

namespace Geometry.AnalyticData

variable (A : AnalyticData)

/-- The central source of the analytic star is path-connected. -/
public theorem starCentral_pathConnected : PathConnectedSpace A.CentralFamily := by
  let _ := A.starCentralCharts
  let _ : ConnectedSpace A.CentralFamily := A.centralFamily_connected
  let _ : LocallyPathConnectedSpace A.CentralFamily :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel A.CentralFamily
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- Every filling source of the analytic star is path-connected. -/
public theorem starFilling_pathConnected (i : Fin 3) :
    PathConnectedSpace (A.StarFilling i) := by
  let _ := A.starFillingCharts i
  let _ : ConnectedSpace (A.StarFilling i) := A.starFilling_connected i
  let _ : LocallyPathConnectedSpace (A.StarFilling i) :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel (A.StarFilling i)
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-- The punctured cusp collar source in the analytic star is path-connected. -/
public theorem starCuspCollarSource_pathConnected :
    PathConnectedSpace (A.openEmbeddingStarData.collarSource 0) := by
  change PathConnectedSpace
    (CuspCollar.PuncturedLocalCuspQuotient A.starCuspWitness)
  exact CuspCollar.puncturedLocalCuspQuotient_pathConnected A.starCuspWitness

/-- The penultimate Mayer--Vietoris stage is the union of the central, order-three, and
order-four pieces. -/
public theorem ellipticInterior_eq_threePieceUnion :
    (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) =
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 0 ∪
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 1 ∪
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 2 := by
  ext x
  simp only [FourPieceOpenCover.stage, mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi, hx⟩
    fin_cases i <;> simp_all
  · rintro ((hx | hx) | hx)
    · exact ⟨0, by omega, hx⟩
    · exact ⟨1, by omega, hx⟩
    · exact ⟨2, by omega, hx⟩


/-- The actual final overlap is exactly the central--cusp intersection. -/
public theorem cuspAttachmentOverlap_eq_centralCuspIntersection :
    (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
      (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 =
      (A.openEmbeddingStarData.sectionSevenEulerCover).piece 0 ∩
        (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 := by
  ext x
  constructor
  · rintro ⟨hxstage, hxcusp⟩
    rw [FourPieceOpenCover.stage] at hxstage
    simp only [mem_iUnion] at hxstage
    obtain ⟨i, hi, hxi⟩ := hxstage
    fin_cases i
    · exact ⟨hxi, hxcusp⟩
    · have hbad :
          x ∈ (A.openEmbeddingStarData.sectionSevenEulerCover).piece 2 ∩
            (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 := ⟨hxi, hxcusp⟩
      have hempty :
          (A.openEmbeddingStarData.sectionSevenEulerCover).piece 2 ∩
            (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 = ∅ := by
        simpa using A.openEmbeddingStarData.fillingPiece_inter_fillingPiece
          (i := 1) (j := 0) (by decide)
      rw [hempty] at hbad
      exact hbad.elim
    · have hbad :
          x ∈ (A.openEmbeddingStarData.sectionSevenEulerCover).piece 3 ∩
            (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 := ⟨hxi, hxcusp⟩
      have hempty :
          (A.openEmbeddingStarData.sectionSevenEulerCover).piece 3 ∩
            (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 = ∅ := by
        simpa using A.openEmbeddingStarData.fillingPiece_inter_fillingPiece
          (i := 2) (j := 0) (by decide)
      rw [hempty] at hbad
      exact hbad.elim
    · change (3 : Fin 4) ≤ 2 at hi
      omega
  · rintro ⟨hxcentral, hxcusp⟩
    refine ⟨?_, hxcusp⟩
    rw [FourPieceOpenCover.stage]
    exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨by omega, hxcentral⟩⟩

/-- The punctured cusp collar is homeomorphic to the actual final overlap. -/
public noncomputable def cuspCollarToSectionSevenFinalOverlapHomeomorph :
    A.openEmbeddingStarData.collarSource 0 ≃ₜ
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) :=
  (A.openEmbeddingStarData.collarToMayerVietorisOverlapHomeomorph 0).trans
    (Homeomorph.setCongr (by
      change
        (A.openEmbeddingStarData.sectionSevenEulerCover).stage 0 ∩
            (A.openEmbeddingStarData.sectionSevenEulerCover).piece 1 =
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage 2 ∩
            (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3
      rw [A.openEmbeddingStarData.sectionSevenEulerStage_zero]
      exact (A.cuspAttachmentOverlap_eq_centralCuspIntersection).symm))


end Geometry.AnalyticData

end SphereSixComplex
