module

public import SphereSixComplex.Paper.Geometry.PaperLocalCuspFillingConnected
public import SphereSixComplex.Prerequisites.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Paper.Topology.SectionSevenMayerVietorisEuler
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The final degree-zero Mayer--Vietoris map of the analytic star

The central family and all three filling pieces are path-connected because they are connected
complex manifolds.  Hence the penultimate stage and the final cusp piece are path-connected.
The punctured cusp collar is the quotient of a convex additive half-space, so it too is
path-connected.  Its homeomorphism with the actual final overlap then gives canonical augmentation
bases in which the final degree-zero Mayer--Vietoris map is `x ↦ (x, -x)`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Set
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The canonical conversion from one integer coordinate to a `Fin 1`-indexed vector. -/
public noncomputable def integerToFinOneAddEquiv : ℤ ≃+ (Fin 1 → ℤ) where
  toFun z := fun _ ↦ z
  invFun f := f 0
  left_inv _ := rfl
  right_inv f := by funext i; fin_cases i; rfl
  map_add' _ _ := rfl

/-- The canonical conversion from an integer pair to a `Fin 2`-indexed vector. -/
public noncomputable def integerPairToFinTwoAddEquiv : (ℤ × ℤ) ≃+ (Fin 2 → ℤ) where
  toFun z := ![z.1, z.2]
  invFun f := (f 0, f 1)
  left_inv z := by rcases z with ⟨x, y⟩; rfl
  right_inv f := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl

namespace Geometry.CuspPuncturedCollarBridge

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
    {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    PathConnectedSpace (PuncturedLocalCuspQuotient W) := by
  let _ : PathConnectedSpace
      {p : localCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_pathConnected M W.localWitness.radius W.localWitness.radius_pos
  change PathConnectedSpace (Quotient (puncturedPsiOrbitRel W))
  infer_instance

end Geometry.CuspPuncturedCollarBridge

namespace Geometry.PaperAnalyticData

variable (A : PaperAnalyticData)

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
    (CuspPuncturedCollarBridge.PuncturedLocalCuspQuotient A.starCuspWitness)
  exact CuspPuncturedCollarBridge.puncturedLocalCuspQuotient_pathConnected A.starCuspWitness

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

/-- The penultimate Mayer--Vietoris stage of the analytic star is path-connected. -/
public theorem ellipticInterior_pathConnected :
    PathConnectedSpace
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4)) := by
  let _ : PathConnectedSpace A.CentralFamily := A.starCentral_pathConnected
  let _ : PathConnectedSpace (A.StarFilling 1) := A.starFilling_pathConnected 1
  let _ : PathConnectedSpace (A.StarFilling 2) := A.starFilling_pathConnected 2
  let _ : PathConnectedSpace A.openEmbeddingStarData.central := by
    change PathConnectedSpace A.CentralFamily
    exact A.starCentral_pathConnected
  let _ : PathConnectedSpace (A.openEmbeddingStarData.filling 1) := by
    change PathConnectedSpace (A.StarFilling 1)
    exact A.starFilling_pathConnected 1
  let _ : PathConnectedSpace (A.openEmbeddingStarData.filling 2) := by
    change PathConnectedSpace (A.StarFilling 2)
    exact A.starFilling_pathConnected 2
  let _ : PathConnectedSpace
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 0) :=
    pathConnectedSpace_of_homeomorph
      A.openEmbeddingStarData.centralToSectionSevenEulerPieceHomeomorph
  let _ : PathConnectedSpace
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 1) :=
    pathConnectedSpace_of_homeomorph
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 1)
  let _ : PathConnectedSpace
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 2) :=
    pathConnectedSpace_of_homeomorph
      (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 2)
  have hPieceZero :
      IsPathConnected
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 0) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hPieceOne :
      IsPathConnected
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 1) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hPieceTwo :
      IsPathConnected
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 2) :=
    isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hZeroOne :
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 0 ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 1).Nonempty := by
    let _ : Nonempty (A.openEmbeddingStarData.collarSource 1) :=
      A.openEmbeddingStarData_collarSource_nonempty 1
    have h := Set.range_nonempty
      (A.openEmbeddingStarData.collarSourceToGlued (1 : Fin 3))
    rw [A.openEmbeddingStarData.range_collarSourceToGlued 1] at h
    exact h
  have hZeroTwo :
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 0 ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 2).Nonempty := by
    let _ : Nonempty (A.openEmbeddingStarData.collarSource 2) :=
      A.openEmbeddingStarData_collarSource_nonempty 2
    have h := Set.range_nonempty
      (A.openEmbeddingStarData.collarSourceToGlued (2 : Fin 3))
    rw [A.openEmbeddingStarData.range_collarSourceToGlued 2] at h
    exact h
  have hZeroOnePath :
      IsPathConnected
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 0 ∪
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 1) :=
    hPieceZero.union hPieceOne hZeroOne
  have hUnionInterTwo :
      (((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 0 ∪
          (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 1) ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 2).Nonempty := by
    obtain ⟨x, hxzero, hxtwo⟩ := hZeroTwo
    exact ⟨x, Or.inl hxzero, hxtwo⟩
  apply isPathConnected_iff_pathConnectedSpace.mp
  rw [A.ellipticInterior_eq_threePieceUnion]
  exact hZeroOnePath.union hPieceTwo hUnionInterTwo

/-- The last piece in the paper's Mayer--Vietoris order is the cusp filling and is
path-connected. -/
public theorem cuspAttachmentPiece_pathConnected :
    PathConnectedSpace
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3) := by
  let _ : PathConnectedSpace (A.StarFilling 0) := A.starFilling_pathConnected 0
  let _ : PathConnectedSpace (A.openEmbeddingStarData.filling 0) := by
    change PathConnectedSpace (A.StarFilling 0)
    exact A.starFilling_pathConnected 0
  exact pathConnectedSpace_of_homeomorph
    (A.openEmbeddingStarData.fillingToSectionSevenEulerPieceHomeomorph 0)

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

/-- Path-connectedness of the punctured cusp collar transports to the actual final overlap. -/
public theorem cuspAttachmentOverlap_pathConnected :
    PathConnectedSpace
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) := by
  let _ := A.starCuspCollarSource_pathConnected
  exact pathConnectedSpace_of_homeomorph
    A.cuspCollarToSectionSevenFinalOverlapHomeomorph

/-- The canonical augmentation basis on the actual final overlap. -/
public noncomputable def cuspAttachmentOverlapHomologyZeroEquiv :
    IntegralSingularHomology 0
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace) ≃+ (Fin 1 → ℤ) := by
  let _ := A.cuspAttachmentOverlap_pathConnected
  exact (pathConnectedIntegralHomologyZeroEquivInteger _).trans integerToFinOneAddEquiv

/-- The product of the canonical augmentation bases on the two final sides. -/
public noncomputable def cuspAttachmentSidesHomologyZeroEquiv :
    (IntegralSingularHomology 0
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4)) ×
      IntegralSingularHomology 0
        ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3)) ≃+
      (Fin 2 → ℤ) := by
  let _ := A.ellipticInterior_pathConnected
  let _ := A.cuspAttachmentPiece_pathConnected
  exact ((pathConnectedIntegralHomologyZeroEquivInteger _).prodCongr
    (pathConnectedIntegralHomologyZeroEquivInteger _)).trans integerPairToFinTwoAddEquiv

/-- In the canonical augmentation bases, the actual final degree-zero difference map is the
displayed `Fin 1 → Fin 2` antidiagonal. -/
public theorem cuspAttachment_differenceMap_zero_coordinates
    (x : IntegralSingularHomology 0
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4) ∩
        (A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3 :
          Set A.openEmbeddingStarData.SectionSevenMayerVietorisSpace)) :
    A.cuspAttachmentSidesHomologyZeroEquiv
        (IntegralMayerVietoris.differenceMap
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
          ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3) 0 x) =
      sectionSevenMayerVietorisFinalZeroHom
        (A.cuspAttachmentOverlapHomologyZeroEquiv x) := by
  let _ := A.ellipticInterior_pathConnected
  let _ := A.cuspAttachmentPiece_pathConnected
  let _ := A.cuspAttachmentOverlap_pathConnected
  have hnormal :=
    IntegralMayerVietoris.differenceMap_zero_apply_normalForm
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).stage (2 : Fin 4))
      ((A.openEmbeddingStarData.sectionSevenMayerVietorisCover).piece 3) x
  funext i
  fin_cases i
  · simpa [cuspAttachmentSidesHomologyZeroEquiv, cuspAttachmentOverlapHomologyZeroEquiv,
      integerPairToFinTwoAddEquiv, integerToFinOneAddEquiv,
      sectionSevenMayerVietorisFinalZeroHom] using congrArg Prod.fst hnormal
  · simpa [cuspAttachmentSidesHomologyZeroEquiv, cuspAttachmentOverlapHomologyZeroEquiv,
      integerPairToFinTwoAddEquiv, integerToFinOneAddEquiv,
      sectionSevenMayerVietorisFinalZeroHom] using congrArg Prod.snd hnormal


end Geometry.PaperAnalyticData

end SphereSixComplex
