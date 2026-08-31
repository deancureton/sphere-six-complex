module

public import SphereSixComplex.Topology.PaperSectionSevenCanonicalCuspFiberBandCompatibilityCompletion

/-!
# Radial homotopy for the canonical cusp fibre

The selected full-fibre slice is compared with the mapping-torus fibre through the actual
radial homotopy equivalence.  Composing this comparison with the literal restriction of the
cusp-to-elliptic map closes the canonical cusp fibre-to-band square.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set TopologicalSpace
open scoped ContinuousMap

namespace SphereSixComplex.Geometry.PaperAnalyticData

open CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspRadialClutchingConstruction

variable {A : PaperAnalyticData}

namespace SectionSevenEllipticTwoDiscCoverData

private theorem openRadialIntervalProdHomotopyEquiv_apply_snd_completion
    {X : Type} [TopologicalSpace X] {r : ℝ} (hr : 0 < r)
    (p : OpenRadialInterval r × X) :
    openRadialIntervalProdHomotopyEquiv hr p = p.2 := by
  rfl

private theorem totalHomeomorph_actualCuspFullFibreSlice_snd_completion
    (s : ℂ)
    (hs : ‖cuspQ s‖ < A.starCuspWitness.localWitness.radius)
    (y : let G := A.actualCuspRadialClutchingData
      let _ := G.fiberTopology
      G.Fiber) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    (G.totalHomeomorph (actualCuspFullFibreSlice (A := A) s hs y)).2 =
      SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph G.clutching
        (Quotient.mk
          (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid G.clutching)
          (s.re, y)) := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  change (A.actualCuspRadialClutchingData.totalHomeomorph
    (A.actualCuspRadialClutchingData.totalHomeomorph.symm
      (⟨‖cuspQ s‖,
          norm_cuspQ_pos s, hs⟩,
        SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph
          A.actualCuspRadialClutchingData.clutching
          (Quotient.mk
            (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid
              A.actualCuspRadialClutchingData.clutching)
            (s.re, y))))).2 = _
  rw [A.actualCuspRadialClutchingData.totalHomeomorph.apply_symm_apply]

private def circleMappingTorusRealFibreSliceCompletion
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (a : ℝ) :
    C(F, CircleMappingTorus phi) :=
  ⟨fun y ↦ SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi
      (Quotient.mk
        (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid phi) (a, y)),
    (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi).continuous.comp
      (continuous_quot_mk.comp (continuous_const.prodMk continuous_id))⟩

private def circleMappingTorusRealFibreSliceHomotopyCompletion
    {F : Type} [TopologicalSpace F] (phi : F ≃ₜ F) (a : ℝ) :
    ContinuousMap.Homotopy (circleMappingTorusRealFibreSliceCompletion phi a)
      (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) where
  toFun q :=
    SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi
      (Quotient.mk
        (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusSetoid phi)
        ((1 - (q.1 : ℝ)) * a, q.2))
  continuous_toFun :=
    (SphereSixComplex.CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi).continuous.comp
      (continuous_quot_mk.comp
        (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          continuous_const).prodMk continuous_snd))
  map_zero_left x := by
    simp [circleMappingTorusRealFibreSliceCompletion]
  map_one_left x := by
    simpa using realMappingTorusHomeomorph_mk_zero phi x

private theorem actualCuspWangFibreSlice_to_mappingTorus_completion
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    G.totalHomotopyEquiv.toFun.comp
        ((TopologicalSpace.Opens.inclusion' (R.twoDiscCover.cuspOrderThreeOpen ⊓
          R.twoDiscCover.cuspOrderFourOpen)).hom.comp
          (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)) =
      circleMappingTorusRealFibreSliceCompletion G.clutching
        (A.actualCuspAngularLiftPoint (actualCuspFullFibreCrossingTime A)).1.2.re := by
  dsimp
  let _ := A.actualCuspRadialClutchingData.fiberTopology
  ext y
  change openRadialIntervalProdHomotopyEquiv _
    (A.actualCuspRadialClutchingData.totalHomeomorph
      (((TopologicalSpace.Opens.inclusion' _).hom.comp
        (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)) y)) = _
  rw [openRadialIntervalProdHomotopyEquiv_apply_snd_completion]
  change (A.actualCuspRadialClutchingData.totalHomeomorph
    (actualCuspFullFibreSlice (A := A)
      (A.actualCuspAngularLiftPoint (actualCuspFullFibreCrossingTime A)).1.2
      (A.actualCuspAngularLiftPoint (actualCuspFullFibreCrossingTime A)).2 y)).2 = _
  exact totalHomeomorph_actualCuspFullFibreSlice_snd_completion _ _ y

/-- The selected full-fibre slice, followed by the cusp map, is literally the inclusion of its
transport to the elliptic band. -/
public theorem cuspMap_actualCuspWangFibreSlice_eq_bandInclusion
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    R.twoDiscCover.cuspToEllipticInteriorMap.hom.comp
        ((TopologicalSpace.Opens.inclusion' (R.twoDiscCover.cuspOrderThreeOpen ⊓
          R.twoDiscCover.cuspOrderFourOpen)).hom.comp
          (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)) =
      ((⟨Subtype.val, continuous_subtype_val⟩ :
          C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
              Set A.SectionSevenEllipticInterior),
            A.SectionSevenEllipticInterior)).comp
        (actualCuspWangFibreToBandMap (A := A) R)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  apply ContinuousMap.ext
  intro y
  rfl

/-- The oriented low-overlap fibre and the explicit middle-height full-fibre slice define
homotopic maps into the elliptic interior. -/
public theorem actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_homotopic_wangSlice
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      R.twoDiscCover.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap
      ((⟨Subtype.val, continuous_subtype_val⟩ :
          C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
              Set A.SectionSevenEllipticInterior),
            A.SectionSevenEllipticInterior)).comp
        (actualCuspWangFibreToBandMap (A := A) R)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  let slice : C(G.Fiber, puncturedLocalCuspQuotient A.starCuspWitness) :=
    (TopologicalSpace.Opens.inclusion' (R.twoDiscCover.cuspOrderThreeOpen ⊓
      R.twoDiscCover.cuspOrderFourOpen)).hom.comp
      (actualCuspWangFibreToCuspCoverIntersectionMap (A := A) R)
  let a : ℝ :=
    (A.actualCuspAngularLiftPoint (actualCuspFullFibreCrossingTime A)).1.2.re
  let realSlice : C(G.Fiber, CircleMappingTorus G.clutching) :=
    circleMappingTorusRealFibreSliceCompletion G.clutching a
  have hphase : ContinuousMap.Homotopic
      (torusPt (fun _ : Unit ↦ G.clutching) () uQuarter) realSlice := by
    have hquarter : ContinuousMap.Homotopic
        (torusPt (fun _ : Unit ↦ G.clutching) () uQuarter)
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) :=
      ⟨torusPtHomotopy (fun _ : Unit ↦ G.clutching) () uQuarter⟩
    have hreal : ContinuousMap.Homotopic realSlice
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ G.clutching)) :=
      ⟨circleMappingTorusRealFibreSliceHomotopyCompletion G.clutching a⟩
    exact hquarter.trans hreal.symm
  have hradial : ContinuousMap.Homotopic
      (G.totalHomotopyEquiv.invFun.comp
        (torusPt (fun _ : Unit ↦ G.clutching) () uQuarter)) slice := by
    have hto : G.totalHomotopyEquiv.toFun.comp slice = realSlice :=
      actualCuspWangFibreSlice_to_mappingTorus_completion R
    have hphase' := ContinuousMap.Homotopic.comp
      (.refl G.totalHomotopyEquiv.invFun) hphase
    have hreturn : ContinuousMap.Homotopic
        (G.totalHomotopyEquiv.invFun.comp
          (G.totalHomotopyEquiv.toFun.comp slice)) slice := by
      simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
        ContinuousMap.Homotopic.comp G.totalHomotopyEquiv.left_inv (.refl slice)
    rw [← hto] at hphase'
    exact hphase'.trans hreturn
  rw [R.twoDiscCover.actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_eq]
  rw [← cuspMap_actualCuspWangFibreSlice_eq_bandInclusion R]
  exact ContinuousMap.Homotopic.comp
    (.refl R.twoDiscCover.cuspToEllipticInteriorMap.hom) hradial

/-- The actual mapping-torus fibre is homotopic to the explicit full-fibre slice transported
into the elliptic band. -/
public theorem actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_wangSlice
    (R : A.SectionSevenAffineRadialCompletionInput) :
    let G := A.actualCuspRadialClutchingData
    let _ := G.fiberTopology
    ContinuousMap.Homotopic
      R.twoDiscCover.actualCuspMappingTorusFiberToEllipticInteriorMap
      ((⟨Subtype.val, continuous_subtype_val⟩ :
          C((R.twoDiscCover.orderThreeSide ∩ R.twoDiscCover.orderFourSide :
              Set A.SectionSevenEllipticInterior),
            A.SectionSevenEllipticInterior)).comp
        (actualCuspWangFibreToBandMap (A := A) R)) := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact
    R.twoDiscCover.actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_lowOverlap.trans
      (actualCuspMappingTorusLowOverlapFiberToEllipticInteriorMap_homotopic_wangSlice R)

/-- The actual radial cusp model satisfies the canonical cusp fibre-to-band topological
compatibility without an additional marked-coordinate hypothesis. -/
public theorem canonicalCuspFiberBandTopologicalCompatibility
    (R : A.SectionSevenAffineRadialCompletionInput) :
    R.twoDiscCover.CanonicalCuspFiberBandTopologicalCompatibility := by
  let G := A.actualCuspRadialClutchingData
  let _ := G.fiberTopology
  exact
    (actualCuspMappingTorusFiberToEllipticInteriorMap_homotopic_wangSlice R).trans
      (actualCuspWangFibreToEllipticInteriorMap_homotopic_canonical R)

end SectionSevenEllipticTwoDiscCoverData

end SphereSixComplex.Geometry.PaperAnalyticData

end

end
