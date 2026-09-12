module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CompactPhaseCorrection
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspCollar
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public abbrev ClosedPhaseCell (r : ℝ) :=
  constructedPositiveCentralCell r 0 × (Fin 2 → Circle)

public abbrev SingletonPhaseCell (r : ℝ) :=
  positiveSingletonStratum r × (Fin 2 → Circle)

public def closedPhaseCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : ClosedPhaseCell W.localWitness.radius) :
    ActualLocalCuspCentralOrbitQuotient W :=
  effectivePhaseCentralOrbit W p.2 p.1.1

public def singletonPhaseCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : SingletonPhaseCell W.localWitness.radius) :
    ActualLocalCuspCentralOrbitQuotient W :=
  effectivePhaseCentralOrbit W p.2 p.1.1.1

public theorem continuous_closedPhaseCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (closedPhaseCellMap W) := by
  let _ := actualLocalCuspQuotientAction W
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hg : Continuous (fun p : ClosedPhaseCell W.localWitness.radius ↦
      compactTorusEmbedding (effectivePhaseSection p.2)) :=
    continuous_compactTorusEmbedding.comp
      (continuous_effectivePhaseSection.comp continuous_snd)
  have hp : Continuous (fun p : ClosedPhaseCell W.localWitness.radius ↦
      (p.1.1.1.1.1 : constructedModel.Carrier)) := by fun_prop
  simp only [positiveCentralPoint]
  exact Continuous.comp
    (f := fun p : ClosedPhaseCell W.localWitness.radius ↦
      (compactTorusEmbedding (effectivePhaseSection p.2),
        (p.1.1.1.1.1 : constructedModel.Carrier)))
    (g := fun z : DenseTorus × constructedModel.Carrier ↦ constructedModel.torusAction z.1 z.2)
    (continuous_torusAction constructedModel) (hg.prodMk hp)

public theorem isProperMap_closedPhaseCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsProperMap (closedPhaseCellMap W) := by
  let _ : CompactSpace (constructedPositiveCentralCell W.localWitness.radius 0) :=
    (surjective_cellSquareProjection W.localWitness.radius_pos 0).compactSpace
      (continuous_cellSquareProjection W.localWitness.radius_pos 0)
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact (continuous_closedPhaseCellMap W).isProperMap

public theorem continuous_singletonPhaseCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (singletonPhaseCellMap W) := by
  have heq : singletonPhaseCellMap W = closedPhaseCellMap W ∘
      (fun p : SingletonPhaseCell W.localWitness.radius ↦ (p.1.1, p.2)) := rfl
  rw [heq]
  exact (continuous_closedPhaseCellMap W).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

public def singletonPhaseImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.range (singletonPhaseCellMap W)

public theorem closedPhaseCellMap_mem_singletonImage_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : ClosedPhaseCell W.localWitness.radius) :
    closedPhaseCellMap W p ∈ singletonPhaseImage W ↔
      componentSupport constructedModel (p.1.1.1.1.1 : Carrier) = {0} := by
  constructor
  · rintro ⟨s, h⟩
    let _ := actualLocalCuspQuotientAction W
    have hc := actualCentralOrbitRel_componentSupport_ncard_eq W
      (effectivePhaseCentralPoint W s.2 s.1.1.1)
      (effectivePhaseCentralPoint W p.2 p.1.1) (Quotient.exact h)
    rw [effectivePhaseCentralPoint_support,
      effectivePhaseCentralPoint_support, s.1.property] at hc
    have hc' : (componentSupport constructedModel (p.1.1.1.1.1 : Carrier)).ncard = 1 := by
      simpa using hc.symm
    obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hc'
    have h0 : 0 ∈ componentSupport constructedModel (p.1.1.1.1.1 : Carrier) := p.1.property
    rw [hv, Set.mem_singleton_iff] at h0
    simpa [← h0] using hv
  · intro hp
    exact ⟨(⟨p.1, hp⟩, p.2), rfl⟩

public def singletonPhasePreimageHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    SingletonPhaseCell W.localWitness.radius ≃ₜ
      (closedPhaseCellMap W ⁻¹' singletonPhaseImage W) where
  toFun p := ⟨(p.1.1, p.2),
    (closedPhaseCellMap_mem_singletonImage_iff W _).mpr p.1.property⟩
  invFun p := (⟨p.1.1,
    (closedPhaseCellMap_mem_singletonImage_iff W _).mp p.property⟩, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

public def singletonPhaseMapToImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : SingletonPhaseCell W.localWitness.radius) :
    singletonPhaseImage W :=
  ⟨singletonPhaseCellMap W p, Set.mem_range_self p⟩

public theorem isProperMap_singletonPhaseMapToImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsProperMap (singletonPhaseMapToImage W) := by
  have heq : (singletonPhaseImage W).restrictPreimage
      (closedPhaseCellMap W) ∘ singletonPhasePreimageHomeomorph W =
      singletonPhaseMapToImage W := by
    funext p
    apply Subtype.ext
    rfl
  rw [← heq]
  exact ((isProperMap_closedPhaseCellMap W).restrictPreimage
    (singletonPhaseImage W)).comp
      (singletonPhasePreimageHomeomorph W).isProperMap

/-- The parametrized singleton-support image in the actual central quotient is a product with
the effective compact two-torus, with a continuous inverse. -/
public def singletonPhaseHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    SingletonPhaseCell W.localWitness.radius ≃ₜ
      singletonPhaseImage W :=
  (Equiv.ofBijective (singletonPhaseMapToImage W)
    ⟨fun _ _ h ↦ injective_effectivePhaseCentralOrbit_prod W
        (congrArg Subtype.val h),
      fun ⟨_, p, hp⟩ ↦ ⟨p, Subtype.ext hp⟩⟩).toHomeomorphOfContinuousClosed
    ((continuous_singletonPhaseCellMap W).subtype_mk _)
    (isProperMap_singletonPhaseMapToImage W).isClosedMap

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction

end
