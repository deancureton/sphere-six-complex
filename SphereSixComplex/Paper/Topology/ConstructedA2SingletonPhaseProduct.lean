module

public import SphereSixComplex.Paper.Topology.ConstructedA2HoneycombCompactPhaseCorrection
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.InfiniteA2Toric.Construction

variable {E : NormalizedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public abbrev ConstructedA2ClosedPhaseCell (r : ℝ) :=
  constructedPositiveCentralCell r 0 × (Fin 2 → Circle)

public abbrev ConstructedA2SingletonPhaseCell (r : ℝ) :=
  constructedA2PositiveSingletonStratum r × (Fin 2 → Circle)

public def constructedA2ClosedPhaseCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : ConstructedA2ClosedPhaseCell W.localWitness.radius) :
    ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2EffectivePhaseCentralOrbit W p.2 p.1.1

public def constructedA2SingletonPhaseCellMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : ConstructedA2SingletonPhaseCell W.localWitness.radius) :
    ActualLocalCuspCentralOrbitQuotient W :=
  constructedA2EffectivePhaseCentralOrbit W p.2 p.1.1.1

public theorem constructedA2ClosedPhaseCellMap_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedA2ClosedPhaseCellMap W) := by
  let _ := actualLocalCuspQuotientAction W
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hg : Continuous (fun p : ConstructedA2ClosedPhaseCell W.localWitness.radius ↦
      compactTorusEmbedding (constructedA2EffectivePhaseSection p.2)) :=
    continuous_compactTorusEmbedding.comp
      (constructedA2EffectivePhaseSection_continuous.comp continuous_snd)
  have hp : Continuous (fun p : ConstructedA2ClosedPhaseCell W.localWitness.radius ↦
      (p.1.1.1.1.1 : constructedModel.Carrier)) := by fun_prop
  simp only [constructedA2PositiveCentralPoint]
  exact Continuous.comp
    (f := fun p : ConstructedA2ClosedPhaseCell W.localWitness.radius ↦
      (compactTorusEmbedding (constructedA2EffectivePhaseSection p.2),
        (p.1.1.1.1.1 : constructedModel.Carrier)))
    (g := fun z : DenseTorus × constructedModel.Carrier ↦ constructedModel.torusAction z.1 z.2)
    (continuous_torusAction constructedModel) (hg.prodMk hp)

public theorem constructedA2ClosedPhaseCellMap_isProperMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsProperMap (constructedA2ClosedPhaseCellMap W) := by
  let _ : CompactSpace (constructedPositiveCentralCell W.localWitness.radius 0) :=
    (constructedA2CellSquareProjection_surjective W.localWitness.radius_pos 0).compactSpace
      (constructedA2CellSquareProjection_continuous W.localWitness.radius_pos 0)
  let _ : T2Space (ActualLocalCuspFilling W) :=
    SphereSixComplex.Geometry.PaperAnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact (constructedA2ClosedPhaseCellMap_continuous W).isProperMap

public theorem constructedA2SingletonPhaseCellMap_continuous
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (constructedA2SingletonPhaseCellMap W) := by
  have heq : constructedA2SingletonPhaseCellMap W = constructedA2ClosedPhaseCellMap W ∘
      (fun p : ConstructedA2SingletonPhaseCell W.localWitness.radius ↦ (p.1.1, p.2)) := rfl
  rw [heq]
  exact (constructedA2ClosedPhaseCellMap_continuous W).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

public def constructedA2SingletonPhaseImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Set (ActualLocalCuspCentralOrbitQuotient W) :=
  Set.range (constructedA2SingletonPhaseCellMap W)

public theorem constructedA2ClosedPhaseCellMap_mem_singletonImage_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : ConstructedA2ClosedPhaseCell W.localWitness.radius) :
    constructedA2ClosedPhaseCellMap W p ∈ constructedA2SingletonPhaseImage W ↔
      componentSupport constructedModel (p.1.1.1.1.1 : Carrier) = {0} := by
  constructor
  · rintro ⟨s, h⟩
    let _ := actualLocalCuspQuotientAction W
    have hc := constructedA2ActualCentralOrbitRel_componentSupport_ncard_eq W
      (constructedA2EffectivePhaseCentralPoint W s.2 s.1.1.1)
      (constructedA2EffectivePhaseCentralPoint W p.2 p.1.1) (Quotient.exact h)
    rw [constructedA2EffectivePhaseCentralPoint_support,
      constructedA2EffectivePhaseCentralPoint_support, s.1.property] at hc
    have hc' : (componentSupport constructedModel (p.1.1.1.1.1 : Carrier)).ncard = 1 := by
      simpa using hc.symm
    obtain ⟨v, hv⟩ := Set.ncard_eq_one.mp hc'
    have h0 : 0 ∈ componentSupport constructedModel (p.1.1.1.1.1 : Carrier) := p.1.property
    rw [hv, Set.mem_singleton_iff] at h0
    simpa [← h0] using hv
  · intro hp
    exact ⟨(⟨p.1, hp⟩, p.2), rfl⟩

public def constructedA2SingletonPhasePreimageHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ConstructedA2SingletonPhaseCell W.localWitness.radius ≃ₜ
      (constructedA2ClosedPhaseCellMap W ⁻¹' constructedA2SingletonPhaseImage W) where
  toFun p := ⟨(p.1.1, p.2),
    (constructedA2ClosedPhaseCellMap_mem_singletonImage_iff W _).mpr p.1.property⟩
  invFun p := (⟨p.1.1,
    (constructedA2ClosedPhaseCellMap_mem_singletonImage_iff W _).mp p.property⟩, p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

public def constructedA2SingletonPhaseMapToImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : ConstructedA2SingletonPhaseCell W.localWitness.radius) :
    constructedA2SingletonPhaseImage W :=
  ⟨constructedA2SingletonPhaseCellMap W p, Set.mem_range_self p⟩

public theorem constructedA2SingletonPhaseMapToImage_isProperMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsProperMap (constructedA2SingletonPhaseMapToImage W) := by
  have heq : (constructedA2SingletonPhaseImage W).restrictPreimage
      (constructedA2ClosedPhaseCellMap W) ∘ constructedA2SingletonPhasePreimageHomeomorph W =
      constructedA2SingletonPhaseMapToImage W := by
    funext p
    apply Subtype.ext
    rfl
  rw [← heq]
  exact ((constructedA2ClosedPhaseCellMap_isProperMap W).restrictPreimage
    (constructedA2SingletonPhaseImage W)).comp
      (constructedA2SingletonPhasePreimageHomeomorph W).isProperMap

/-- The parametrized singleton-support image in the actual central quotient is a product with
the effective compact two-torus, with a continuous inverse. -/
public def constructedA2SingletonPhaseHomeomorph
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ConstructedA2SingletonPhaseCell W.localWitness.radius ≃ₜ
      constructedA2SingletonPhaseImage W :=
  (Equiv.ofBijective (constructedA2SingletonPhaseMapToImage W)
    ⟨fun _ _ h ↦ constructedA2EffectivePhaseCentralOrbit_jointly_injective W
        (congrArg Subtype.val h),
      fun ⟨_, p, hp⟩ ↦ ⟨p, Subtype.ext hp⟩⟩).toHomeomorphOfContinuousClosed
    ((constructedA2SingletonPhaseCellMap_continuous W).subtype_mk _)
    (constructedA2SingletonPhaseMapToImage_isProperMap W).isClosedMap

end SphereSixComplex.Geometry.InfiniteA2Toric

end
