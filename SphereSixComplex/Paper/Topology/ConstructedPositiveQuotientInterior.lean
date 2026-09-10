module
public import SphereSixComplex.Prerequisites.Topology.LocalHalfSpaceCoveringCollars
public import SphereSixComplex.Prerequisites.Geometry.QuotientTopology
public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveLocalCollars
public import SphereSixComplex.Paper.Topology.ConstructedA2PositiveQuotientRelativeCWProof

@[expose] public section
noncomputable section
open Set Topology
open scoped NNReal
namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
open SphereSixComplex SphereSixComplex.Periods
open CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge CuspPeriodExpansion
open CuspStraighteningRetraction StandardInfiniteA2ToricModel.Construction
variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

public theorem constructedPositiveQuotientCore_locallyCollared
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    LocallyCollared (ConstructedA2PositiveQuotientCore W) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  let π := PolarHoneycombData.orbitProjection (constructedLocalPositivePart W.localWitness.radius)
  intro z hz
  obtain ⟨q, rfl⟩ := (constructedPositiveDeck_quotientCovering W).surjective z
  have hq : constructedModel.t q.1.1 = 0 := by
    have hpre := constructedPositiveDeck_central_preimage W
    exact Set.ext_iff.mp hpre q |>.mp hz
  let r := W.localWitness.radius
  obtain ⟨a, u, hu⟩ := carrierPositiveChart_jointly_surjective (localPositiveInclusion r q)
  let p := orthantThreeHalfSpaceHomeomorph u
  have hp : carrierPositiveHalfSpaceChart a p = localPositiveInclusion r q := by
    simpa [carrierPositiveHalfSpaceChart, p] using hu
  have hp0 : p.2 = 0 := (carrierPositiveHalfSpaceChart_height_zero a p).mp (by
    rw [hp]
    exact hq)
  let i := localPositiveInclusion r
  let hi := localPositiveInclusion_isOpenEmbedding r
  let f := carrierPositiveHalfSpaceChart a
  let hf := carrierPositiveHalfSpaceChart_isOpenEmbedding a
  let _ : Nonempty (constructedLocalPositivePart r) := ⟨q⟩
  let e := (hf.toOpenPartialHomeomorph f).trans (hi.toOpenPartialHomeomorph i).symm
  have hsource (v : (Fin 2 → ℝ) × ℝ≥0) : v ∈ e.source ↔ f v ∈ range i := by simp [e]
  have he (v : (Fin 2 → ℝ) × ℝ≥0) (hv : v ∈ e.source) : i (e v) = f v := by
    simp only [e, OpenPartialHomeomorph.trans_apply, IsOpenEmbedding.toOpenPartialHomeomorph_apply]
    exact (hi.toOpenPartialHomeomorph i).right_inv (by simpa using (hsource v).mp hv)
  have hxy : f (p.1, 0) = i q := by simpa only [← hp0] using hp
  have hy : (p.1, 0) ∈ e.source := (hsource _).mpr ⟨q, hxy.symm⟩
  have hx : e (p.1, 0) = q := hi.injective ((he _ hy).trans hxy)
  have hb : ∀ v ∈ e.source, π (e v) ∈ ConstructedA2PositiveQuotientCore W ↔ v.2 = 0 := by
    intro v hv
    have hpre := Set.ext_iff.mp (constructedPositiveDeck_central_preimage W) (e v)
    change π (e v) ∈ ConstructedA2PositiveQuotientCore W ↔ _ at hpre
    rw [hpre]
    change constructedModel.t (e v).1.1 = 0 ↔ v.2 = 0
    rw [← carrierPositiveHalfSpaceChart_height_zero a v]
    change carrierHeight (i (e v)).1 = 0 ↔ carrierHeight (f v).1 = 0
    rw [he v hv]
  have h := locallyCollared_of_projected_halfSpaceChart (ConstructedA2PositiveQuotientCore W)
    π (constructedPositiveDeck_quotientCovering W).isCoveringMap.isLocalHomeomorph e p.1 hy hb
  simpa only [hx] using h

public theorem constructedPositiveQuotient_metrizable
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    TopologicalSpace.MetrizableSpace (ConstructedA2PositiveQuotient W) := by
  let _ := normalizedPositiveDeckAction N constructedModel
    (constructedLocalPositivePart W.localWitness.radius)
    (constructedPositiveDeck_mem N W.localWitness.radius)
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (constructedLocalPositivePart W.localWitness.radius) :=
    constructedPositiveDeck_continuous N W.localWitness.radius
  let _ : LocallyCompactSpace (constructedLocalPositivePart W.localWitness.radius) :=
    constructedLocalPositivePart_locallyCompactSpace W.localWitness.radius
  let _ : LocallyCompactSpace (ConstructedA2PositiveQuotient W) :=
    SphereSixComplex.Geometry.orbitQuotient_locallyCompactSpace
  let _ : SecondCountableTopology (ConstructedA2PositiveQuotient W) :=
    SphereSixComplex.Geometry.orbitQuotient_secondCountableTopology
  let _ : T2Space (ConstructedA2PositiveQuotient W) := constructedPositiveDeck_quotient_t2 W
  infer_instance

public def constructedPositiveQuotientInteriorHomotopyEquiv
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContinuousMap.HomotopyEquiv (ConstructedA2PositiveQuotient W)
      ↥((ConstructedA2PositiveQuotientCore W)ᶜ) := by
  let _ := constructedPositiveQuotient_metrizable W
  let c := Classical.choice (LocallyCollared.nonempty_collar (ConstructedA2PositiveQuotientCore W)
    (constructedPositiveQuotientCore_locallyCollared W))
  let w := Classical.choice (c.nonempty_pushWeight (constructedPositiveDeck_orbitCore_isClosed W))
  exact c.interiorHomotopyEquiv w

public theorem constructedPositiveQuotientInteriorHomotopyEquiv_inv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : ↥((ConstructedA2PositiveQuotientCore W)ᶜ)) :
    (constructedPositiveQuotientInteriorHomotopyEquiv W).invFun x = x.1 := rfl

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Established
