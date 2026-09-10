module

public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.ChartedSpace
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic

/-!
# Manifolds are locally nice

The covering-space form of van Kampen needs the covered space to be locally path connected and
semilocally simply connected.  Both follow from strong local contractibility, which every charted
space over a normed model has, so this file records that implication once:

* `normedSpace_stronglyLocallyContractibleSpace`: balls in a real normed space are convex, hence
  contractible, and they form a neighbourhood basis;
* `stronglyLocallyContractibleSpace_of_open_nhds`: strong local contractibility is a local
  property;
* `ChartedSpace.stronglyLocallyContractibleSpace`: therefore a charted space over a strongly
  locally contractible model is strongly locally contractible;
* `ChartedSpace.semilocallySimplyConnectedSpace`: and so semilocally simply connected, via
  Tau Ceti's implication from local contractibility.
-/

@[expose] public section

open Topology Filter Set

namespace SphereSixComplex

/-- A real normed space is strongly locally contractible: its balls are convex, hence
contractible, and they form a neighbourhood basis. -/
public theorem normedSpace_stronglyLocallyContractibleSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    StronglyLocallyContractibleSpace E :=
  .of_bases (fun _ => Metric.nhds_basis_ball)
    (fun x r hr => Convex.contractibleSpace (_root_.convex_ball x r) ⟨x, Metric.mem_ball_self hr⟩)

/-- Strong local contractibility is a local property: it suffices that every point has an open
neighbourhood which is strongly locally contractible as a subspace. -/
public theorem stronglyLocallyContractibleSpace_of_open_nhds {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ StronglyLocallyContractibleSpace U) :
    StronglyLocallyContractibleSpace X := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hUopen, hxU, hU⟩ := h x
  have hemb : Topology.IsOpenEmbedding ((↑) : U → X) := hUopen.isOpenEmbedding_subtypeVal
  have hmap : 𝓝 x = Filter.map ((↑) : U → X) (𝓝 (⟨x, hxU⟩ : U)) :=
    (hemb.map_nhds_eq ⟨x, hxU⟩).symm
  have hbasis := (StronglyLocallyContractibleSpace.contractible_basis (X := U) ⟨x, hxU⟩).map
    ((↑) : U → X)
  rw [← hmap] at hbasis
  refine hbasis.to_hasBasis' ?_ ?_
  · rintro s ⟨hs, hcontr⟩
    refine ⟨((↑) : U → X) '' s, ⟨?_, ?_⟩, le_rfl⟩
    · rw [hmap]
      exact Filter.image_mem_map hs
    · exact (hemb.toIsEmbedding.homeomorphImage s).contractibleSpace_iff.mp hcontr
  · rintro s ⟨hs, -⟩
    exact hs

/-- A charted space over a strongly locally contractible model is strongly locally contractible:
each chart identifies an open neighbourhood with an open subset of the model. -/
public theorem ChartedSpace.stronglyLocallyContractibleSpace
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [StronglyLocallyContractibleSpace H] : StronglyLocallyContractibleSpace M := by
  refine stronglyLocallyContractibleSpace_of_open_nhds fun x => ?_
  refine ⟨(chartAt H x).source, (chartAt H x).open_source, mem_chart_source H x, ?_⟩
  have htarget : StronglyLocallyContractibleSpace ((chartAt H x).target) :=
    (chartAt H x).open_target.stronglyLocallyContractibleSpace
  exact ((chartAt H x).toHomeomorphSourceTarget).isOpenEmbedding.stronglyLocallyContractibleSpace

/-- A charted space over a strongly locally contractible model is semilocally simply connected. -/
public theorem ChartedSpace.semilocallySimplyConnectedSpace
    {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    [StronglyLocallyContractibleSpace H] : TauCeti.SemilocallySimplyConnectedSpace M := by
  have _ : StronglyLocallyContractibleSpace M :=
    ChartedSpace.stronglyLocallyContractibleSpace (H := H)
  exact TauCeti.SemilocallySimplyConnectedSpace.of_locallyContractibleSpace
    (StronglyLocallyContractibleSpace.locallyContractible)

end SphereSixComplex
