module

public import SphereSixComplex.Topology.HexagonBoundaryPathHomology
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Convex.PathConnected

@[expose] public section
noncomputable section
open Set Topology
namespace SphereSixComplex

public def pathInSubset {E : Type*} [TopologicalSpace E] (s : Set E)
    {x y : E} (p : Path x y) (hx : x ∈ s) (hy : y ∈ s) (hp : ∀ t, p t ∈ s) :
    Path (⟨x, hx⟩ : s) ⟨y, hy⟩ where
  toFun t := ⟨p t, hp t⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

public theorem convex_paths_map_homotopic
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace F] {s : Set E} (hs : Convex ℝ s)
    (f : ContinuousMap s F) {x y : E} (p q : Path x y)
    (hx : x ∈ s) (hy : y ∈ s) (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    ((pathInSubset s p hx hy hp).map f.continuous).Homotopic
      ((pathInSubset s q hx hy hq).map f.continuous) := by
  let _ : ContractibleSpace s := hs.contractibleSpace ⟨x, hx⟩
  exact (SimplyConnectedSpace.paths_homotopic
    (pathInSubset s p hx hy hp) (pathInSubset s q hx hy hq)).map f

public theorem convex_paths_homotopic_in_superset
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s u : Set E} (hs : Convex ℝ s) (hsu : s ⊆ u)
    {x y : E} (p q : Path x y) (hx : x ∈ s) (hy : y ∈ s)
    (hp : ∀ t, p t ∈ s) (hq : ∀ t, q t ∈ s) :
    (pathInSubset u p (hsu hx) (hsu hy) (fun t ↦ hsu (hp t))).Homotopic
      (pathInSubset u q (hsu hx) (hsu hy) (fun t ↦ hsu (hq t))) := by
  exact convex_paths_map_homotopic hs
    (⟨fun z ↦ ⟨z.1, hsu z.2⟩, continuous_subtype_val.subtype_mk _⟩ : ContinuousMap s u) p q hx hy hp hq

end SphereSixComplex
