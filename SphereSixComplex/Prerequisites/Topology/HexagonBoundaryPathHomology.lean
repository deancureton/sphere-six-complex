module

public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof

@[expose] public section
noncomputable section
open Function Set Topology CategoryTheory

namespace SphereSixComplex

open Hurewicz.Chains StandardCircleHomologyLiftDegree

public theorem paths_homotopic_of_range_in_embedded_contractible
    {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] [ContractibleSpace Z]
    (f : Z → X) (hf : IsEmbedding f) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ range f) (hq : ∀ t, q t ∈ range f) : p.Homotopic q := by
  let _ : ContractibleSpace (range f) := hf.toHomeomorph.symm.contractibleSpace
  have hx : x ∈ range f := by simpa using hp 0
  have hy : y ∈ range f := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : range f) ⟨y, hy⟩ :=
    ⟨⟨fun t ↦ ⟨p t, hp t⟩, p.continuous.subtype_mk _⟩,
      Subtype.ext p.source, Subtype.ext p.target⟩
  let q' : Path (⟨x, hx⟩ : range f) ⟨y, hy⟩ :=
    ⟨⟨fun t ↦ ⟨q t, hq t⟩, q.continuous.subtype_mk _⟩,
      Subtype.ext q.source, Subtype.ext q.target⟩
  exact (SimplyConnectedSpace.paths_homotopic p' q').map ⟨Subtype.val, continuous_subtype_val⟩

public def hexagonBoundaryPath {X : Type} [TopologicalSpace X] {x y : X}
    (a b c : Path x y) : Path x x :=
  ((((a.trans b.symm).trans c).trans a.symm).trans b).trans c.symm

public theorem hexagonBoundaryPath_homology_zero {X : Type} [TopologicalSpace X] {x y : X}
    (a b c : Path x y) : loopHomologyClass (hexagonBoundaryPath a b c) = 0 := by
  apply (AddCommGrpCat.mono_iff_injective ((integralChains X).homologyι 1)).mp
    (inferInstance : Mono ((integralChains X).homologyι 1))
  calc
    _ = pathOpchainClass (hexagonBoundaryPath a b c) := homologyι_loopHomologyClass _
    _ = 0 := by
      simp only [hexagonBoundaryPath, pathOpchainClass_trans, pathOpchainClass_symm]
      abel
    _ = _ := ((integralChains X).homologyι 1).hom.map_zero.symm

public theorem pairedHexagonBoundaryPath_homology_zero
    {X : Type} [TopologicalSpace X] {x y : X}
    (a b c a' b' c' : Path x y)
    (ha : a.Homotopic a') (hb : b.Homotopic b') (hc : c.Homotopic c') :
    loopHomologyClass (((((a.trans b.symm).trans c).trans a'.symm).trans b').trans c'.symm) = 0 := by
  apply (AddCommGrpCat.mono_iff_injective ((integralChains X).homologyι 1)).mp
    (inferInstance : Mono ((integralChains X).homologyι 1))
  calc
    _ = pathOpchainClass (((((a.trans b.symm).trans c).trans a'.symm).trans b').trans c'.symm) :=
      homologyι_loopHomologyClass _
    _ = 0 := by
      simp only [pathOpchainClass_trans, pathOpchainClass_symm]
      rw [← pathOpchainClass_homotopic ha, ← pathOpchainClass_homotopic hb,
        ← pathOpchainClass_homotopic hc]
      abel
    _ = _ := ((integralChains X).homologyι 1).hom.map_zero.symm

public theorem alternatingHexagonBoundaryPath_homology_zero
    {X : Type} [TopologicalSpace X] {x y : X}
    (a c e : Path x y) (b d f : Path y x)
    (ha : a.Homotopic d.symm) (hb : b.symm.Homotopic e) (hc : c.Homotopic f.symm) :
    loopHomologyClass (((((a.trans b).trans c).trans d).trans e).trans f) = 0 := by
  simpa only [Path.symm_symm] using
    pairedHexagonBoundaryPath_homology_zero a b.symm c d.symm e f.symm ha hb hc

end SphereSixComplex
