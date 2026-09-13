module

public import SphereSixComplex.Prerequisites.Topology.FirstHurewiczProof

@[expose] public section
noncomputable section
open Function Set Topology CategoryTheory

namespace SphereSixComplex

open Hurewicz.Chains StandardCircleHomologyLiftDegree

public theorem pairLoop_eq_zero_of_range
    {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z]
    [Subsingleton (IntegralSingularHomology 1 Z)]
    (f : Z → X) (hf : IsEmbedding f) {x y : X} (p : Path x y) (q : Path y x)
    (hp : ∀ t, p t ∈ range f) (hq : ∀ t, q t ∈ range f) :
    loopHomologyClass (p.trans q) = 0 := by
  let e := hf.toHomeomorph
  let : Subsingleton (IntegralSingularHomology 1 (range f)) :=
    (integralSingularHomologyEquiv 1 e).symm.injective.subsingleton
  have hx : x ∈ range f := by simpa using hp 0
  have hy : y ∈ range f := by simpa using hp 1
  let p' : Path (⟨x, hx⟩ : range f) ⟨y, hy⟩ :=
    ⟨⟨fun t ↦ ⟨p t, hp t⟩, p.continuous.subtype_mk _⟩,
      Subtype.ext p.source, Subtype.ext p.target⟩
  let q' : Path (⟨y, hy⟩ : range f) ⟨x, hx⟩ :=
    ⟨⟨fun t ↦ ⟨q t, hq t⟩, q.continuous.subtype_mk _⟩,
      Subtype.ext q.source, Subtype.ext q.target⟩
  have h : loopHomologyClass (p'.trans q') = 0 := Subsingleton.elim _ _
  have hm := congrArg (integralSingularHomologyMap 1
    (⟨Subtype.val, continuous_subtype_val⟩ : C(range f, X))) h
  rw [integralSingularHomologyMap_loopHomologyClass, map_zero] at hm
  have he : (p'.trans q').map continuous_subtype_val = p.trans q := by
    ext t
    simp only [Path.map_trans]
    rfl
  rw [he] at hm
  exact hm

public theorem alternatingHexagonBoundaryPath_homology_zero_of_pairLoops
    {X : Type} [TopologicalSpace X] {x y : X}
    (a c e : Path x y) (b d f : Path y x)
    (ha : loopHomologyClass (a.trans d) = 0)
    (hb : loopHomologyClass (b.trans e) = 0)
    (hc : loopHomologyClass (c.trans f) = 0) :
    loopHomologyClass (((((a.trans b).trans c).trans d).trans e).trans f) = 0 := by
  have ha' := congrArg ((integralChains X).homologyι 1).hom ha
  have hb' := congrArg ((integralChains X).homologyι 1).hom hb
  have hc' := congrArg ((integralChains X).homologyι 1).hom hc
  simp only [homologyι_loopHomologyClass, pathOpchainClass_trans] at ha' hb' hc'
  have ha'' := ha'.trans ((integralChains X).homologyι 1).hom.map_zero
  have hb'' := hb'.trans ((integralChains X).homologyι 1).hom.map_zero
  have hc'' := hc'.trans ((integralChains X).homologyι 1).hom.map_zero
  apply (AddCommGrpCat.mono_iff_injective ((integralChains X).homologyι 1)).mp
    (inferInstance : Mono ((integralChains X).homologyι 1))
  calc
    _ = pathOpchainClass (((((a.trans b).trans c).trans d).trans e).trans f) :=
      homologyι_loopHomologyClass _
    _ = (pathOpchainClass a + pathOpchainClass d) +
        (pathOpchainClass b + pathOpchainClass e) +
        (pathOpchainClass c + pathOpchainClass f) := by
      simp only [pathOpchainClass_trans]
      abel
    _ = 0 := by rw [ha'', hb'', hc'']; simp
    _ = _ := ((integralChains X).homologyι 1).hom.map_zero.symm

end SphereSixComplex
