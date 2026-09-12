/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.LocallyFinite

/-!
# Gluing homeomorphisms along locally finite closed covers

Compatible homeomorphisms on two locally finite closed covers induce a homeomorphism of the
ambient spaces. Quotient maps with the same fibers give the corresponding general construction.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace Topology.IsQuotientMap

/-- Quotient maps out of a common space with identical fibres have homeomorphic targets. -/
public noncomputable def homeomorphOfSameFibers
    {W A B : Type*} [TopologicalSpace W] [TopologicalSpace A] [TopologicalSpace B]
    {f : W → A} {g : W → B} (hf : Topology.IsQuotientMap f)
    (hg : Topology.IsQuotientMap g) (hfg : ∀ x y, f x = f y ↔ g x = g y) : A ≃ₜ B := by
  let cf : C(W, A) := ⟨f, hf.continuous⟩
  let cg : C(W, B) := ⟨g, hg.continuous⟩
  let F := (show IsQuotientMap cf from hf).lift cg (fun _ _ h ↦ (hfg _ _).mp h)
  let G := (show IsQuotientMap cg from hg).lift cf (fun _ _ h ↦ (hfg _ _).mpr h)
  have hF (x : W) : F (f x) = g x := congrArg (fun k : C(W, B) ↦ k x)
    ((show IsQuotientMap cf from hf).lift_comp cg (fun _ _ h ↦ (hfg _ _).mp h))
  have hG (x : W) : G (g x) = f x := congrArg (fun k : C(W, A) ↦ k x)
    ((show IsQuotientMap cg from hg).lift_comp cf (fun _ _ h ↦ (hfg _ _).mpr h))
  exact
    { toFun := F
      invFun := G
      left_inv := by
        intro a
        obtain ⟨x, rfl⟩ := hf.surjective a
        rw [hF, hG]
      right_inv := by
        intro b
        obtain ⟨x, rfl⟩ := hg.surjective b
        rw [hG, hF]
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }

public theorem homeomorphOfSameFibers_apply
    {W A B : Type*} [TopologicalSpace W] [TopologicalSpace A] [TopologicalSpace B]
    {f : W → A} {g : W → B} (hf : Topology.IsQuotientMap f)
    (hg : Topology.IsQuotientMap g) (hfg : ∀ x y, f x = f y ↔ g x = g y)
    (x : W) : homeomorphOfSameFibers hf hg hfg (f x) = g x  := by
  exact congrArg (fun k : C(W, B) ↦ k x)
    ((show IsQuotientMap (⟨f, hf.continuous⟩ : C(W, A)) from hf).lift_comp
      ⟨g, hg.continuous⟩ (fun _ _ h ↦ (hfg _ _).mp h))

end Topology.IsQuotientMap

namespace SphereSixComplex

namespace LocallyFiniteClosedCover

/-- Projection from the disjoint union of a family of subsets. -/
public def projection {ι X : Type*} (A : ι → Set X) (p : Σ i, A i) : X :=
  p.2.1

public theorem continuous_projection {ι X : Type*} [TopologicalSpace X]
    (A : ι → Set X) : Continuous (projection A) :=
  continuous_sigma_iff.mpr fun _ ↦ continuous_subtype_val

public theorem surjective_projection {ι X : Type*} {A : ι → Set X}
    (hcover : ⋃ i, A i = Set.univ) : Function.Surjective (projection A) := by
  intro x
  have hx : x ∈ ⋃ i, A i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  exact ⟨⟨i, x, hi⟩, rfl⟩

/-- Projection from a locally finite closed cover is a closed map. -/
public theorem isClosedMap_projection {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hclosed : ∀ i, IsClosed (A i)) (hloc : LocallyFinite A) :
    IsClosedMap (projection A) := by
  intro S hS
  let F : ι → Set X := fun i ↦
    (Subtype.val : A i → X) '' ((fun x : A i ↦ Sigma.mk i x) ⁻¹' S)
  have hFclosed (i : ι) : IsClosed (F i) :=
    (hclosed i).isClosedMap_subtype_val _ (hS.preimage continuous_sigmaMk)
  have hFsub (i : ι) : F i ⊆ A i := by
    rintro x ⟨a, _, rfl⟩
    exact a.2
  have heq : projection A '' S = ⋃ i, F i := by
    ext x
    constructor
    · rintro ⟨⟨i, a⟩, ha, rfl⟩
      exact Set.mem_iUnion.mpr ⟨i, a, ha, rfl⟩
    · intro hx
      obtain ⟨i, a, ha, rfl⟩ := Set.mem_iUnion.mp hx
      exact ⟨⟨i, a⟩, ha, rfl⟩
  rw [heq]
  exact (hloc.subset hFsub).isClosed_iUnion hFclosed

public theorem isQuotientMap_projection {ι X : Type*} [TopologicalSpace X]
    {A : ι → Set X} (hcover : ⋃ i, A i = Set.univ)
    (hclosed : ∀ i, IsClosed (A i)) (hloc : LocallyFinite A) :
    Topology.IsQuotientMap (projection A) :=
  (isClosedMap_projection hclosed hloc).isQuotientMap (continuous_projection A)
    (surjective_projection hcover)

/-- Homeomorphisms on the members of an indexed cover assemble over the disjoint union. -/
public def sigmaHomeomorph {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y)
    (e : ∀ i, A i ≃ₜ B i) : (Σ i, A i) ≃ₜ (Σ i, B i) where
  toFun p := ⟨p.1, e p.1 p.2⟩
  invFun p := ⟨p.1, (e p.1).symm p.2⟩
  left_inv := by rintro ⟨i, a⟩; simp
  right_inv := by rintro ⟨i, b⟩; simp
  continuous_toFun :=
    continuous_sigma_iff.mpr fun i ↦ continuous_sigmaMk.comp (e i).continuous
  continuous_invFun :=
    continuous_sigma_iff.mpr fun i ↦ continuous_sigmaMk.comp (e i).symm.continuous

/-- Compatible cellwise homeomorphisms on two locally finite closed covers glue to a global
homeomorphism. -/
public noncomputable def homeomorph {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (A : ι → Set X) (B : ι → Set Y)
    (e : ∀ i, A i ≃ₜ B i) (hAcov : ⋃ i, A i = Set.univ)
    (hAcl : ∀ i, IsClosed (A i)) (hAloc : LocallyFinite A)
    (hBcov : ⋃ i, B i = Set.univ) (hBcl : ∀ i, IsClosed (B i))
    (hBloc : LocallyFinite B)
    (hglue : ∀ i j (x : A i) (y : A j),
      (x : X) = (y : X) ↔ (e i x : Y) = (e j y : Y)) : X ≃ₜ Y := by
  let f := projection A
  let g := projection B ∘ sigmaHomeomorph A B e
  have hf : Topology.IsQuotientMap f := isQuotientMap_projection hAcov hAcl hAloc
  have hg : Topology.IsQuotientMap g :=
    (isQuotientMap_projection hBcov hBcl hBloc).comp
      (sigmaHomeomorph A B e).isQuotientMap
  have hfg : ∀ a b, f a = f b ↔ g a = g b := fun a b ↦
    hglue a.1 b.1 a.2 b.2
  exact hf.homeomorphOfSameFibers hg hfg

end LocallyFiniteClosedCover

end SphereSixComplex
