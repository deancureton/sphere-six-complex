module

public import ForMathlib.Topology.Collar.OpenPush
public import TauCeti.Geometry.Manifold.Boundary.Collar.Brown

/-!
# Collars of compact locally collared subsets

This specializes Tau Ceti's proof of Brown's collaring theorem to subset inclusions.
Local collars meet the entire boundary only on their zero slices.
-/

@[expose] public section

namespace SphereSixComplex

open Set Topology Function

public def LocallyCollared {X : Type*} [TopologicalSpace X] (B : Set X) : Prop :=
  ∀ x ∈ B, ∃ V : Set X, V ⊆ B ∧ x ∈ V ∧ IsOpen {b : B | b.1 ∈ V} ∧
    ∃ c : OpenTopologicalCollar X V,
      ∀ p, (c.chart p).1 ∈ B → p.2 = openCollarZero

public theorem LocallyCollared.nonempty_collar {X : Type*} [TopologicalSpace X] [T2Space X]
    (B : Set X) [CompactSpace B]
    (hB : LocallyCollared B) :
    Nonempty (OpenTopologicalCollar X B) := by
  have h : TauCeti.IsLocallyCollared (Subtype.val : B → X) := by
    apply TauCeti.isLocallyCollared_iff.mpr
    intro x
    obtain ⟨V, hVB, hxV, hV, c, hc⟩ := hB x x.2
    let U : Set B := {b | b.1 ∈ V}
    let e : U ≃ₜ V :=
      { toFun := fun b ↦ ⟨b.1.1, b.2⟩
        invFun := fun v ↦ ⟨⟨v.1, hVB v.2⟩, v.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
        continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
    let f : U × Ico (0 : ℝ) 1 → X :=
      fun p ↦ (c.chart (e p.1, p.2)).1
    have hf : IsOpenEmbedding f :=
      c.neighborhood.2.isOpenEmbedding_subtypeVal.comp
        (c.chart.isOpenEmbedding.comp (e.prodCongr (Homeomorph.refl _)).isOpenEmbedding)
    refine ⟨U, hV, hxV, f, ⟨hf, ?_⟩, ?_⟩
    · intro u
      exact c.zero (e u)
    · intro p hp
      have hpB : f p ∈ B := by
        obtain ⟨b, hb⟩ := hp
        exact hb ▸ b.2
      have ht := hc (e p.1, p.2) hpB
      exact congrArg Subtype.val ht
  obtain ⟨f, hf⟩ := TauCeti.isCollared_iff.mp (h.isCollared Subtype.val_injective)
  let U : TopologicalSpace.Opens X := ⟨range f, hf.isOpenEmbedding.isOpen_range⟩
  refine ⟨{ neighborhood := U
            chart := hf.isOpenEmbedding.isEmbedding.toHomeomorph
            zero := ?_ }⟩
  intro b
  exact hf.apply_zero b

end SphereSixComplex
