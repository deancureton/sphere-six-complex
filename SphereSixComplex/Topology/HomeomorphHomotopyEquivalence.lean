module

public import SphereSixComplex.Topology.MapHomotopyEquivalence

/-!
# Transporting specified homotopy equivalences along homeomorphisms

This file supplies the small amount of bookkeeping needed when a specified map is replaced by
the same map written in homeomorphic source or target coordinates.  Besides proposition-level
closure lemmas, it exposes bundled witnesses whose pointwise behaviour is easy to rewrite.
-/

@[expose] public section

open ContinuousMap

namespace SphereSixComplex

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

namespace IsHomotopyEquivalence

/-- Replace the specified map underlying a homotopy equivalence by an equal function. -/
public theorem congr {f g : X → Y} (hf : IsHomotopyEquivalence f) (hfg : f = g) :
    IsHomotopyEquivalence g := by
  subst g
  exact hf

/-- A chosen bundled witness for a specified homotopy equivalence. -/
public noncomputable def homotopyEquiv {f : X → Y} (hf : IsHomotopyEquivalence f) : X ≃ₕ Y :=
  Classical.choose hf

/-- The chosen bundled witness has the originally specified forward map. -/
@[simp]
public theorem homotopyEquiv_apply {f : X → Y} (hf : IsHomotopyEquivalence f) (x : X) :
    hf.homotopyEquiv x = f x :=
  congrFun (Classical.choose_spec hf) x

/-- Postcompose a chosen homotopy-equivalence witness by a homeomorphism of its target. -/
public noncomputable def postcompHomeomorph {f : X → Y} (hf : IsHomotopyEquivalence f)
    (h : Y ≃ₜ Z) : X ≃ₕ Z :=
  hf.homotopyEquiv.trans h.toHomotopyEquiv

/-- Pointwise description of the witness obtained by postcomposing with a homeomorphism. -/
@[simp]
public theorem postcompHomeomorph_apply {f : X → Y} (hf : IsHomotopyEquivalence f)
    (h : Y ≃ₜ Z) (x : X) :
    hf.postcompHomeomorph h x = h (f x) := by
  change h (hf.homotopyEquiv x) = h (f x)
  rw [homotopyEquiv_apply]

/-- Postcomposition by a homeomorphism preserves a specified homotopy equivalence. -/
public theorem postcomp_homeomorph {f : X → Y} (hf : IsHomotopyEquivalence f)
    (h : Y ≃ₜ Z) : IsHomotopyEquivalence (h ∘ f) := by
  refine ⟨hf.postcompHomeomorph h, ?_⟩
  funext x
  exact hf.postcompHomeomorph_apply h x

/-- Precompose a chosen homotopy-equivalence witness by a homeomorphism of its source. -/
public noncomputable def precompHomeomorph {f : Y → Z} (hf : IsHomotopyEquivalence f)
    (h : X ≃ₜ Y) : X ≃ₕ Z :=
  h.toHomotopyEquiv.trans hf.homotopyEquiv

/-- Pointwise description of the witness obtained by precomposing with a homeomorphism. -/
@[simp]
public theorem precompHomeomorph_apply {f : Y → Z} (hf : IsHomotopyEquivalence f)
    (h : X ≃ₜ Y) (x : X) :
    hf.precompHomeomorph h x = f (h x) := by
  change hf.homotopyEquiv (h x) = f (h x)
  rw [homotopyEquiv_apply]

/-- Precomposition by a homeomorphism preserves a specified homotopy equivalence. -/
public theorem precomp_homeomorph {f : Y → Z} (hf : IsHomotopyEquivalence f)
    (h : X ≃ₜ Y) : IsHomotopyEquivalence (f ∘ h) := by
  refine ⟨hf.precompHomeomorph h, ?_⟩
  funext x
  exact hf.precompHomeomorph_apply h x

/-- Postcomposition by a homeomorphism preserves and reflects specified homotopy equivalences. -/
public theorem postcomp_homeomorph_iff {f : X → Y} (h : Y ≃ₜ Z) :
    IsHomotopyEquivalence (h ∘ f) ↔ IsHomotopyEquivalence f := by
  constructor
  · intro hf
    exact (hf.postcomp_homeomorph h.symm).congr (by
      funext x
      exact h.symm_apply_apply (f x))
  · intro hf
    exact hf.postcomp_homeomorph h

/-- Precomposition by a homeomorphism preserves and reflects specified homotopy equivalences. -/
public theorem precomp_homeomorph_iff {f : Y → Z} (h : X ≃ₜ Y) :
    IsHomotopyEquivalence (f ∘ h) ↔ IsHomotopyEquivalence f := by
  constructor
  · intro hf
    exact (hf.precomp_homeomorph h.symm).congr (by
      funext y
      exact congrArg f (h.apply_symm_apply y))
  · intro hf
    exact hf.precomp_homeomorph h

end IsHomotopyEquivalence

end SphereSixComplex
