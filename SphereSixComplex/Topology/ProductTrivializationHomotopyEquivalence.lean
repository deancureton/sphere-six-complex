module

public import SphereSixComplex.Topology.MapHomotopyEquivalence

/-!
# Homotopy equivalences in product coordinates

This file lifts homotopy equivalences through explicit product trivializations.  The result is
stated for a specified total-space map, so a commuting product-coordinate square proves that the
literal map, rather than merely a conjugate of it, is a homotopy equivalence.
-/

@[expose] public section

open ContinuousMap

namespace SphereSixComplex

universe u v w q r s

variable {X : Type u} {Y : Type v} {Z : Type w} {W : Type q}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W]

/-- The product of two specified homotopy equivalences is a homotopy equivalence carried by the
literal product map. -/
public theorem IsHomotopyEquivalence.prodMap {f : X → Y} {g : Z → W}
    (hf : IsHomotopyEquivalence f) (hg : IsHomotopyEquivalence g) :
    IsHomotopyEquivalence (Prod.map f g) := by
  obtain ⟨ef, rfl⟩ := hf
  obtain ⟨eg, rfl⟩ := hg
  exact ⟨ef.prodCongr eg, rfl⟩

variable {E₁ : Type r} {E₂ : Type s}
variable [TopologicalSpace E₁] [TopologicalSpace E₂]

/-- A map which is a product of homotopy equivalences in explicit source and target
trivializations is itself a homotopy equivalence.  The conclusion remembers the original map
`totalMap`; the commuting-square equality is what identifies it with the conjugated product map.
-/
public theorem isHomotopyEquivalence_of_product_trivializations
    (baseMap : X → Y) (fiberMap : Z → W) (totalMap : E₁ → E₂)
    (sourceTrivialization : E₁ ≃ₜ X × Z) (targetTrivialization : E₂ ≃ₜ Y × W)
    (commutes : targetTrivialization ∘ totalMap =
      Prod.map baseMap fiberMap ∘ sourceTrivialization)
    (hBase : IsHomotopyEquivalence baseMap)
    (hFiber : IsHomotopyEquivalence fiberMap) :
    IsHomotopyEquivalence totalMap := by
  obtain ⟨baseEquiv, hBaseMap⟩ := hBase
  obtain ⟨fiberEquiv, hFiberMap⟩ := hFiber
  let totalEquiv : E₁ ≃ₕ E₂ :=
    sourceTrivialization.toHomotopyEquiv |>.trans
      (baseEquiv.prodCongr fiberEquiv) |>.trans
      targetTrivialization.symm.toHomotopyEquiv
  refine ⟨totalEquiv, ?_⟩
  funext x
  apply targetTrivialization.injective
  change targetTrivialization
      (targetTrivialization.symm
        (baseEquiv (sourceTrivialization x).1, fiberEquiv (sourceTrivialization x).2)) =
    targetTrivialization (totalMap x)
  rw [targetTrivialization.apply_symm_apply, hBaseMap, hFiberMap]
  exact (congrFun commutes x).symm

/-- Identity on the fibre lifts a specified base homotopy equivalence through compatible product
trivializations.  This is the common bundle-inclusion case. -/
public theorem isHomotopyEquivalence_of_product_trivializations_right_id
    (baseMap : X → Y) (totalMap : E₁ → E₂)
    (sourceTrivialization : E₁ ≃ₜ X × Z) (targetTrivialization : E₂ ≃ₜ Y × Z)
    (commutes : targetTrivialization ∘ totalMap =
      Prod.map baseMap id ∘ sourceTrivialization)
    (hBase : IsHomotopyEquivalence baseMap) :
    IsHomotopyEquivalence totalMap :=
  isHomotopyEquivalence_of_product_trivializations baseMap id totalMap
    sourceTrivialization targetTrivialization commutes hBase isHomotopyEquivalence_id

end SphereSixComplex

end
