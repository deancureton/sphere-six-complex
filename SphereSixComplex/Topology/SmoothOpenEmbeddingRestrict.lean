module

public import SphereSixComplex.Topology.SmoothOpenEmbedding

/-!
# Restricting the codomain of a smooth open embedding

An open embedding whose range lies in an open submanifold can be regarded as a smooth open
embedding into that submanifold.  Keeping this construction explicit is useful for collars which
remain wholly inside an away-from-the-seam piece.
-/

@[expose] public section

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Manifold Topology

namespace SphereSixComplex
namespace SmoothOpenEmbedding

universe uE uH uM uN

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} {N : Type uN}
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H N]

/-- The range of an embedding, viewed inside a larger open submanifold containing it. -/
public def restrictedTarget (e : SmoothOpenEmbedding I M N) (U : Opens N)
    (h : (e.target : Set N) ⊆ U) : Opens U where
  carrier := Subtype.val ⁻¹' (e.target : Set N)
  is_open' := e.target.isOpen.preimage continuous_subtype_val

/-- The canonical diffeomorphism between the original range and its nested-open-subset form. -/
public def targetToRestrictedTarget (e : SmoothOpenEmbedding I M N) (U : Opens N)
    (h : (e.target : Set N) ⊆ U) :
    e.target ≃ₘ⟮I, I⟯ restrictedTarget e U h where
  toEquiv :=
    { toFun := fun x ↦ ⟨⟨x.1, h x.2⟩, x.2⟩
      invFun := fun x ↦ ⟨x.1.1, x.2⟩
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        rfl }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (restrictedTarget e U h) _).mp
    apply (ContMDiff.subtypeVal_comp_iff U _).mp
    exact contMDiff_subtype_val (I := I) (U := e.target)
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff e.target _).mp
    exact (contMDiff_subtype_val (I := I) (U := U)).comp
      (contMDiff_subtype_val (I := I) (U := restrictedTarget e U h))

/-- Restrict the codomain of a smooth open embedding to any open submanifold containing its
range. -/
public def codRestrict (e : SmoothOpenEmbedding I M N) (U : Opens N)
    (h : (e.target : Set N) ⊆ U) :
    SmoothOpenEmbedding I M U where
  target := restrictedTarget e U h
  toDiffeomorph := e.toDiffeomorph.trans (targetToRestrictedTarget e U h)

@[simp]
public theorem codRestrict_apply (e : SmoothOpenEmbedding I M N) (U : Opens N)
    (h : (e.target : Set N) ⊆ U) (x : M) :
    ((codRestrict e U h x : U) : N) = e x :=
  rfl

end SmoothOpenEmbedding
end SphereSixComplex
