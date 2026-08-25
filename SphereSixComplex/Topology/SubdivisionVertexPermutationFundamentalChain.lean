module

public import SphereSixComplex.Topology.SingularBarycentricOuterFaces
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Vertex permutations and barycentric fundamental chains

An arbitrary permutation of the vertices of an ordered simplex is not a morphism of the
representable simplicial set.  After barycentric subdivision it is, however, an order
automorphism of the poset of nonempty vertex subsets.  This file constructs that automorphism
directly in Mathlib's `SimplexCategory.sd` model and computes its action on the explicit signed
maximal-flag fundamental chain.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

/-- Reindex a nonempty finite subset of the vertices by an arbitrary permutation. -/
public noncomputable def nonemptyFiniteChainsVertexPerm {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1)))
    (s : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    NonemptyFiniteChains (ULift.{0} (Fin (n + 1))) where
  finset := s.finset.image (fun i ↦ ULift.up (σ i.down))
  nonempty := Finset.image_nonempty.mpr s.nonempty
  comparable := fun _ _ ↦ le_total _ _

@[simp]
public theorem nonemptyFiniteChainsVertexPerm_finset {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1)))
    (s : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    (nonemptyFiniteChainsVertexPerm σ s).finset =
      s.finset.image (fun i ↦ ULift.up (σ i.down)) :=
  rfl

/-- Vertex reindexing is an order automorphism of the nonempty-subset poset. -/
public noncomputable def nonemptyFiniteChainsVertexPermOrderIso {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    NonemptyFiniteChains (ULift.{0} (Fin (n + 1))) ≃o
      NonemptyFiniteChains (ULift.{0} (Fin (n + 1))) where
  toFun := nonemptyFiniteChainsVertexPerm σ
  invFun := nonemptyFiniteChainsVertexPerm σ.symm
  left_inv s := by
    apply NonemptyFiniteChains.ext
    ext i
    rcases i with ⟨i⟩
    simp [nonemptyFiniteChainsVertexPerm]
  right_inv s := by
    apply NonemptyFiniteChains.ext
    ext i
    rcases i with ⟨i⟩
    simp [nonemptyFiniteChainsVertexPerm]
  map_rel_iff' := by
    intro s t
    change s.finset.image (fun i ↦ ULift.up (σ i.down)) ⊆
        t.finset.image (fun i ↦ ULift.up (σ i.down)) ↔
      s.finset ⊆ t.finset
    constructor
    · intro h i hi
      have himage : ULift.up (σ i.down) ∈
          t.finset.image (fun j ↦ ULift.up (σ j.down)) :=
        h (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp himage
      have hdown : j.down = i.down := σ.injective (ULift.ext_iff.mp hji)
      have hji' : j = i := by
        apply ULift.ext
        exact hdown
      simpa [hji'] using hj
    · intro h
      exact Finset.image_mono _ h

/-- The induced simplicial automorphism of Mathlib's explicit subdivision model. -/
public noncomputable def simplexSubdivisionVertexPermIso {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) ≅
      SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) :=
  PartOrd.nerveFunctor.mapIso
    (PartOrd.Iso.mk (nonemptyFiniteChainsVertexPermOrderIso σ))

/-- The forward simplicial map underlying vertex reindexing. -/
public noncomputable def simplexSubdivisionVertexPermMap {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) ⟶
      SimplexCategory.sd.{0}.obj (SimplexCategory.mk n) :=
  (simplexSubdivisionVertexPermIso σ).hom

/-- Reindexing a prefix subset agrees with left multiplication of its vertex ordering. -/
public theorem nonemptyFiniteChainsVertexPerm_permutationPrefixChain {n : ℕ}
    (σ τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    nonemptyFiniteChainsVertexPerm σ (permutationPrefixChain τ k) =
      permutationPrefixChain (σ * τ) k := by
  apply NonemptyFiniteChains.ext
  change (permutationPrefixFinset τ k).image
      (fun i ↦ ULift.up (σ i.down)) =
    permutationPrefixFinset (σ * τ) k
  unfold permutationPrefixFinset
  rw [Finset.image_image]
  rfl

/-- The subdivision automorphism sends a maximal flag to the left-reindexed maximal flag. -/
public theorem simplexSubdivisionVertexPermMap_permutationMaximalFlagSimplex {n : ℕ}
    (σ τ : Equiv.Perm (Fin (n + 1))) :
    (simplexSubdivisionVertexPermMap σ).app
        (Opposite.op (SimplexCategory.mk n))
        (permutationMaximalFlagSimplex τ) =
      permutationMaximalFlagSimplex (σ * τ) := by
  refine ComposableArrows.ext (fun k ↦ ?_) (fun k hk ↦ ?_)
  · change nonemptyFiniteChainsVertexPerm σ (permutationPrefixChain τ k) =
      permutationPrefixChain (σ * τ) k
    exact nonemptyFiniteChainsVertexPerm_permutationPrefixChain σ τ k
  · apply Subsingleton.elim

/-- The induced chain map multiplies the barycentric fundamental chain by the ordinary sign of
the vertex permutation. -/
public theorem subdividedSimplexFundamentalChain_vertexPerm {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) :
    subdividedSimplexFundamentalChain n ≫
        (SSet.chainComplexMap (simplexSubdivisionVertexPermMap σ)
          (AddCommGrpCat.of ℤ)).f n =
      permutationSignInteger σ • subdividedSimplexFundamentalChain n := by
  rw [subdividedSimplexFundamentalChain, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, SSet.ι_chainComplexMap_f,
    simplexSubdivisionVertexPermMap_permutationMaximalFlagSimplex,
    Finset.smul_sum, smul_smul]
  rw [← Equiv.sum_comp (Equiv.mulLeft σ.symm)]
  apply Finset.sum_congr rfl
  intro τ hτ
  change permutationSignInteger (σ.symm * τ) •
      (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).ιChainComplex
        (permutationMaximalFlagSimplex (σ * (σ.symm * τ))) =
    (permutationSignInteger σ * permutationSignInteger τ) •
      (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).ιChainComplex
        (permutationMaximalFlagSimplex τ)
  have hcancel : σ * (σ.symm * τ) = τ := by
    apply Equiv.ext
    intro i
    exact σ.apply_symm_apply (τ i)
  rw [hcancel]
  rw [permutationSignInteger, permutationSignInteger, permutationSignInteger,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_symm]
  norm_num

/-- In particular an odd vertex permutation negates the barycentric fundamental chain. -/
public theorem subdividedSimplexFundamentalChain_vertexPerm_of_sign_neg {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (hσ : Equiv.Perm.sign σ = -1) :
    subdividedSimplexFundamentalChain n ≫
        (SSet.chainComplexMap (simplexSubdivisionVertexPermMap σ)
          (AddCommGrpCat.of ℤ)).f n =
      -subdividedSimplexFundamentalChain n := by
  rw [subdividedSimplexFundamentalChain_vertexPerm, permutationSignInteger, hσ]
  norm_num

end SphereSixComplex
