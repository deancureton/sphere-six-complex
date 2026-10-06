module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.AffineSimplex
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! # Original affine chains and the ordered cone boundary -/

noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Ordered vertices determine their actual coefficient-one affine chain. -/
def affineSingularChain (n : ℕ) (v : Fin (n + 1) → E) : (integralSingularChains E).X n :=
  integralSimplexChain n (affineSingularSimplex n v)

/-- The original alternating boundary deletes each ordered vertex. -/
theorem affineSingularChain_boundary (n : ℕ) (v : Fin (n + 2) → E) :
    (integralSingularChains E).d (n + 1) n (affineSingularChain (n + 1) v) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • affineSingularChain n (v ∘ i.succAbove) := by
  unfold affineSingularChain
  rw [integralSimplexChain_boundary]
  simp only [affineSingularSimplex_face]

/-- Distinct ordered vertex lists give distinct actual affine simplices. -/
theorem affineSingularSimplex_injective (n : ℕ) :
    Function.Injective (affineSingularSimplex (E := E) n) := by
  intro v w h
  have he := congrArg (integralSingularSimplexEquiv n E) h
  change integralSingularSimplexEquiv n E ((integralSingularSimplexEquiv n E).symm
    (affineSimplexMap v)) = integralSingularSimplexEquiv n E
      ((integralSingularSimplexEquiv n E).symm (affineSimplexMap w)) at he
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at he
  funext i
  simpa only [affineSimplexMap_vertex] using congrArg
    (fun F : C(Convexity.StdSimplex ℝ (Fin (n + 1)), E) => F (Convexity.StdSimplex.single i)) he

/-- The actual cone with a new first vertex has the original face as its
zeroth face and the negatively signed cones of the original remaining faces. -/
theorem affineSingularChain_cone_boundary (n : ℕ) (a : E) (v : Fin (n + 2) → E) :
    (integralSingularChains E).d (n + 2) (n + 1)
        (affineSingularChain (n + 2) (Fin.cons a v)) =
      affineSingularChain (n + 1) v -
        ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
          affineSingularChain (n + 1) (Fin.cons a (v ∘ i.succAbove)) := by
  rw [affineSingularChain_boundary, Fin.sum_univ_succ]
  have hzero : Fin.cons a v ∘ (0 : Fin (n + 3)).succAbove = v := by
    funext i
    simp
  rw [hzero]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ,
    Fin.cons_comp_succ_succAbove, pow_succ, mul_neg_one]
  have hn (k : ℤ) (c : (integralSingularChains E).X (n + 1)) : (-k) • c = -(k • c) :=
    neg_zsmul c k
  simp only [hn]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

end DifferentialGeometry.Topology
