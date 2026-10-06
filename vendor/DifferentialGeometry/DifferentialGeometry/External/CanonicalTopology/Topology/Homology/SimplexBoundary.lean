module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexBasis

@[expose] public section

/-! # Original simplex generators and their alternating boundaries -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module
open scoped Simplicial

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

/-- The coefficient-one chain of the original singular simplex. -/
def integralSimplexChain (n : ℕ) (σ : integralSingularSimplex n X) :
    (integralSingularChains X).X n :=
  (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := integralSingularCoefficients) σ (ULift.up 1)

/-- The actual coproduct generator has exactly one unit coefficient. -/
theorem integralSingularChainRepr_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularChainRepr n X (integralSimplexChain n σ) = Finsupp.single σ 1 := by
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    ((TopCat.toSSet.obj (TopCat.of X)).isColimitChainComplexXCofan integralSingularCoefficients n)
    (ModuleCat.finsuppCoconeIsColimit ℤ (ULift.{u} ℤ) (integralSingularSimplex n X)) ⟨σ⟩
  have he : (integralSingularChainFinsuppIso n X).hom (integralSimplexChain n σ) =
      Finsupp.single σ (ULift.up 1) := congrArg (fun k => k (ULift.up 1)) h
  change Finsupp.mapRange ULift.down (by rfl) ((integralSingularChainFinsuppIso n X).hom
    (integralSimplexChain n σ)) = _
  rw [he, Finsupp.mapRange_single]

/-- The proved basis consists of those same original coefficient-one simplices. -/
theorem integralSingularChainBasis_apply (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularChainBasis n X σ = integralSimplexChain n σ := by
  apply (integralSingularChainRepr n X).injective
  rw [integralSingularChainRepr_simplex]
  exact (integralSingularChainBasis n X).repr_self σ

/-- The original differential is the alternating sum of the original faces. -/
theorem integralSimplexChain_boundary (n : ℕ) (σ : integralSingularSimplex (n + 1) X) :
    (integralSingularChains X).d (n + 1) n (integralSimplexChain (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        integralSimplexChain n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := by
  have h := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
    (R := integralSingularCoefficients) σ
  let ev : (integralSingularCoefficients.{u} ⟶
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex integralSingularCoefficients).X n) →+
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex integralSingularCoefficients).X n :=
    { toFun := fun f => f (ULift.up 1)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev h
  refine he.trans ?_
  refine (map_sum ev _ Finset.univ).trans ?_
  apply Finset.sum_congr rfl
  intro i _
  exact map_zsmul ev _ _

/-- The degree-one boundary is endpoint minus starting point, with the
orientation inherited from the actual alternating-face differential. -/
theorem integralSimplexChain_boundary_one (σ : integralSingularSimplex 1 X) :
    (integralSingularChains X).d 1 0 (integralSimplexChain 1 σ) =
      integralSimplexChain 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) -
        integralSimplexChain 0 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) := by
  simpa [Fin.sum_univ_two, sub_eq_add_neg] using integralSimplexChain_boundary 0 σ

/-- The original degree-two boundary is edge 12 minus edge 02 plus edge 01. -/
theorem integralSimplexChain_boundary_two (σ : integralSingularSimplex 2 X) :
    (integralSingularChains X).d 2 1 (integralSimplexChain 2 σ) =
      integralSimplexChain 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 0 σ) -
        integralSimplexChain 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 1 σ) +
          integralSimplexChain 1 ((TopCat.toSSet.obj (TopCat.of X)).δ 2 σ) := by
  simpa [Fin.sum_univ_succ, Fin.sum_univ_two, sub_eq_add_neg, add_assoc] using
    integralSimplexChain_boundary 1 σ

end DifferentialGeometry.Topology
