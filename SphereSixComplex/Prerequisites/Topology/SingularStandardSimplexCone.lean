module

public import SphereSixComplex.Prerequisites.Topology.SingularBarycentricOuterFaces
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# The cone contraction on standard-simplex chains

Prepending the zero vertex defines an extra degeneracy on every standard simplex.  On integral
simplicial chains this is the classical cone operator.  This file constructs it on the actual
coproduct basis used by `SSet.chainComplex` and proves its positive-degree contraction identity.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

/-- Prepend the zero vertex to a simplex of `Δ[m]`. -/
public noncomputable def standardSimplexZeroConeSimplex
    (m n : ℕ)
    (x : (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk (n + 1))) :=
  SSet.stdSimplex.objEquiv.symm
    (SSet.Augmented.StandardSimplex.shift (SSet.stdSimplex.objEquiv x))

/-- Removing the newly prepended zero vertex recovers the original simplex. -/
@[simp]
public theorem standardSimplexZeroConeSimplex_delta_zero
    (m n : ℕ)
    (x : (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (Δ[m] : SSet.{0}).δ 0 (standardSimplexZeroConeSimplex m n x) = x := by
  let ed := SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk m)
  have h := ed.s_comp_δ₀ n
  exact ConcreteCategory.congr_hom h x

/-- Every later face of a cone is the cone on the preceding face. -/
@[simp]
public theorem standardSimplexZeroConeSimplex_delta_succ
    (m n : ℕ) (i : Fin (n + 2))
    (x : (Δ[m] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (Δ[m] : SSet.{0}).δ i.succ (standardSimplexZeroConeSimplex m (n + 1) x) =
      standardSimplexZeroConeSimplex m n ((Δ[m] : SSet.{0}).δ i x) := by
  let ed := SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk m)
  have h := ed.s_comp_δ n i
  exact ConcreteCategory.congr_hom h x



























end SphereSixComplex
