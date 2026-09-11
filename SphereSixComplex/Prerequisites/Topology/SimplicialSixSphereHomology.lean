module

public import SphereSixComplex.Prerequisites.Topology.SingularStandardSimplexCone
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Low-degree simplicial homology of the boundary of the seven-simplex

The simplicial boundary `∂Δ[7]` is a finite combinatorial model of a six-sphere.  In degrees
below six, prepending the zero vertex remains in the boundary and gives the usual cone
contraction.  This file constructs that cone on Mathlib's actual coproduct chain groups, with an
arbitrary coefficient object in `AddCommGrpCat`.

This computes simplicial homology only.  Identifying the realization of `∂Δ[7]` with the
topological six-sphere and comparing simplicial with singular homology are separate missing
theorems.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- In low degrees, coning a simplex of `∂Δ[7]` to the zero vertex remains in `∂Δ[7]`. -/
public noncomputable def boundarySevenZeroConeSimplex
    (n : ℕ) (hn : n + 1 < 7)
    (x : (∂Δ[7] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (∂Δ[7] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk (n + 1))) :=
  ⟨standardSimplexZeroConeSimplex 7 n x.1, by
    rw [SSet.boundary_obj_eq_univ (n + 1) 7 hn]
    exact Set.mem_univ _⟩

/-- Removing the new cone vertex recovers the original boundary simplex. -/
@[simp]
public theorem boundarySevenZeroConeSimplex_delta_zero
    (n : ℕ) (hn : n + 1 < 7)
    (x : (∂Δ[7] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (∂Δ[7] : SSet.{0}).δ 0 (boundarySevenZeroConeSimplex n hn x) = x := by
  apply Subtype.ext
  exact standardSimplexZeroConeSimplex_delta_zero 7 n x.1

/-- Every later face of a low-degree boundary cone is the cone on the preceding face. -/
@[simp]
public theorem boundarySevenZeroConeSimplex_delta_succ
    (n : ℕ) (hn : n + 2 < 7) (i : Fin (n + 2))
    (x : (∂Δ[7] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk (n + 1)))) :
    (∂Δ[7] : SSet.{0}).δ i.succ
        (boundarySevenZeroConeSimplex (n + 1) hn x) =
      boundarySevenZeroConeSimplex n (by omega)
        ((∂Δ[7] : SSet.{0}).δ i x) := by
  apply Subtype.ext
  exact standardSimplexZeroConeSimplex_delta_succ 7 n i x.1

/-- The zero-vertex cone on low-degree chains of `∂Δ[7]`. -/
public noncomputable def boundarySevenZeroConeComponent
    (R : AddCommGrpCat) (n : ℕ) (hn : n + 1 < 7) :
    ((∂Δ[7] : SSet.{0}).chainComplex R).X n ⟶
      ((∂Δ[7] : SSet.{0}).chainComplex R).X (n + 1) :=
  Sigma.desc (fun x ↦
    (∂Δ[7] : SSet.{0}).ιChainComplex
      (boundarySevenZeroConeSimplex n hn x))

@[reassoc (attr := simp)]
public theorem iota_boundarySevenZeroConeComponent
    (R : AddCommGrpCat) (n : ℕ) (hn : n + 1 < 7)
    (x : (∂Δ[7] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n))) :
    (∂Δ[7] : SSet.{0}).ιChainComplex x ≫
        boundarySevenZeroConeComponent R n hn =
      (∂Δ[7] : SSet.{0}).ιChainComplex
        (boundarySevenZeroConeSimplex n hn x) := by
  apply Sigma.ι_desc

/-- In positive degrees below six, the boundary cone contracts the chain complex of `∂Δ[7]`.
-/
public theorem boundarySevenZeroConeComponent_boundary_succ
    (R : AddCommGrpCat) (n : ℕ) (hn : n + 2 < 7) :
    boundarySevenZeroConeComponent R (n + 1) hn ≫
          ((∂Δ[7] : SSet.{0}).chainComplex R).d (n + 2) (n + 1) +
        ((∂Δ[7] : SSet.{0}).chainComplex R).d (n + 1) n ≫
          boundarySevenZeroConeComponent R n (by omega) =
      𝟙 (((∂Δ[7] : SSet.{0}).chainComplex R).X (n + 1)) := by
  apply (∂Δ[7] : SSet.{0}).chainComplex_hom_ext
  intro x
  simp only [Preadditive.comp_add, Category.comp_id]
  rw [← Category.assoc, iota_boundarySevenZeroConeComponent,
    SSet.ιChainComplex_d]
  rw [← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
  simp only [Preadditive.zsmul_comp, iota_boundarySevenZeroConeComponent]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul,
    boundarySevenZeroConeSimplex_delta_zero,
    boundarySevenZeroConeSimplex_delta_succ, Fin.val_succ, pow_succ]
  rw [add_assoc, ← Finset.sum_add_distrib]
  simp







end SphereSixComplex
