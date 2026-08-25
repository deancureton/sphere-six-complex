module

public import SphereSixComplex.Topology.SingularStandardSimplexCone
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

/-- In degrees `4 → 3 → 2`, the identity of the boundary chain short complex is
null-homotopic. -/
public noncomputable def boundarySevenShortComplexIdentityHomotopyThree
    (R : AddCommGrpCat) :
    let K := (∂Δ[7] : SSet.{0}).chainComplex R
    ShortComplex.Homotopy (𝟙 (K.sc' 4 3 2)) 0 := by
  let K := (∂Δ[7] : SSet.{0}).chainComplex R
  let c1 := boundarySevenZeroConeComponent R 1 (by omega)
  let c2 := boundarySevenZeroConeComponent R 2 (by omega)
  let c3 := boundarySevenZeroConeComponent R 3 (by omega)
  let c4 := boundarySevenZeroConeComponent R 4 (by omega)
  refine
    { h₀ := c4 ≫ K.d 5 4
      h₀_f := ?_
      h₁ := c3
      h₂ := c2
      h₃ := K.d 2 1 ≫ c1
      g_h₃ := ?_
      comm₁ := ?_
      comm₂ := ?_
      comm₃ := ?_ }
  · dsimp
    change (c4 ≫ K.d 5 4) ≫ K.d 4 3 = 0
    rw [Category.assoc, K.d_comp_d, comp_zero]
  ·
    change K.d 3 2 ≫ (K.d 2 1 ≫ c1) = 0
    rw [← Category.assoc, K.d_comp_d, zero_comp]
  · change 𝟙 (K.X 4) = K.d 4 3 ≫ c3 + c4 ≫ K.d 5 4 + 0
    have h := boundarySevenZeroConeComponent_boundary_succ R 3 (by omega)
    rw [add_zero]
    exact (by simpa [add_comm] using h.symm)
  · change 𝟙 (K.X 3) = K.d 3 2 ≫ c2 + c3 ≫ K.d 4 3 + 0
    have h := boundarySevenZeroConeComponent_boundary_succ R 2 (by omega)
    rw [add_zero]
    exact (by simpa [add_comm] using h.symm)
  · change 𝟙 (K.X 2) = K.d 2 1 ≫ c1 + c2 ≫ K.d 3 2 + 0
    have h := boundarySevenZeroConeComponent_boundary_succ R 1 (by omega)
    rw [add_zero]
    exact (by simpa [add_comm] using h.symm)

/-- The degree-three simplicial homology of the combinatorial six-sphere `∂Δ[7]` vanishes,
with arbitrary coefficients in `AddCommGrpCat`. -/
public theorem boundarySeven_simplicialHomology_three_isZero
    (R : AddCommGrpCat) :
    IsZero (((∂Δ[7] : SSet.{0}).chainComplex R).homology 3) := by
  let K := (∂Δ[7] : SSet.{0}).chainComplex R
  rw [← K.exactAt_iff_isZero_homology]
  apply (K.exactAt_iff' (i := 4) (j := 3) (k := 2) (by simp) (by simp)).2
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h := (boundarySevenShortComplexIdentityHomotopyThree R).homologyMap_congr
  simpa only [ShortComplex.homologyMap_id, ShortComplex.homologyMap_zero] using h

/-- In particular, degree-three simplicial homology of `∂Δ[7]` vanishes over `𝔽₂`. -/
public theorem boundarySeven_simplicialHomology_three_zModTwo_isZero :
    IsZero (((∂Δ[7] : SSet.{0}).chainComplex
      (AddCommGrpCat.of (ZMod 2))).homology 3) :=
  boundarySeven_simplicialHomology_three_isZero (AddCommGrpCat.of (ZMod 2))

/-- In degrees `3 → 2 → 1`, the same zero-vertex cone null-homotopes the identity. -/
public noncomputable def boundarySevenShortComplexIdentityHomotopyTwo
    (R : AddCommGrpCat) :
    let K := (∂Δ[7] : SSet.{0}).chainComplex R
    ShortComplex.Homotopy (𝟙 (K.sc' 3 2 1)) 0 := by
  let K := (∂Δ[7] : SSet.{0}).chainComplex R
  let c0 := boundarySevenZeroConeComponent R 0 (by omega)
  let c1 := boundarySevenZeroConeComponent R 1 (by omega)
  let c2 := boundarySevenZeroConeComponent R 2 (by omega)
  let c3 := boundarySevenZeroConeComponent R 3 (by omega)
  refine
    { h₀ := c3 ≫ K.d 4 3
      h₀_f := ?_
      h₁ := c2
      h₂ := c1
      h₃ := K.d 1 0 ≫ c0
      g_h₃ := ?_
      comm₁ := ?_
      comm₂ := ?_
      comm₃ := ?_ }
  · dsimp
    change (c3 ≫ K.d 4 3) ≫ K.d 3 2 = 0
    rw [Category.assoc, K.d_comp_d, comp_zero]
  · change K.d 2 1 ≫ (K.d 1 0 ≫ c0) = 0
    rw [← Category.assoc, K.d_comp_d, zero_comp]
  · change 𝟙 (K.X 3) = K.d 3 2 ≫ c2 + c3 ≫ K.d 4 3 + 0
    have h := boundarySevenZeroConeComponent_boundary_succ R 2 (by omega)
    rw [add_zero]
    exact (by simpa [add_comm] using h.symm)
  · change 𝟙 (K.X 2) = K.d 2 1 ≫ c1 + c2 ≫ K.d 3 2 + 0
    have h := boundarySevenZeroConeComponent_boundary_succ R 1 (by omega)
    rw [add_zero]
    exact (by simpa [add_comm] using h.symm)
  · change 𝟙 (K.X 1) = K.d 1 0 ≫ c0 + c1 ≫ K.d 2 1 + 0
    have h := boundarySevenZeroConeComponent_boundary_succ R 0 (by omega)
    rw [add_zero]
    exact (by simpa [add_comm] using h.symm)

/-- Degree-two simplicial homology of `∂Δ[7]` also vanishes for arbitrary coefficients. -/
public theorem boundarySeven_simplicialHomology_two_isZero
    (R : AddCommGrpCat) :
    IsZero (((∂Δ[7] : SSet.{0}).chainComplex R).homology 2) := by
  let K := (∂Δ[7] : SSet.{0}).chainComplex R
  rw [← K.exactAt_iff_isZero_homology]
  apply (K.exactAt_iff' (i := 3) (j := 2) (k := 1) (by simp) (by simp)).2
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have h := (boundarySevenShortComplexIdentityHomotopyTwo R).homologyMap_congr
  simpa only [ShortComplex.homologyMap_id, ShortComplex.homologyMap_zero] using h

/-- In particular, degree-two simplicial homology of `∂Δ[7]` vanishes over `𝔽₂`. -/
public theorem boundarySeven_simplicialHomology_two_zModTwo_isZero :
    IsZero (((∂Δ[7] : SSet.{0}).chainComplex
      (AddCommGrpCat.of (ZMod 2))).homology 2) :=
  boundarySeven_simplicialHomology_two_isZero (AddCommGrpCat.of (ZMod 2))

end SphereSixComplex
