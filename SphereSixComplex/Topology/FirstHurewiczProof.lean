module

public import SphereSixComplex.Topology.EstablishedFirstHurewicz

/-!
# A chain-level proof of the first Hurewicz theorem

This module develops an explicit inverse to the loop-class map using integral singular chains.
It is deliberately not imported by the production graph while the proof is assembled.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap

namespace SphereSixComplex.Topology.FirstHurewiczProof

open SphereSixComplex.StandardCircleHomologyLiftDegree
open SphereSixComplex.Topology.EstablishedFirstHurewicz

def simplexCoordinate (n : ℕ) (i : Fin (n + 1)) : C(Simplex n, unitInterval) where
  toFun s := ⟨s i, stdSimplex.zero_le s i, stdSimplex.le_one s i⟩
  continuous_toFun := ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

theorem simplexFace_one_zero (s : Simplex 1) :
    (simplexFace 1 0 s : Fin 3 → ℝ) = ![0, s 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_self 1 0 s
  · exact simplexFace_apply_succAbove 1 0 s 0
  · exact simplexFace_apply_succAbove 1 0 s 1

theorem simplexFace_one_one (s : Simplex 1) :
    (simplexFace 1 1 s : Fin 3 → ℝ) = ![s 0, 0, s 1] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 1 s 0
  · exact simplexFace_apply_self 1 1 s
  · exact simplexFace_apply_succAbove 1 1 s 1

theorem simplexFace_one_two (s : Simplex 1) :
    (simplexFace 1 2 s : Fin 3 → ℝ) = ![s 0, s 1, 0] := by
  funext k
  fin_cases k
  · exact simplexFace_apply_succAbove 1 2 s 0
  · exact simplexFace_apply_succAbove 1 2 s 1
  · exact simplexFace_apply_self 1 2 s

def concatTime : C(Simplex 2, unitInterval) where
  toFun s :=
    ⟨s 1 / 2 + s 2, by
      have h0 := stdSimplex.zero_le s 0
      have h1 := stdSimplex.zero_le s 1
      have h2 := stdSimplex.zero_le s 2
      have hs := stdSimplex.sum_eq_one s
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
      change s 0 + (s 1 + s 2) = 1 at hs
      constructor <;> linarith⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      ((continuous_apply (1 : Fin 3)).comp continuous_subtype_val).div_const 2 |>.add
        ((continuous_apply (2 : Fin 3)).comp continuous_subtype_val)

def concatSimplex {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) : C(Simplex 2, X) :=
  (p.trans q).toContinuousMap.comp concatTime

theorem concatSimplex_apply {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) (s : Simplex 2) :
    concatSimplex p q s = (p.trans q).extend (s 1 / 2 + s 2) :=
  (Path.extend_apply (p.trans q) (concatTime s).property).symm

@[simp]
theorem concatSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 0) = pathSimplex q := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 0 s) = pathSimplex q s
  rw [concatSimplex_apply]
  have h1 : simplexFace 1 0 s 1 = s 0 := simplexFace_apply_succAbove 1 0 s 0
  have h2 : simplexFace 1 0 s 2 = s 1 := simplexFace_apply_succAbove 1 0 s 1
  rw [h1, h2]
  have hs := stdSimplex.add_eq_one s
  have hnonneg := stdSimplex.zero_le s 1
  rw [Path.extend_trans_of_half_le p q (show 1 / 2 ≤ s 0 / 2 + s 1 by linarith)]
  have he : 2 * (s 0 / 2 + s 1) - 1 = s 1 := by linarith
  rw [he]
  exact Path.extend_apply q (simplexCoordinate 1 1 s).property

@[simp]
theorem concatSimplex_face_one {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 1) = pathSimplex (p.trans q) := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 1 s) = pathSimplex (p.trans q) s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h2 : simplexFace 1 1 s 2 = s 1 := simplexFace_apply_succAbove 1 1 s 1
  rw [h2, zero_div, zero_add]
  exact Path.extend_apply (p.trans q) (simplexCoordinate 1 1 s).property

@[simp]
theorem concatSimplex_face_two {X : Type*} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) :
    (concatSimplex p q).comp (simplexFace 1 2) = pathSimplex p := by
  apply ContinuousMap.ext
  intro s
  change concatSimplex p q (simplexFace 1 2 s) = pathSimplex p s
  rw [concatSimplex_apply, simplexFace_apply_self]
  have h1 : simplexFace 1 2 s 1 = s 1 := simplexFace_apply_succAbove 1 2 s 1
  rw [h1, add_zero]
  have hle := stdSimplex.le_one s 1
  rw [Path.extend_trans_of_le_half p q (show s 1 / 2 ≤ 1 / 2 by linarith)]
  rw [show 2 * (s 1 / 2) = s 1 by ring]
  exact Path.extend_apply p (simplexCoordinate 1 1 s).property

def lowerTriangleMap : C(Simplex 2, unitInterval × unitInterval) where
  toFun s := (simplexCoordinate 2 2 s, unitInterval.symm (simplexCoordinate 2 0 s))
  continuous_toFun :=
    (simplexCoordinate 2 2).continuous.prodMk
      (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous)

def upperTriangleMap : C(Simplex 2, unitInterval × unitInterval) where
  toFun s := (unitInterval.symm (simplexCoordinate 2 0 s), simplexCoordinate 2 2 s)
  continuous_toFun :=
    (unitInterval.continuous_symm.comp (simplexCoordinate 2 0).continuous).prodMk
      (simplexCoordinate 2 2).continuous

theorem lowerTriangle_face_zero (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 0 s) = (simplexCoordinate 1 1 s, 1) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring

theorem lowerTriangle_face_one (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 1 s) =
      (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

theorem lowerTriangle_face_two (s : Simplex 1) :
    lowerTriangleMap (simplexFace 1 2 s) = (0, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]

theorem upperTriangle_face_zero (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 0 s) = (1, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 0 s 0 = 1
    rw [simplexFace_apply_self]
    ring
  · change simplexFace 1 0 s 2 = s 1
    exact congrFun (simplexFace_one_zero s) 2

theorem upperTriangle_face_one (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 1 s) =
      (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 1 s 0 = s 1
    have h0 : simplexFace 1 1 s 0 = s 0 := congrFun (simplexFace_one_one s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 1 s 2 = s 1
    exact congrFun (simplexFace_one_one s) 2

theorem upperTriangle_face_two (s : Simplex 1) :
    upperTriangleMap (simplexFace 1 2 s) = (simplexCoordinate 1 1 s, 0) := by
  apply Prod.ext <;> apply Subtype.ext
  · change 1 - simplexFace 1 2 s 0 = s 1
    have h0 : simplexFace 1 2 s 0 = s 0 := congrFun (simplexFace_one_two s) 0
    rw [h0]
    linarith [stdSimplex.add_eq_one s]
  · change simplexFace 1 2 s 2 = 0
    exact simplexFace_apply_self 1 2 s

def homotopyLowerSimplex {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp lowerTriangleMap

def homotopyUpperSimplex {X : Type*} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : C(Simplex 2, X) :=
  H.toHomotopy.toContinuousMap.comp upperTriangleMap

def homotopyDiagonalSimplex {X : Type*} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : C(Simplex 1, X) where
  toFun s := H (simplexCoordinate 1 1 s, simplexCoordinate 1 1 s)
  continuous_toFun := H.continuous.comp
    ((simplexCoordinate 1 1).continuous.prodMk (simplexCoordinate 1 1).continuous)

@[simp]
theorem homotopyLowerSimplex_face_zero {X : Type*} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 0) =
      ContinuousMap.const (Simplex 1) y := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 0 s)) = y
  rw [lowerTriangle_face_zero, H.target]

@[simp]
theorem homotopyLowerSimplex_face_one {X : Type*} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 1 s)) = _
  rw [lowerTriangle_face_one]
  rfl

@[simp]
theorem homotopyLowerSimplex_face_two {X : Type*} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyLowerSimplex H).comp (simplexFace 1 2) = pathSimplex p := by
  apply ContinuousMap.ext
  intro s
  change H (lowerTriangleMap (simplexFace 1 2 s)) = pathSimplex p s
  rw [lowerTriangle_face_two]
  exact H.map_zero_left _

@[simp]
theorem homotopyUpperSimplex_face_zero {X : Type*} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 0) = pathSimplex q := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 0 s)) = pathSimplex q s
  rw [upperTriangle_face_zero]
  exact H.map_one_left _

@[simp]
theorem homotopyUpperSimplex_face_one {X : Type*} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 1) = homotopyDiagonalSimplex H := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 1 s)) = _
  rw [upperTriangle_face_one]
  rfl

@[simp]
theorem homotopyUpperSimplex_face_two {X : Type*} [TopologicalSpace X]
    {x y : X} {p q : Path x y} (H : p.Homotopy q) :
    (homotopyUpperSimplex H).comp (simplexFace 1 2) =
      ContinuousMap.const (Simplex 1) x := by
  apply ContinuousMap.ext
  intro s
  change H (upperTriangleMap (simplexFace 1 2 s)) = x
  rw [upperTriangle_face_two, H.source]

def concatChain {X : Type} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) : Chains X 2 :=
  simplexChain X 2 (concatSimplex p q)

theorem boundaryTwo_concatChain {X : Type} [TopologicalSpace X] {x y z : X}
    (p : Path x y) (q : Path y z) :
    boundaryTwo X (concatChain p q) = pathChain q - pathChain (p.trans q) + pathChain p := by
  rw [concatChain, boundaryTwo_simplex, concatSimplex_face_zero, concatSimplex_face_one,
    concatSimplex_face_two]
  rfl

def constantEdgeChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 1 :=
  simplexChain X 1 (ContinuousMap.const (Simplex 1) x)

def constantTriangleChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 2 :=
  simplexChain X 2 (ContinuousMap.const (Simplex 2) x)

theorem boundaryTwo_constantTriangleChain {X : Type} [TopologicalSpace X] (x : X) :
    boundaryTwo X (constantTriangleChain x) = constantEdgeChain x := by
  rw [constantTriangleChain, boundaryTwo_simplex]
  change constantEdgeChain x - constantEdgeChain x + constantEdgeChain x = _
  abel

@[simp]
theorem pathChain_refl {X : Type} [TopologicalSpace X] (x : X) :
    pathChain (Path.refl x) = constantEdgeChain x :=
  rfl

def homotopyChain {X : Type} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (H : p.Homotopy q) : Chains X 2 :=
  simplexChain X 2 (homotopyLowerSimplex H) -
    simplexChain X 2 (homotopyUpperSimplex H)

theorem boundaryTwo_homotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (homotopyChain H) =
      pathChain p - pathChain q + constantEdgeChain y - constantEdgeChain x := by
  rw [homotopyChain, map_sub, boundaryTwo_simplex, boundaryTwo_simplex,
    homotopyLowerSimplex_face_zero, homotopyLowerSimplex_face_one,
    homotopyLowerSimplex_face_two, homotopyUpperSimplex_face_zero,
    homotopyUpperSimplex_face_one, homotopyUpperSimplex_face_two]
  change
    constantEdgeChain y - simplexChain X 1 (homotopyDiagonalSimplex H) + pathChain p -
        (pathChain q - simplexChain X 1 (homotopyDiagonalSimplex H) + constantEdgeChain x) = _
  abel

def correctedHomotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) : Chains X 2 :=
  homotopyChain H - constantTriangleChain y + constantTriangleChain x

theorem boundaryTwo_correctedHomotopyChain {X : Type} [TopologicalSpace X] {x y : X}
    {p q : Path x y} (H : p.Homotopy q) :
    boundaryTwo X (correctedHomotopyChain H) = pathChain p - pathChain q := by
  rw [correctedHomotopyChain, map_add, map_sub, boundaryTwo_homotopyChain,
    boundaryTwo_constantTriangleChain, boundaryTwo_constantTriangleChain]
  abel

def chainHomologyClass {X : Type} [TopologicalSpace X]
    (c : Chains X 1) (hc : boundaryOne X c = 0) : IntegralSingularHomology 1 X :=
  ((IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by
      apply AddCommGrpCat.int_hom_ext
      simpa using hc) ≫
    (IntegralChains X).homologyπ 1) 1

theorem chainHomologyClass_eq_zero_of_boundary {X : Type} [TopologicalSpace X]
    (c : Chains X 1) (hc : boundaryOne X c = 0) (b : Chains X 2)
    (hb : boundaryTwo X b = c) : chainHomologyClass c hc = 0 := by
  have h := (IntegralChains X).liftCycles_homologyπ_eq_zero_of_boundary
    (AddCommGrpCat.asHom c) 0 (by simp) (AddCommGrpCat.asHom b) (by
      apply AddCommGrpCat.int_hom_ext
      simpa using hb.symm)
  have h1 := ConcreteCategory.congr_hom h (1 : ℤ)
  exact h1

theorem chainHomologyClass_sub {X : Type} [TopologicalSpace X]
    (c d : Chains X 1) (hc : boundaryOne X c = 0) (hd : boundaryOne X d = 0) :
    chainHomologyClass (c - d) (by rw [map_sub, hc, hd, sub_zero]) =
      chainHomologyClass c hc - chainHomologyClass d hd := by
  change
    ((IntegralChains X).liftCycles (AddCommGrpCat.asHom (c - d)) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simp [hc, hd]) ≫
        (IntegralChains X).homologyπ 1) 1 =
      ((IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by
            apply AddCommGrpCat.int_hom_ext
            simpa using hc) ≫
          (IntegralChains X).homologyπ 1) 1 -
        ((IntegralChains X).liftCycles (AddCommGrpCat.asHom d) 0 (by simp) (by
            apply AddCommGrpCat.int_hom_ext
            simpa using hd) ≫
          (IntegralChains X).homologyπ 1) 1
  have hLift :
      (IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simpa using hc) -
        (IntegralChains X).liftCycles (AddCommGrpCat.asHom d) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simpa using hd) =
      (IntegralChains X).liftCycles (AddCommGrpCat.asHom (c - d)) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simp [hc, hd]) := by
    rw [← cancel_mono ((IntegralChains X).iCycles 1),
      CategoryTheory.Preadditive.sub_comp]
    simp only [HomologicalComplex.liftCycles_i]
    apply AddCommGrpCat.int_hom_ext
    simp
  have hComp := congrArg
    (fun f => f ≫ (IntegralChains X).homologyπ 1) hLift
  rw [CategoryTheory.Preadditive.sub_comp] at hComp
  have hEval := ConcreteCategory.congr_hom hComp (1 : ℤ)
  symm
  simpa only [AddCommGrpCat.comp_apply, AddCommGrpCat.hom_sub,
    AddMonoidHom.sub_apply] using hEval

theorem chainHomologyClass_add {X : Type} [TopologicalSpace X]
    (c d : Chains X 1) (hc : boundaryOne X c = 0) (hd : boundaryOne X d = 0) :
    chainHomologyClass (c + d) (by rw [map_add, hc, hd, add_zero]) =
      chainHomologyClass c hc + chainHomologyClass d hd := by
  change
    ((IntegralChains X).liftCycles (AddCommGrpCat.asHom (c + d)) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simp [hc, hd]) ≫
        (IntegralChains X).homologyπ 1) 1 =
      ((IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by
            apply AddCommGrpCat.int_hom_ext
            simpa using hc) ≫
          (IntegralChains X).homologyπ 1) 1 +
        ((IntegralChains X).liftCycles (AddCommGrpCat.asHom d) 0 (by simp) (by
            apply AddCommGrpCat.int_hom_ext
            simpa using hd) ≫
          (IntegralChains X).homologyπ 1) 1
  have hLift :
      (IntegralChains X).liftCycles (AddCommGrpCat.asHom c) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simpa using hc) +
        (IntegralChains X).liftCycles (AddCommGrpCat.asHom d) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simpa using hd) =
      (IntegralChains X).liftCycles (AddCommGrpCat.asHom (c + d)) 0 (by simp) (by
          apply AddCommGrpCat.int_hom_ext
          simp [hc, hd]) := by
    rw [← cancel_mono ((IntegralChains X).iCycles 1),
      CategoryTheory.Preadditive.add_comp]
    simp only [HomologicalComplex.liftCycles_i]
    apply AddCommGrpCat.int_hom_ext
    simp
  have hComp := congrArg
    (fun f => f ≫ (IntegralChains X).homologyπ 1) hLift
  rw [CategoryTheory.Preadditive.add_comp] at hComp
  have hEval := ConcreteCategory.congr_hom hComp (1 : ℤ)
  symm
  simpa only [AddCommGrpCat.comp_apply, AddCommGrpCat.hom_add,
    AddMonoidHom.add_apply] using hEval

theorem loopHomologyClass_eq_chainHomologyClass {X : Type} [TopologicalSpace X]
    {x : X} (p : Path x x) :
    loopHomologyClass p = chainHomologyClass (pathChain p) (boundaryOne_loop p) := by
  rfl

theorem loopHomologyClass_homotopic {X : Type} [TopologicalSpace X] {x : X}
    {p q : Path x x} (H : p.Homotopy q) :
    loopHomologyClass p = loopHomologyClass q := by
  rw [loopHomologyClass_eq_chainHomologyClass,
    loopHomologyClass_eq_chainHomologyClass]
  have hzero := chainHomologyClass_eq_zero_of_boundary
    (pathChain p - pathChain q)
    (by rw [map_sub, boundaryOne_loop, boundaryOne_loop, sub_zero])
    (correctedHomotopyChain H) (boundaryTwo_correctedHomotopyChain H)
  rw [chainHomologyClass_sub (pathChain p) (pathChain q)
    (boundaryOne_loop p) (boundaryOne_loop q)] at hzero
  exact sub_eq_zero.mp hzero

theorem loopHomologyClass_refl {X : Type} [TopologicalSpace X] (x : X) :
    loopHomologyClass (Path.refl x) = 0 := by
  rw [loopHomologyClass_eq_chainHomologyClass]
  exact chainHomologyClass_eq_zero_of_boundary
    (pathChain (Path.refl x)) (boundaryOne_loop (Path.refl x))
    (constantTriangleChain x) (boundaryTwo_constantTriangleChain x)

theorem loopHomologyClass_trans {X : Type} [TopologicalSpace X] {x : X}
    (p q : Path x x) :
    loopHomologyClass (p.trans q) = loopHomologyClass p + loopHomologyClass q := by
  rw [loopHomologyClass_eq_chainHomologyClass,
    loopHomologyClass_eq_chainHomologyClass,
    loopHomologyClass_eq_chainHomologyClass]
  have hzero := chainHomologyClass_eq_zero_of_boundary
    (pathChain p + pathChain q - pathChain (p.trans q))
    (by simp only [map_sub, map_add, boundaryOne_loop, add_zero, sub_zero])
    (concatChain p q) (by rw [boundaryTwo_concatChain]; abel)
  rw [chainHomologyClass_sub (pathChain p + pathChain q)
      (pathChain (p.trans q))
      (by rw [map_add, boundaryOne_loop, boundaryOne_loop, add_zero])
      (boundaryOne_loop (p.trans q)),
    chainHomologyClass_add (pathChain p) (pathChain q)
      (boundaryOne_loop p) (boundaryOne_loop q)] at hzero
  exact eq_of_sub_eq_zero hzero |>.symm

theorem loopHomologyClass_homotopic' {X : Type} [TopologicalSpace X] {x : X}
    {p q : Path x x} (h : p.Homotopic q) :
    loopHomologyClass p = loopHomologyClass q := by
  obtain ⟨H⟩ := h
  exact loopHomologyClass_homotopic H

theorem loopClass_trans {X : Type} [TopologicalSpace X] {b : X}
    (p q : Path b b) : loopClass (p.trans q) = loopClass p + loopClass q := by
  rw [loopClass, Path.Homotopic.Quotient.mk_trans]
  change Additive.ofMul
    (Abelianization.of
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q) *
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))) = _
  rw [map_mul, ofMul_mul, add_comm]
  rfl

@[simp]
theorem loopClass_symm {X : Type} [TopologicalSpace X] {b : X} (p : Path b b) :
    loopClass p.symm = -loopClass p := by
  rw [loopClass, Path.Homotopic.Quotient.mk_symm]
  change Additive.ofMul
    (Abelianization.of
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))⁻¹) = _
  rw [map_inv, ofMul_inv]
  rfl

def hurewiczFunction {X : Type} [TopologicalSpace X] (b : X) :
    FundamentalGroup X b → IntegralSingularHomology 1 X :=
  Quotient.lift (fun p : Path b b ↦ loopHomologyClass p)
    (fun _ _ h ↦ loopHomologyClass_homotopic' h)

def hurewiczPi1 {X : Type} [TopologicalSpace X] (b : X) :
    FundamentalGroup X b →* Multiplicative (IntegralSingularHomology 1 X) where
  toFun g := Multiplicative.ofAdd (hurewiczFunction b g)
  map_one' := congrArg Multiplicative.ofAdd (loopHomologyClass_refl b)
  map_mul' g h := by
    obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective g
    obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective h
    change Multiplicative.ofAdd (loopHomologyClass (q.trans p)) =
      Multiplicative.ofAdd (loopHomologyClass p + loopHomologyClass q)
    rw [loopHomologyClass_trans, add_comm]

def hurewiczMap {X : Type} [TopologicalSpace X] (b : X) :
    AbelianPi1 X b →ₗ[ℤ] IntegralSingularHomology 1 X where
  toFun := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft
  map_add' := (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft.map_add
  map_smul' n a := by
    exact map_intCast_smul
      (Abelianization.lift (hurewiczPi1 b)).toAdditiveLeft ℤ ℤ n a

@[simp]
theorem hurewiczMap_loopClass {X : Type} [TopologicalSpace X] (b : X)
    (p : Path b b) : hurewiczMap b (loopClass p) = loopHomologyClass p := by
  rfl

def chainLiftTo (X : Type) [TopologicalSpace X] (n : ℕ) (A : Type)
    [AddCommGroup A] (f : SingularSimplex X n → A) : Chains X n →+ A :=
  (Sigma.desc
    (fun s : (TopCat.toSSet.obj (TopCat.of X)).obj
        (Opposite.op (SimplexCategory.mk n)) ↦
      AddCommGrpCat.ofHom
        (zmultiplesHom A
          (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n)) s)))) :
    Chains X n ⟶ AddCommGrpCat.of A).hom

@[simp]
theorem chainLiftTo_simplex (X : Type) [TopologicalSpace X] (n : ℕ)
    (A : Type) [AddCommGroup A] (f : SingularSimplex X n → A)
    (s : SingularSimplex X n) :
    chainLiftTo X n A f (simplexChain X n s) = f s := by
  have h := Sigma.ι_desc
    (fun t : (TopCat.toSSet.obj (TopCat.of X)).obj
        (Opposite.op (SimplexCategory.mk n)) ↦
      AddCommGrpCat.ofHom
        (zmultiplesHom A
          (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n)) t))))
    (simplexIndex X n s)
  have he := congrArg (fun g : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of A ↦ g.hom 1) h
  change chainLiftTo X n A f (simplexChain X n s) =
    zmultiplesHom A
      (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n))
        (simplexIndex X n s))) 1 at he
  simpa [simplexIndex] using he

theorem chainHomTo_ext (X : Type) [TopologicalSpace X] (n : ℕ)
    (A : Type) [AddCommGroup A] {f g : Chains X n →+ A}
    (h : ∀ s : SingularSimplex X n,
      f (simplexChain X n s) = g (simplexChain X n s)) : f = g := by
  have hcat : (AddCommGrpCat.ofHom f : Chains X n ⟶ AddCommGrpCat.of A) =
      AddCommGrpCat.ofHom g := by
    apply SSet.chainComplex_hom_ext
    intro s
    apply AddCommGrpCat.int_hom_ext
    change f (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := AddCommGrpCat.of ℤ) s).hom 1) =
      g (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := AddCommGrpCat.of ℤ) s).hom 1)
    simpa [simplexChain, simplexIndex] using
      h ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n)) s)
  exact congrArg AddCommGrpCat.Hom.hom hcat

def basedLoop {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ z : X, Path b z) (p : Path x y) : Path b b :=
  (r x).trans (p.trans (r y).symm)

def basedLoopQuotient {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ z : X, Path b z) (p : Path x y) : FundamentalGroup X b :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (basedLoop r p))

def basedLoopClass {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ z : X, Path b z) (p : Path x y) : AbelianPi1 X b :=
  loopClass (basedLoop r p)

theorem basedLoopQuotient_trans {X : Type} [TopologicalSpace X] {b x y z : X}
    (r : ∀ a : X, Path b a) (p : Path x y) (q : Path y z) :
    basedLoopQuotient r (p.trans q) =
      basedLoopQuotient r q * basedLoopQuotient r p := by
  simp only [basedLoopQuotient, basedLoop, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk (r y)).symm (Path.Homotopic.Quotient.mk (r y)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

theorem basedLoopClass_trans {X : Type} [TopologicalSpace X] {b x y z : X}
    (r : ∀ a : X, Path b a) (p : Path x y) (q : Path y z) :
    basedLoopClass r (p.trans q) = basedLoopClass r p + basedLoopClass r q := by
  change Additive.ofMul (Abelianization.of (basedLoopQuotient r (p.trans q))) = _
  rw [basedLoopQuotient_trans, map_mul, ofMul_mul, add_comm]
  rfl

theorem basedLoop_homotopic {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ a : X, Path b a) {p q : Path x y} (h : p.Homotopic q) :
    (basedLoop r p).Homotopic (basedLoop r q) :=
  (Path.Homotopic.refl (r x)).hcomp
    (h.hcomp (Path.Homotopic.refl (r y).symm))

theorem basedLoopClass_homotopic {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ a : X, Path b a) {p q : Path x y} (h : p.Homotopic q) :
    basedLoopClass r p = basedLoopClass r q := by
  apply congrArg (fun g : FundamentalGroup X b ↦
    Additive.ofMul (Abelianization.of g))
  apply Path.Homotopic.Quotient.eq.mpr
  exact basedLoop_homotopic r h

theorem basedLoopClass_triangle {X : Type} [TopologicalSpace X] {b x y z : X}
    (r : ∀ a : X, Path b a) (p₀₁ : Path x y) (p₁₂ : Path y z)
    (p₀₂ : Path x z) (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₀₁ + basedLoopClass r p₁₂ = basedLoopClass r p₀₂ := by
  rw [← basedLoopClass_trans]
  exact basedLoopClass_homotopic r h

theorem basedLoopClass_triangle_boundary {X : Type} [TopologicalSpace X]
    {b x y z : X} (r : ∀ a : X, Path b a) (p₀₁ : Path x y)
    (p₁₂ : Path y z) (p₀₂ : Path x z)
    (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopClass r p₁₂ - basedLoopClass r p₀₂ + basedLoopClass r p₀₁ = 0 := by
  rw [← basedLoopClass_triangle r p₀₁ p₁₂ p₀₂ h]
  abel

@[simp]
theorem basedLoopClass_loop {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ a : X, Path b a) (p : Path b b) : basedLoopClass r p = loopClass p := by
  rw [basedLoopClass, basedLoop, loopClass_trans, loopClass_trans, loopClass_symm]
  abel

theorem basedLoopClass_cast {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ a : X, Path b a) (p : Path x y) {x' y' : X}
    (hx : x' = x) (hy : y' = y) :
    basedLoopClass r (p.cast hx hy) = basedLoopClass r p := by
  cases hx
  cases hy
  rfl

theorem basedLoopClass_triangleFacePath {X : Type} [TopologicalSpace X]
    {b : X} (r : ∀ a : X, Path b a) (s : SingularSimplex X 2) (i : Fin 3) :
    basedLoopClass r (triangleFacePath s i) =
      basedLoopClass r (simplexPath (s.comp (simplexFace 1 i))) :=
  basedLoopClass_cast r _ _ _

def edgeLoopCochain {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ a : X, Path b a) : Chains X 1 →+ AbelianPi1 X b :=
  chainLiftTo X 1 (AbelianPi1 X b)
    (fun s ↦ basedLoopClass r (simplexPath s))

@[simp]
theorem edgeLoopCochain_simplex {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ a : X, Path b a) (s : SingularSimplex X 1) :
    edgeLoopCochain r (simplexChain X 1 s) = basedLoopClass r (simplexPath s) :=
  chainLiftTo_simplex X 1 (AbelianPi1 X b) _ s

@[simp]
theorem edgeLoopCochain_pathChain {X : Type} [TopologicalSpace X] {b x y : X}
    (r : ∀ a : X, Path b a) (p : Path x y) :
    edgeLoopCochain r (pathChain p) = basedLoopClass r p := by
  rw [pathChain, edgeLoopCochain_simplex, simplexPath_pathSimplex]
  exact basedLoopClass_cast r _ _ _

@[simp]
theorem edgeLoopCochain_loop {X : Type} [TopologicalSpace X] {b : X}
    (r : ∀ a : X, Path b a) (p : Path b b) :
    edgeLoopCochain r (pathChain p) = loopClass p := by
  rw [edgeLoopCochain_pathChain, basedLoopClass_loop]

theorem edgeLoopCochain_boundaryTwo_simplex {X : Type} [TopologicalSpace X]
    {b : X} (r : ∀ a : X, Path b a) (s : SingularSimplex X 2) :
    edgeLoopCochain r (boundaryTwo X (simplexChain X 2 s)) = 0 := by
  simp only [boundaryTwo_simplex, map_add, map_sub, edgeLoopCochain_simplex]
  have he := congrArg₂ (fun a c : AbelianPi1 X b ↦ a + c)
    (congrArg₂ (fun a c : AbelianPi1 X b ↦ a - c)
      (basedLoopClass_triangleFacePath r s 0)
      (basedLoopClass_triangleFacePath r s 1))
    (basedLoopClass_triangleFacePath r s 2)
  exact he.symm.trans
    (basedLoopClass_triangle_boundary r (triangleEdge01 s) (triangleEdge12 s)
      (triangleEdge02 s) (triangleEdges_homotopic s))

theorem edgeLoopCochain_comp_boundaryTwo {X : Type} [TopologicalSpace X]
    {b : X} (r : ∀ a : X, Path b a) :
    (edgeLoopCochain r).comp (boundaryTwo X) = 0 := by
  apply chainHomTo_ext X 2 (AbelianPi1 X b)
  intro s
  exact edgeLoopCochain_boundaryTwo_simplex r s

end SphereSixComplex.Topology.FirstHurewiczProof
