module

public import SphereSixComplex.Topology.WangHomologyPresentationProof
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Topology.Covering.AddCircle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Lift degree on first homology of the standard circle

The singular-chain constructions in this file are a focused adaptation of the first-Hurewicz
development in Boris's `hopfproblem/Solution.lean`, released under Apache-2.0.  Only the
degree-one winding cocycle needed here is retained.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap

namespace SphereSixComplex.StandardTorusHomology

/-- The standard `n`-dimensional real torus. -/
public abbrev StdTorus (n : ℕ) : Type := Fin n → UnitAddCircle

end SphereSixComplex.StandardTorusHomology

namespace SphereSixComplex.StandardCircleHomologyLiftDegree

abbrev Simplex (n : ℕ) := stdSimplex ℝ (Fin (n + 1))

def simplexFace (n : ℕ) (i : Fin (n + 2)) : C(Simplex n, Simplex (n + 1)) :=
  ⟨stdSimplex.map (SimplexCategory.δ i).toOrderHom,
    stdSimplex.continuous_map (SimplexCategory.δ i).toOrderHom⟩

@[simp]
theorem simplexFace_apply_self (n : ℕ) (i : Fin (n + 2)) (s : Simplex n) :
    simplexFace n i s i = 0 := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ) i = 0
  rw [FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro k hk
  exact False.elim (Fin.succAbove_ne i k (Finset.mem_filter.mp hk).2)

@[simp]
theorem simplexFace_apply_succAbove (n : ℕ) (i : Fin (n + 2)) (s : Simplex n)
    (k : Fin (n + 1)) : simplexFace n i s (i.succAbove k) = s k := by
  change FunOnFinite.linearMap ℝ ℝ i.succAbove (s : Fin (n + 1) → ℝ)
      (i.succAbove k) = s k
  simp [FunOnFinite.linearMap_apply_apply, Fin.succAbove_right_injective.eq_iff,
    Finset.sum_filter]

theorem simplexFace_vertex (n : ℕ) (i : Fin (n + 2)) (k : Fin (n + 1)) :
    simplexFace n i (stdSimplex.vertex (S := ℝ) k) =
      stdSimplex.vertex (S := ℝ) (i.succAbove k) := by
  change stdSimplex.map i.succAbove (stdSimplex.vertex (S := ℝ) k) = _
  rw [stdSimplex.map_vertex]

theorem simplexZero_eq_vertex (s : Simplex 0) :
    s = stdSimplex.vertex (S := ℝ) (0 : Fin 1) := by
  let _ : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
  apply Subtype.ext
  funext k
  fin_cases k
  exact stdSimplex.eq_one_of_unique s 0

@[simp]
theorem simplexFace_zero_zero (s : Simplex 0) :
    simplexFace 0 0 s = stdSimplex.vertex (S := ℝ) (1 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_vertex]
  rfl

@[simp]
theorem simplexFace_zero_one (s : Simplex 0) :
    simplexFace 0 1 s = stdSimplex.vertex (S := ℝ) (0 : Fin 2) := by
  rw [simplexZero_eq_vertex s, simplexFace_vertex]
  rfl

def simplexPath {X : Type*} [TopologicalSpace X] (σ : C(Simplex 1, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 2)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 2))) where
  toFun t := σ (stdSimplexHomeomorphUnitInterval.symm t)
  continuous_toFun := σ.continuous.comp stdSimplexHomeomorphUnitInterval.symm.continuous
  source' := congrArg σ
    (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_zero.symm)
  target' := congrArg σ
    (stdSimplexHomeomorphUnitInterval.symm_apply_eq.mpr
      stdSimplexHomeomorphUnitInterval_one.symm)

def pathSimplex {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y) :
    C(Simplex 1, X) :=
  p.toContinuousMap.comp
    ⟨stdSimplexHomeomorphUnitInterval, stdSimplexHomeomorphUnitInterval.continuous⟩

@[simp]
theorem pathSimplex_vertex_zero {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) : pathSimplex p (stdSimplex.vertex (S := ℝ) (0 : Fin 2)) = x := by
  change p (stdSimplexHomeomorphUnitInterval _) = x
  rw [stdSimplexHomeomorphUnitInterval_zero, p.source]

@[simp]
theorem pathSimplex_vertex_one {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) : pathSimplex p (stdSimplex.vertex (S := ℝ) (1 : Fin 2)) = y := by
  change p (stdSimplexHomeomorphUnitInterval _) = y
  rw [stdSimplexHomeomorphUnitInterval_one, p.target]

@[simp]
theorem pathSimplex_face_zero {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) :
    (pathSimplex p).comp (simplexFace 0 0) = ContinuousMap.const (Simplex 0) y := by
  apply ContinuousMap.ext
  intro s
  simp

@[simp]
theorem pathSimplex_face_one {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) :
    (pathSimplex p).comp (simplexFace 0 1) = ContinuousMap.const (Simplex 0) x := by
  apply ContinuousMap.ext
  intro s
  simp

@[simp]
theorem pathSimplex_simplexPath {X : Type*} [TopologicalSpace X]
    (σ : C(Simplex 1, X)) : pathSimplex (simplexPath σ) = σ := by
  apply ContinuousMap.ext
  intro s
  change σ (stdSimplexHomeomorphUnitInterval.symm
    (stdSimplexHomeomorphUnitInterval s)) = σ s
  rw [Homeomorph.symm_apply_apply]

theorem simplexPath_pathSimplex {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) :
    simplexPath (pathSimplex p) = p.cast (by simp [pathSimplex]) (by simp [pathSimplex]) := by
  apply Path.ext
  funext t
  change p (stdSimplexHomeomorphUnitInterval
    (stdSimplexHomeomorphUnitInterval.symm t)) = p t
  rw [Homeomorph.apply_symm_apply]

abbrev IntegralChains (X : Type) [TopologicalSpace X] : ChainComplex AddCommGrpCat ℕ :=
  (TopCat.toSSet.obj (TopCat.of X)).chainComplex (AddCommGrpCat.of ℤ)

abbrev Chains (X : Type) [TopologicalSpace X] (n : ℕ) := (IntegralChains X).X n

abbrev SingularSimplex (X : Type) [TopologicalSpace X] (n : ℕ) := C(Simplex n, X)

def simplexIndex (X : Type) [TopologicalSpace X] (n : ℕ) (σ : SingularSimplex X n) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (Opposite.op (SimplexCategory.mk n)) :=
  ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n))).symm σ

def simplexChain (X : Type) [TopologicalSpace X] (n : ℕ) (σ : SingularSimplex X n) :
    Chains X n :=
  ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := AddCommGrpCat.of ℤ) (simplexIndex X n σ)) 1

abbrev boundaryOne (X : Type) [TopologicalSpace X] : Chains X 1 →+ Chains X 0 :=
  (IntegralChains X).d 1 0 |>.hom

abbrev boundaryTwo (X : Type) [TopologicalSpace X] : Chains X 2 →+ Chains X 1 :=
  (IntegralChains X).d 2 1 |>.hom

theorem simplexIndex_face (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex X (n + 1)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of X)).δ i (simplexIndex X (n + 1) σ) =
      simplexIndex X n (σ.comp (simplexFace n i)) := by
  rfl

theorem boundary_simplex (X : Type) [TopologicalSpace X] (n : ℕ)
    (σ : SingularSimplex X (n + 1)) :
    (IntegralChains X).d (n + 1) n (simplexChain X (n + 1) σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • simplexChain X n (σ.comp (simplexFace n i)) := by
  have h := (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex_d
    (R := AddCommGrpCat.of ℤ) (simplexIndex X (n + 1) σ)
  let ev : (AddCommGrpCat.of ℤ ⟶ Chains X n) →+ Chains X n :=
    { toFun := fun f ↦ f.hom 1
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have he := congrArg ev h
  rw [map_sum] at he
  simp only [map_zsmul, simplexIndex_face] at he
  exact he

theorem boundaryTwo_simplex (X : Type) [TopologicalSpace X]
    (σ : SingularSimplex X 2) :
    boundaryTwo X (simplexChain X 2 σ) =
      simplexChain X 1 (σ.comp (simplexFace 1 0)) -
        simplexChain X 1 (σ.comp (simplexFace 1 1)) +
          simplexChain X 1 (σ.comp (simplexFace 1 2)) := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg, add_assoc] using boundary_simplex X 1 σ

theorem boundaryOne_simplex (X : Type) [TopologicalSpace X]
    (σ : SingularSimplex X 1) :
    boundaryOne X (simplexChain X 1 σ) =
      simplexChain X 0 (σ.comp (simplexFace 0 0)) -
        simplexChain X 0 (σ.comp (simplexFace 0 1)) := by
  simpa [Fin.sum_univ_succ, sub_eq_add_neg] using boundary_simplex X 0 σ

def pointChain {X : Type} [TopologicalSpace X] (x : X) : Chains X 0 :=
  simplexChain X 0 (ContinuousMap.const (Simplex 0) x)

def pathChain {X : Type} [TopologicalSpace X] {x y : X} (p : Path x y) : Chains X 1 :=
  simplexChain X 1 (pathSimplex p)

theorem boundaryOne_pathChain {X : Type} [TopologicalSpace X] {x y : X}
    (p : Path x y) : boundaryOne X (pathChain p) = pointChain y - pointChain x := by
  rw [pathChain, boundaryOne_simplex, pathSimplex_face_zero, pathSimplex_face_one]
  rfl

theorem boundaryOne_loop {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    boundaryOne X (pathChain p) = 0 := by
  rw [boundaryOne_pathChain, sub_self]

def chainLift (X : Type) [TopologicalSpace X] (n : ℕ)
    (f : SingularSimplex X n → ℤ) : Chains X n →+ ℤ :=
  (Sigma.desc
    (fun s : (TopCat.toSSet.obj (TopCat.of X)).obj
        (Opposite.op (SimplexCategory.mk n)) ↦
      AddCommGrpCat.ofHom
        (zmultiplesHom ℤ
          (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n)) s)))) :
    Chains X n ⟶ AddCommGrpCat.of ℤ).hom

@[simp]
theorem chainLift_simplex (X : Type) [TopologicalSpace X] (n : ℕ)
    (f : SingularSimplex X n → ℤ) (σ : SingularSimplex X n) :
    chainLift X n f (simplexChain X n σ) = f σ := by
  have h := Sigma.ι_desc
    (fun s : (TopCat.toSSet.obj (TopCat.of X)).obj
        (Opposite.op (SimplexCategory.mk n)) ↦
      AddCommGrpCat.ofHom
        (zmultiplesHom ℤ
          (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n)) s))))
    (simplexIndex X n σ)
  have he := congrArg (fun g : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ ↦ g.hom 1) h
  change chainLift X n f (simplexChain X n σ) =
    zmultiplesHom ℤ
      (f ((TopCat.of X).toSSetObjEquiv (.op (SimplexCategory.mk n))
        (simplexIndex X n σ))) 1 at he
  simpa [simplexIndex] using he

theorem chainHom_ext (X : Type) [TopologicalSpace X] (n : ℕ)
    {f g : Chains X n →+ ℤ}
    (h : ∀ σ : SingularSimplex X n, f (simplexChain X n σ) =
      g (simplexChain X n σ)) : f = g := by
  have hcat : (AddCommGrpCat.ofHom f : Chains X n ⟶ AddCommGrpCat.of ℤ) =
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

theorem simplex_contractible (n : ℕ) : ContractibleSpace (Simplex n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
    ⟨(stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).val,
      (stdSimplex.vertex (S := ℝ) (0 : Fin (n + 1))).property⟩

theorem simplex_simplyConnected (n : ℕ) : SimplyConnectedSpace (Simplex n) := by
  let _ := simplex_contractible n
  infer_instance

def triangleFacePath {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X))
    (i : Fin 3) :
    Path (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (0 : Fin 2))))
      (σ (stdSimplex.vertex (S := ℝ) (i.succAbove (1 : Fin 2)))) :=
  (simplexPath (σ.comp (simplexFace 1 i))).cast
    (congrArg σ (simplexFace_vertex 1 i 0)).symm
    (congrArg σ (simplexFace_vertex 1 i 1)).symm

abbrev triangleEdge01 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3))) :=
  triangleFacePath σ 2

abbrev triangleEdge12 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (1 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 0

abbrev triangleEdge02 {X : Type*} [TopologicalSpace X] (σ : C(Simplex 2, X)) :
    Path (σ (stdSimplex.vertex (S := ℝ) (0 : Fin 3)))
      (σ (stdSimplex.vertex (S := ℝ) (2 : Fin 3))) :=
  triangleFacePath σ 1

theorem triangleEdges_homotopic {X : Type*} [TopologicalSpace X]
    (σ : C(Simplex 2, X)) :
    ((triangleEdge01 σ).trans (triangleEdge12 σ)).Homotopic (triangleEdge02 σ) := by
  let _ := simplex_simplyConnected 2
  have h := SimplyConnectedSpace.paths_homotopic
    ((triangleEdge01 (ContinuousMap.id (Simplex 2))).trans
      (triangleEdge12 (ContinuousMap.id (Simplex 2))))
    (triangleEdge02 (ContinuousMap.id (Simplex 2)))
  have hmap := h.map σ
  rw [Path.map_trans] at hmap
  exact hmap

def intToUnitDeck : ℤ ≃+ AddSubgroup.zmultiples (1 : ℝ) :=
  AddEquiv.ofBijective
    ((Int.castAddHom ℝ).codRestrict (AddSubgroup.zmultiples (1 : ℝ))
      (fun n ↦ by simp))
    (by
      constructor
      · intro m n h
        have h' : (m : ℝ) = (n : ℝ) := congrArg Subtype.val h
        exact_mod_cast h'
      · rintro ⟨x, hx⟩
        obtain ⟨n, hn⟩ := hx
        refine ⟨n, Subtype.ext ?_⟩
        simpa using hn)

def unitCircleFundamentalGroupEquiv :
    FundamentalGroup UnitAddCircle 0 ≃* Multiplicative ℤ :=
  ((AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)).fundamentalGroupEquiv
      (⟨0, rfl⟩ : ((fun x : ℝ ↦ (x : UnitAddCircle)) ⁻¹' ({0} : Set UnitAddCircle)))).trans
    (MulOpposite.opMulEquiv.symm.trans intToUnitDeck.symm.toMultiplicative)

def basedLoop {x y : UnitAddCircle} (r : ∀ z : UnitAddCircle, Path 0 z)
    (p : Path x y) : Path (0 : UnitAddCircle) 0 :=
  (r x).trans (p.trans (r y).symm)

def basedLoopQuotient {x y : UnitAddCircle} (r : ∀ z : UnitAddCircle, Path 0 z)
    (p : Path x y) : FundamentalGroup UnitAddCircle 0 :=
  Path.Homotopic.Quotient.mk (basedLoop r p)

def basedLoopWinding {x y : UnitAddCircle} (r : ∀ z : UnitAddCircle, Path 0 z)
    (p : Path x y) : ℤ :=
  (unitCircleFundamentalGroupEquiv (basedLoopQuotient r p)).toAdd

theorem basedLoopQuotient_trans {x y z : UnitAddCircle}
    (r : ∀ z : UnitAddCircle, Path 0 z) (p : Path x y) (q : Path y z) :
    basedLoopQuotient r (p.trans q) = basedLoopQuotient r q * basedLoopQuotient r p := by
  unfold basedLoopQuotient basedLoop
  simp only [Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, FundamentalGroup.mul_def,
    Path.Homotopic.Quotient.trans_assoc]
  rw [← Path.Homotopic.Quotient.trans_assoc
    (Path.Homotopic.Quotient.mk (r y)).symm (Path.Homotopic.Quotient.mk (r y)),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

theorem basedLoopWinding_trans {x y z : UnitAddCircle}
    (r : ∀ z : UnitAddCircle, Path 0 z) (p : Path x y) (q : Path y z) :
    basedLoopWinding r (p.trans q) = basedLoopWinding r p + basedLoopWinding r q := by
  rw [basedLoopWinding, basedLoopQuotient_trans, map_mul]
  simp [basedLoopWinding, add_comm]

theorem basedLoopWinding_homotopic {x y : UnitAddCircle}
    (r : ∀ z : UnitAddCircle, Path 0 z) {p q : Path x y} (h : p.Homotopic q) :
    basedLoopWinding r p = basedLoopWinding r q := by
  apply congrArg (fun g ↦ (unitCircleFundamentalGroupEquiv g).toAdd)
  apply Path.Homotopic.Quotient.eq.mpr
  exact (Path.Homotopic.refl (r x)).hcomp
    (h.hcomp (Path.Homotopic.refl (r y).symm))

theorem basedLoopWinding_triangle {x y z : UnitAddCircle}
    (r : ∀ z : UnitAddCircle, Path 0 z) (p₀₁ : Path x y) (p₁₂ : Path y z)
    (p₀₂ : Path x z) (h : (p₀₁.trans p₁₂).Homotopic p₀₂) :
    basedLoopWinding r p₁₂ - basedLoopWinding r p₀₂ +
      basedLoopWinding r p₀₁ = 0 := by
  rw [← basedLoopWinding_homotopic r h, basedLoopWinding_trans]
  abel

theorem basedLoopWinding_cast {x y x' y' : UnitAddCircle}
    (r : ∀ z : UnitAddCircle, Path 0 z) (p : Path x y) (hx : x' = x) (hy : y' = y) :
    basedLoopWinding r (p.cast hx hy) = basedLoopWinding r p := by
  cases hx
  cases hy
  rfl

def unitCirclePaths : ∀ z : UnitAddCircle, Path 0 z := PathConnectedSpace.somePath 0

def edgeWinding : Chains UnitAddCircle 1 →+ ℤ :=
  chainLift UnitAddCircle 1 (fun σ ↦ basedLoopWinding unitCirclePaths (simplexPath σ))

@[simp]
theorem edgeWinding_simplex (σ : SingularSimplex UnitAddCircle 1) :
    edgeWinding (simplexChain UnitAddCircle 1 σ) =
      basedLoopWinding unitCirclePaths (simplexPath σ) :=
  chainLift_simplex UnitAddCircle 1 _ σ

theorem basedLoopWinding_triangleFacePath (σ : SingularSimplex UnitAddCircle 2) (i : Fin 3) :
    basedLoopWinding unitCirclePaths (triangleFacePath σ i) =
      basedLoopWinding unitCirclePaths (simplexPath (σ.comp (simplexFace 1 i))) :=
  basedLoopWinding_cast unitCirclePaths _ _ _

theorem edgeWinding_boundaryTwo_simplex (σ : SingularSimplex UnitAddCircle 2) :
    edgeWinding (boundaryTwo UnitAddCircle (simplexChain UnitAddCircle 2 σ)) = 0 := by
  simp only [boundaryTwo_simplex, map_add, map_sub, edgeWinding_simplex]
  have he := congrArg₂ (fun a c : ℤ ↦ a + c)
    (congrArg₂ (fun a c : ℤ ↦ a - c)
      (basedLoopWinding_triangleFacePath σ 0)
      (basedLoopWinding_triangleFacePath σ 1))
    (basedLoopWinding_triangleFacePath σ 2)
  exact he.symm.trans
    (basedLoopWinding_triangle unitCirclePaths (triangleEdge01 σ) (triangleEdge12 σ)
      (triangleEdge02 σ) (triangleEdges_homotopic σ))

theorem edgeWinding_comp_boundaryTwo :
    edgeWinding.comp (boundaryTwo UnitAddCircle) = 0 := by
  apply chainHom_ext UnitAddCircle 2
  intro σ
  exact edgeWinding_boundaryTwo_simplex σ

theorem edgeWinding_boundaryTwo (c : Chains UnitAddCircle 2) :
    edgeWinding (boundaryTwo UnitAddCircle c) = 0 :=
  DFunLike.congr_fun edgeWinding_comp_boundaryTwo c

def windingChainMap :
    IntegralChains UnitAddCircle ⟶
      (HomologicalComplex.single AddCommGrpCat (ComplexShape.down ℕ) 1).obj
        (AddCommGrpCat.of ℤ) :=
  HomologicalComplex.mkHomToSingle (AddCommGrpCat.ofHom edgeWinding) (by
    intro i hi
    have hi' : i = 2 := by simpa using hi.symm
    subst i
    apply AddCommGrpCat.hom_ext
    exact edgeWinding_comp_boundaryTwo)

def unitCircleHomologyWinding :
    IntegralSingularHomology 1 UnitAddCircle →+ ℤ :=
  (HomologicalComplex.homologyMap windingChainMap 1 ≫
    (HomologicalComplex.singleObjHomologySelfIso
      (ComplexShape.down ℕ) 1 (AddCommGrpCat.of ℤ)).hom).hom

def loopCycle {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    AddCommGrpCat.of ℤ ⟶ (IntegralChains X).X 1 :=
  AddCommGrpCat.asHom (pathChain p)

theorem loopCycle_isCycle {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    loopCycle p ≫ (IntegralChains X).d 1 0 = 0 := by
  apply AddCommGrpCat.int_hom_ext
  change (IntegralChains X).d 1 0 ((AddCommGrpCat.asHom (pathChain p)) 1) = 0
  rw [AddCommGrpCat.asHom_hom_apply, one_zsmul]
  exact boundaryOne_loop p

def loopHomologyMap {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    AddCommGrpCat.of ℤ ⟶ (IntegralChains X).homology 1 :=
  (IntegralChains X).liftCycles (loopCycle p) 0 (by simp) (loopCycle_isCycle p) ≫
    (IntegralChains X).homologyπ 1

def loopHomologyClass {X : Type} [TopologicalSpace X] {x : X} (p : Path x x) :
    IntegralSingularHomology 1 X :=
  (loopHomologyMap p) 1

theorem loopHomologyClass_cast {X : Type} [TopologicalSpace X] {x x' : X}
    (p : Path x x) (h : x' = x) :
    loopHomologyClass (p.cast h h) = loopHomologyClass p := by
  cases h
  rfl

theorem loopHomologyMap_winding (p : Path (0 : UnitAddCircle) 0) :
    loopHomologyMap p ≫ HomologicalComplex.homologyMap windingChainMap 1 ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) 1 (AddCommGrpCat.of ℤ)).hom =
      AddCommGrpCat.asHom (basedLoopWinding unitCirclePaths p) := by
  unfold loopHomologyMap
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc]
  rw [← Category.assoc]
  rw [HomologicalComplex.liftCycles_comp_cyclesMap]
  rw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom]
  rw [HomologicalComplex.liftCycles_i_assoc]
  apply AddCommGrpCat.int_hom_ext
  simp [windingChainMap, loopCycle, edgeWinding]
  rw [pathChain, chainLift_simplex, AddCommGrpCat.asHom_hom_apply, one_zsmul,
    simplexPath_pathSimplex]
  exact basedLoopWinding_cast unitCirclePaths _ _ _

theorem unitCircleHomologyWinding_loop (p : Path (0 : UnitAddCircle) 0) :
    unitCircleHomologyWinding (loopHomologyClass p) =
      basedLoopWinding unitCirclePaths p := by
  have h := ConcreteCategory.congr_hom (loopHomologyMap_winding p) (1 : ℤ)
  change ConcreteCategory.hom
      (HomologicalComplex.homologyMap windingChainMap 1 ≫
        (HomologicalComplex.singleObjHomologySelfIso
          (ComplexShape.down ℕ) 1 (AddCommGrpCat.of ℤ)).hom)
      (ConcreteCategory.hom (loopHomologyMap p) 1) =
    basedLoopWinding unitCirclePaths p
  exact h.trans (by rw [AddCommGrpCat.asHom_hom_apply, one_zsmul])

def unitCircleIntegerLoop (n : ℤ) : Path (0 : UnitAddCircle) 0 where
  toFun t := (((t : ℝ) * (n : ℝ) : ℝ) : UnitAddCircle)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

def unitCircleIntegerLoopLift (n : ℤ) : Path (0 : ℝ) (n : ℝ) where
  toFun t := (t : ℝ) * (n : ℝ)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem unitCircleIntegerLoopLift_map (n : ℤ) :
    ((unitCircleIntegerLoopLift n).map continuous_quotient_mk').cast
        (show (0 : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by rfl)
        (show (0 : UnitAddCircle) = ((n : ℝ) : UnitAddCircle) by
          symm
          rw [AddCircle.coe_eq_zero_iff]
          exact ⟨n, by simp⟩) =
      unitCircleIntegerLoop n := by
  apply Path.ext
  rfl

theorem unitCircleFundamentalGroupEquiv_integerLoop (n : ℤ) :
    unitCircleFundamentalGroupEquiv
        (Path.Homotopic.Quotient.mk (unitCircleIntegerLoop n)) =
      Multiplicative.ofAdd n := by
  unfold unitCircleFundamentalGroupEquiv
  let hp := AddCircle.isAddQuotientCoveringMap_coe (1 : ℝ)
  let e0 : ((fun x : ℝ ↦ (x : UnitAddCircle)) ⁻¹' ({0} : Set UnitAddCircle)) :=
    ⟨0, rfl⟩
  let en : ((fun x : ℝ ↦ (x : UnitAddCircle)) ⁻¹' ({0} : Set UnitAddCircle)) :=
    ⟨(n : ℝ), by
      rw [Set.mem_preimage, Set.mem_singleton_iff, AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩⟩
  have hraw :
      hp.fundamentalGroupEquiv e0
          (Path.Homotopic.Quotient.mk (unitCircleIntegerLoop n)) =
        MulOpposite.op (Multiplicative.ofAdd (intToUnitDeck n)) := by
    change hp.fundamentalGroupToMulOpposite e0
        (Path.Homotopic.Quotient.mk (unitCircleIntegerLoop n)) = _
    rw [hp.fundamentalGroupToMulOpposite_apply_eq_Iff]
    have hmono := hp.isCoveringMap.monodromy_eq_of_map_eq
      (γ := Path.Homotopic.Quotient.mk (unitCircleIntegerLoop n))
      (ex := e0) (ey := en)
      (Γ := Path.Homotopic.Quotient.mk (unitCircleIntegerLoopLift n))
      (by
        dsimp [e0, en]
        apply Path.Homotopic.Quotient.eq.mpr
        exact Path.Homotopic.refl _)
    rw [hmono]
    change (n : ℝ) + 0 = n
    simp
  simp only [MulEquiv.trans_apply]
  rw [hraw]
  exact intToUnitDeck.symm_apply_apply n

theorem basedLoopWinding_loop (r : ∀ z : UnitAddCircle, Path 0 z)
    (p : Path (0 : UnitAddCircle) 0) :
    basedLoopWinding r p =
      (unitCircleFundamentalGroupEquiv (Path.Homotopic.Quotient.mk p)).toAdd := by
  unfold basedLoopWinding basedLoopQuotient basedLoop
  simp only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← FundamentalGroup.mul_def, ← FundamentalGroup.inv_def, map_mul, map_inv,
    toAdd_mul, toAdd_inv]
  abel

theorem basedLoopWinding_integerLoop (n : ℤ) :
    basedLoopWinding unitCirclePaths (unitCircleIntegerLoop n) = n := by
  rw [basedLoopWinding_loop, unitCircleFundamentalGroupEquiv_integerLoop]
  rfl

theorem unitCircleHomologyWinding_integerLoop (n : ℤ) :
    unitCircleHomologyWinding (loopHomologyClass (unitCircleIntegerLoop n)) = n := by
  rw [unitCircleHomologyWinding_loop, basedLoopWinding_integerLoop]

def stdTorusOneHomeomorph : StandardTorusHomology.StdTorus 1 ≃ₜ UnitAddCircle where
  toFun z := z 0
  invFun z := fun _ ↦ z
  left_inv z := by
    funext i
    fin_cases i
    rfl
  right_inv _ := rfl
  continuous_toFun := continuous_apply 0
  continuous_invFun := continuous_pi fun _ ↦ continuous_id

theorem unitCircleHomologyWinding_surjective :
    Function.Surjective unitCircleHomologyWinding := by
  intro n
  exact ⟨loopHomologyClass (unitCircleIntegerLoop n),
    unitCircleHomologyWinding_integerLoop n⟩

abbrev singularChainMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) : IntegralChains X ⟶ IntegralChains Y :=
  SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) (AddCommGrpCat.of ℤ)

theorem singularChainMap_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) (σ : SingularSimplex X n) :
    (singularChainMap f).f n (simplexChain X n σ) =
      simplexChain Y n (f.comp σ) := by
  have h := SSet.ι_chainComplexMap_f
    (TopCat.toSSet.obj (TopCat.of X)) (TopCat.toSSet.obj (TopCat.of Y))
    (TopCat.toSSet.map (TopCat.ofHom f)) (AddCommGrpCat.of ℤ) (simplexIndex X n σ)
  have he := congrArg (fun g : AddCommGrpCat.of ℤ ⟶ Chains Y n ↦ g.hom 1) h
  change (singularChainMap f).f n (simplexChain X n σ) =
    simplexChain Y n (f.comp σ) at he
  exact he

theorem loopCycle_naturality {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (p : Path x x) :
    loopCycle p ≫ (singularChainMap f).f 1 = loopCycle (p.map f.continuous) := by
  apply AddCommGrpCat.int_hom_ext
  change (singularChainMap f).f 1 ((AddCommGrpCat.asHom (pathChain p)) 1) =
    (AddCommGrpCat.asHom (pathChain (p.map f.continuous))) 1
  rw [AddCommGrpCat.asHom_hom_apply, AddCommGrpCat.asHom_hom_apply, one_zsmul, one_zsmul]
  rw [pathChain, singularChainMap_simplex, pathChain]
  rfl

theorem loopHomologyMap_naturality {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (p : Path x x) :
    loopHomologyMap p ≫ HomologicalComplex.homologyMap (singularChainMap f) 1 =
      loopHomologyMap (p.map f.continuous) := by
  unfold loopHomologyMap
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [← Category.assoc, HomologicalComplex.liftCycles_comp_cyclesMap]
  simp only [loopCycle_naturality]

theorem integralSingularHomologyMap_loopHomologyClass
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x : X} (p : Path x x) :
    integralSingularHomologyMap 1 f (loopHomologyClass p) =
      loopHomologyClass (p.map f.continuous) := by
  have h := ConcreteCategory.congr_hom (loopHomologyMap_naturality f p) (1 : ℤ)
  exact h

def unitCirclePowerMap (n : ℤ) : C(UnitAddCircle, UnitAddCircle) where
  toFun z := n • z
  continuous_toFun := continuous_const_smul n

theorem unitCircleIntegerLoop_one_map_power (n : ℤ) :
    ((unitCircleIntegerLoop 1).map (unitCirclePowerMap n).continuous).cast
        (by simp [unitCirclePowerMap]) (by simp [unitCirclePowerMap]) =
      unitCircleIntegerLoop n := by
  apply Path.ext
  funext t
  simp only [Path.cast_coe, Path.map_coe, Function.comp_apply]
  change (unitCirclePowerMap n).toFun ((unitCircleIntegerLoop 1).toFun t) =
    (unitCircleIntegerLoop n).toFun t
  dsimp only [unitCirclePowerMap, unitCircleIntegerLoop]
  rw [← AddCircle.coe_zsmul]
  congr 1
  push_cast
  ring

def unitCirclePositiveHomologyClass : IntegralSingularHomology 1 UnitAddCircle :=
  loopHomologyClass (unitCircleIntegerLoop 1)

theorem unitCircleHomologyWinding_positive :
    unitCircleHomologyWinding unitCirclePositiveHomologyClass = 1 :=
  unitCircleHomologyWinding_integerLoop 1

theorem unitCirclePowerMap_positiveHomologyClass (n : ℤ) :
    integralSingularHomologyMap 1 (unitCirclePowerMap n) unitCirclePositiveHomologyClass =
      loopHomologyClass (unitCircleIntegerLoop n) := by
  rw [unitCirclePositiveHomologyClass, integralSingularHomologyMap_loopHomologyClass]
  let hzero : (0 : UnitAddCircle) = unitCirclePowerMap n 0 := by
    simp [unitCirclePowerMap]
  calc
    loopHomologyClass ((unitCircleIntegerLoop 1).map (unitCirclePowerMap n).continuous) =
        loopHomologyClass
          (((unitCircleIntegerLoop 1).map (unitCirclePowerMap n).continuous).cast
            hzero hzero) := (loopHomologyClass_cast _ hzero).symm
    _ = loopHomologyClass (unitCircleIntegerLoop n) := by
      apply congrArg loopHomologyClass
      simpa only using unitCircleIntegerLoop_one_map_power n

theorem unitCircleMap_eq_power_of_additiveLift
    (f : C(UnitAddCircle, UnitAddCircle)) (L : ℝ →+ ℝ) (n : ℤ)
    (map_projection : ∀ r : ℝ, f (r : UnitAddCircle) = (L r : UnitAddCircle))
    (map_one : L 1 = (n : ℝ)) :
    f = unitCirclePowerMap n := by
  apply ContinuousMap.ext
  have heq : (fun r : ℝ ↦ f (r : UnitAddCircle)) =
      fun r : ℝ ↦ unitCirclePowerMap n (r : UnitAddCircle) := by
    apply Rat.denseRange_cast.equalizer
    · exact f.continuous.comp (AddCircle.continuous_mk' 1)
    · exact (unitCirclePowerMap n).continuous.comp (AddCircle.continuous_mk' 1)
    · funext q
      dsimp only [Function.comp_apply]
      rw [map_projection]
      change (L (q : ℝ) : UnitAddCircle) = n • ((q : ℝ) : UnitAddCircle)
      rw [← AddCircle.coe_zsmul]
      congr 1
      simpa [map_one, Rat.smul_def, mul_comm] using map_rat_smul L q (1 : ℝ)
  intro z
  obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective z
  exact congrFun heq r

def stdTorusOneProjection (r : ℝ) : StandardTorusHomology.StdTorus 1 :=
  fun _ ↦ (r : UnitAddCircle)

theorem continuous_stdTorusOneProjection : Continuous stdTorusOneProjection := by
  apply continuous_pi
  intro i
  exact AddCircle.continuous_mk' 1

def stdTorusOnePowerMap (n : ℤ) :
    C(StandardTorusHomology.StdTorus 1, StandardTorusHomology.StdTorus 1) where
  toFun z i := n • z i
  continuous_toFun := by
    fun_prop

theorem stdTorusOneHomeomorph_comp_power (n : ℤ) :
    (stdTorusOneHomeomorph :
        C(StandardTorusHomology.StdTorus 1, UnitAddCircle)).comp
        (stdTorusOnePowerMap n) =
      (unitCirclePowerMap n).comp
        (stdTorusOneHomeomorph :
          C(StandardTorusHomology.StdTorus 1, UnitAddCircle)) := by
  ext z
  rfl

theorem stdTorusOneMap_eq_power_of_additiveLift
    (f : C(StandardTorusHomology.StdTorus 1, StandardTorusHomology.StdTorus 1))
    (L : ℝ →+ ℝ) (n : ℤ)
    (map_projection : ∀ r : ℝ,
      f (stdTorusOneProjection r) = stdTorusOneProjection (L r))
    (map_one : L 1 = (n : ℝ)) :
    f = stdTorusOnePowerMap n := by
  apply ContinuousMap.ext
  have heq : (fun r : ℝ ↦ f (stdTorusOneProjection r)) =
      fun r : ℝ ↦ stdTorusOnePowerMap n (stdTorusOneProjection r) := by
    apply Rat.denseRange_cast.equalizer
    · exact f.continuous.comp continuous_stdTorusOneProjection
    · exact (stdTorusOnePowerMap n).continuous.comp continuous_stdTorusOneProjection
    · funext q
      dsimp only [Function.comp_apply]
      rw [map_projection]
      funext i
      fin_cases i
      change (L (q : ℝ) : UnitAddCircle) = n • ((q : ℝ) : UnitAddCircle)
      rw [← AddCircle.coe_zsmul]
      congr 1
      simpa [map_one, Rat.smul_def, mul_comm] using map_rat_smul L q (1 : ℝ)
  intro z
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (z 0)
  have hz : z = stdTorusOneProjection r := by
    funext i
    fin_cases i
    exact hr.symm
  subst z
  exact congrFun heq r

end SphereSixComplex.StandardCircleHomologyLiftDegree

end
