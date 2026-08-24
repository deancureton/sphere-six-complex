module

public import SphereSixComplex.Topology.SingularSubdivision

/-!
# Low-dimensional barycentric fundamental chains

This file constructs the first actual components of the barycentric subdivision chain operator.
The construction starts from the vertex of `sd Δ[0]` represented by the singleton chain and
uses Yoneda naturality to associate a subdivided vertex to every vertex of a simplicial set.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Simplicial

namespace SphereSixComplex

/-- A singleton, regarded as a nonempty finite chain. -/
public noncomputable def nonemptyFiniteChainSingleton
    {X : Type*} [LinearOrder X] (x : X) : NonemptyFiniteChains X where
  finset := {x}
  comparable := by simp

@[simp]
public theorem nonemptyFiniteChainSingleton_finset
    {X : Type*} [LinearOrder X] (x : X) :
    (nonemptyFiniteChainSingleton x).finset = {x} :=
  rfl

/-- The vertex of the subdivision model of `Δ[0]` represented by its singleton vertex chain. -/
public noncomputable def subdividedZeroSimplexVertex :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 0)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (nonemptyFiniteChainSingleton (ULift.up (0 : Fin 1)))

/-- The corresponding vertex of Mathlib's left-Kan-extension model `sd Δ[0]`. -/
public noncomputable def subdividedStandardZeroVertex :
    (SSet.sd.obj (Δ[0] : SSet.{0})).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 0) |>.app _
    subdividedZeroSimplexVertex

/-- Every vertex of a simplicial set determines its canonical vertex after subdivision. -/
public noncomputable def barycentricSubdivisionVertex
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    (SSet.sd.obj X).obj (Opposite.op (SimplexCategory.mk 0)) :=
  (SSet.sd.map (SSet.yonedaEquiv.symm x)).app _ subdividedStandardZeroVertex

/-- The last-vertex map sends the canonical subdivided vertex of `Δ[0]` to its unique
vertex. -/
public theorem subdivisionLastVertex_subdividedStandardZeroVertex :
    (subdivisionLastVertex.app (Δ[0] : SSet.{0})).app _
        subdividedStandardZeroVertex =
      SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 0)) := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The last-vertex map is a left inverse to barycentric subdivision on vertices. -/
public theorem subdivisionLastVertex_barycentricSubdivisionVertex
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    (subdivisionLastVertex.app X).app _ (barycentricSubdivisionVertex X x) = x := by
  let f : (Δ[0] : SSet.{0}) ⟶ X := SSet.yonedaEquiv.symm x
  have h := subdivisionLastVertex.naturality f
  have h₀ := NatTrans.congr_app h (Opposite.op (SimplexCategory.mk 0))
  have hx := ConcreteCategory.congr_hom h₀ subdividedStandardZeroVertex
  change (subdivisionLastVertex.app X).app _
      ((SSet.sd.map f).app _ subdividedStandardZeroVertex) =
    f.app _ ((subdivisionLastVertex.app (Δ[0] : SSet.{0})).app _
      subdividedStandardZeroVertex) at hx
  rw [subdivisionLastVertex_subdividedStandardZeroVertex] at hx
  change (subdivisionLastVertex.app X).app _
      ((SSet.sd.map f).app _ subdividedStandardZeroVertex) = x
  rw [hx]
  change X.map (𝟙 (Opposite.op (SimplexCategory.mk 0))) x = x
  simp

/-- Canonical subdivided vertices are natural in maps of simplicial sets. -/
public theorem barycentricSubdivisionVertex_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y)
    (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    barycentricSubdivisionVertex Y (f.app _ x) =
      (SSet.sd.map f).app _ (barycentricSubdivisionVertex X x) := by
  rw [barycentricSubdivisionVertex, barycentricSubdivisionVertex]
  rw [← SSet.yonedaEquiv_symm_comp]
  have h := SSet.sd.map_comp (SSet.yonedaEquiv.symm x) f
  have h₀ := NatTrans.congr_app h (Opposite.op (SimplexCategory.mk 0))
  exact ConcreteCategory.congr_hom h₀ subdividedStandardZeroVertex

/-- The degree-zero component of barycentric subdivision on integral simplicial chains. -/
public noncomputable def barycentricSubdivisionChainMapZero (X : SSet.{0}) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X 0 ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 0 :=
  Sigma.desc (fun x ↦ (SSet.sd.obj X).ιChainComplex
    (barycentricSubdivisionVertex X x))

@[reassoc (attr := simp)]
public theorem iota_barycentricSubdivisionChainMapZero
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    X.ιChainComplex x ≫ barycentricSubdivisionChainMapZero X =
      (SSet.sd.obj X).ιChainComplex (barycentricSubdivisionVertex X x) := by
  apply Sigma.ι_desc

/-- In degree zero, barycentric subdivision followed by last vertex is exactly the identity. -/
public theorem barycentricSubdivisionChainMapZero_comp_lastVertex
    (X : SSet.{0}) :
    barycentricSubdivisionChainMapZero X ≫
        (subdivisionLastVertexChainMap X).f 0 =
      𝟙 ((X.chainComplex (AddCommGrpCat.of ℤ)).X 0) := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_barycentricSubdivisionChainMapZero]
  change (SSet.sd.obj X).ιChainComplex (barycentricSubdivisionVertex X x) ≫
      (SSet.chainComplexMap (subdivisionLastVertex.app X)
        (AddCommGrpCat.of ℤ)).f 0 = _
  rw [SSet.ι_chainComplexMap_f,
    subdivisionLastVertex_barycentricSubdivisionVertex]
  simp

/-- The degree-zero barycentric subdivision maps are natural. -/
public theorem barycentricSubdivisionChainMapZero_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f 0 ≫
        barycentricSubdivisionChainMapZero Y =
      barycentricSubdivisionChainMapZero X ≫
        (SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ)).f 0 := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    iota_barycentricSubdivisionChainMapZero]
  rw [← Category.assoc, iota_barycentricSubdivisionChainMapZero,
    SSet.ι_chainComplexMap_f, barycentricSubdivisionVertex_naturality]

section OneSimplex

/-- A specified nonempty finset in a linear order, regarded as a finite chain. -/
public noncomputable def nonemptyFiniteChainOfFinset
    {X : Type*} [LinearOrder X] (s : Finset X) (hs : s.Nonempty) :
    NonemptyFiniteChains X where
  finset := s
  nonempty := hs
  comparable a b := le_total a b

public noncomputable def oneVertexChain (i : Fin 2) :
    NonemptyFiniteChains (ULift.{0} (Fin 2)) :=
  nonemptyFiniteChainSingleton (ULift.up i)

public noncomputable def oneFullChain :
    NonemptyFiniteChains (ULift.{0} (Fin 2)) :=
  nonemptyFiniteChainOfFinset Finset.univ Finset.univ_nonempty

public noncomputable def oneVertexZeroToFull :
    oneVertexChain 0 ⟶ oneFullChain :=
  homOfLE (by
    show (oneVertexChain 0).finset ⊆ oneFullChain.finset
    simp [oneVertexChain, oneFullChain, nonemptyFiniteChainOfFinset])

public noncomputable def oneVertexOneToFull :
    oneVertexChain 1 ⟶ oneFullChain :=
  homOfLE (by
    show (oneVertexChain 1).finset ⊆ oneFullChain.finset
    simp [oneVertexChain, oneFullChain, nonemptyFiniteChainOfFinset])

/-- The vertex `0` in the barycentric subdivision model of `Δ[1]`. -/
public noncomputable def subdividedOneSimplexVertexZero :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (oneVertexChain 0)

/-- The vertex `1` in the barycentric subdivision model of `Δ[1]`. -/
public noncomputable def subdividedOneSimplexVertexOne :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (oneVertexChain 1)

/-- The midpoint vertex in the barycentric subdivision model of `Δ[1]`. -/
public noncomputable def subdividedOneSimplexVertexMidpoint :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ oneFullChain

/-- The oriented edge from vertex `0` to the midpoint. -/
public noncomputable def subdividedOneSimplexEdgeZero :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  ComposableArrows.mk₁ oneVertexZeroToFull

/-- The edge from vertex `1` to the midpoint; it occurs with coefficient `-1` in the oriented
fundamental chain. -/
public noncomputable def subdividedOneSimplexEdgeOne :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk 1)) :=
  ComposableArrows.mk₁ oneVertexOneToFull

/-- The oriented fundamental one-chain `[0,mid] - [1,mid]` of the subdivided interval model. -/
public noncomputable def subdividedOneSimplexFundamentalChain :
    AddCommGrpCat.of ℤ ⟶
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).chainComplex
        (AddCommGrpCat.of ℤ)).X 1 :=
  (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).ιChainComplex
      subdividedOneSimplexEdgeZero -
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).ιChainComplex
      subdividedOneSimplexEdgeOne

/-- The expected oriented boundary `[1] - [0]` of the subdivided interval. -/
public noncomputable def subdividedOneSimplexBoundaryChain :
    AddCommGrpCat.of ℤ ⟶
      ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).chainComplex
        (AddCommGrpCat.of ℤ)).X 0 :=
  (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).ιChainComplex
      subdividedOneSimplexVertexOne -
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).ιChainComplex
      subdividedOneSimplexVertexZero

@[simp]
public theorem subdividedOneSimplexEdgeZero_delta_zero :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).δ 0
        subdividedOneSimplexEdgeZero =
      subdividedOneSimplexVertexMidpoint := by
  apply ComposableArrows.ext₀
  rfl

@[simp]
public theorem subdividedOneSimplexEdgeZero_delta_one :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).δ 1
        subdividedOneSimplexEdgeZero =
      subdividedOneSimplexVertexZero := by
  apply ComposableArrows.ext₀
  rfl

@[simp]
public theorem subdividedOneSimplexEdgeOne_delta_zero :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).δ 0
        subdividedOneSimplexEdgeOne =
      subdividedOneSimplexVertexMidpoint := by
  apply ComposableArrows.ext₀
  rfl

@[simp]
public theorem subdividedOneSimplexEdgeOne_delta_one :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).δ 1
        subdividedOneSimplexEdgeOne =
      subdividedOneSimplexVertexOne := by
  apply ComposableArrows.ext₀
  rfl

/-- The explicit oriented subdivided interval has boundary `[1] - [0]`. -/
public theorem subdividedOneSimplexFundamentalChain_boundary :
    subdividedOneSimplexFundamentalChain ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0 =
      subdividedOneSimplexBoundaryChain := by
  rw [subdividedOneSimplexFundamentalChain, Preadditive.sub_comp]
  rw [SSet.ιChainComplex_d, SSet.ιChainComplex_d]
  simp [subdividedOneSimplexBoundaryChain, Fin.sum_univ_two, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm]
  abel

end OneSimplex

/-- The oriented fundamental one-chain transported to Mathlib's left-Kan-extension model
`sd Δ[1]`. -/
public noncomputable def subdividedStandardOneFundamentalChain :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj (Δ[1] : SSet.{0})).chainComplex
        (AddCommGrpCat.of ℤ)).X 1 :=
  subdividedOneSimplexFundamentalChain ≫
    (SSet.chainComplexMap (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 1))
      (AddCommGrpCat.of ℤ)).f 1

/-- Its boundary, transported from the explicit `[1] - [0]` model chain. -/
public noncomputable def subdividedStandardOneBoundaryChain :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj (Δ[1] : SSet.{0})).chainComplex
        (AddCommGrpCat.of ℤ)).X 0 :=
  subdividedOneSimplexBoundaryChain ≫
    (SSet.chainComplexMap (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 1))
      (AddCommGrpCat.of ℤ)).f 0

/-- The transported oriented fundamental chain has its transported boundary. -/
public theorem subdividedStandardOneFundamentalChain_boundary :
    subdividedStandardOneFundamentalChain ≫
        ((SSet.sd.obj (Δ[1] : SSet.{0})).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0 =
      subdividedStandardOneBoundaryChain := by
  let F := SSet.chainComplexMap
    (SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 1))
    (AddCommGrpCat.of ℤ)
  change (subdividedOneSimplexFundamentalChain ≫ F.f 1) ≫
      _ = subdividedOneSimplexBoundaryChain ≫ F.f 0
  have hcomm := F.comm 1 0
  have hpre := congrArg (fun k ↦ subdividedOneSimplexFundamentalChain ≫ k) hcomm
  calc
    _ = subdividedOneSimplexFundamentalChain ≫
        (F.f 1 ≫ _ ) := Category.assoc _ _ _
    _ = subdividedOneSimplexFundamentalChain ≫
        (_ ≫ F.f 0) := hpre
    _ = (subdividedOneSimplexFundamentalChain ≫
        ((SimplexCategory.sd.{0}.obj (SimplexCategory.mk 1)).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0) ≫ F.f 0 := (Category.assoc _ _ _).symm
    _ = _ := by rw [subdividedOneSimplexFundamentalChain_boundary]

/-- The oriented barycentric subdivision one-chain associated to an arbitrary one-simplex. -/
public noncomputable def barycentricSubdivisionOneChain
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 1))) :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 1 :=
  subdividedStandardOneFundamentalChain ≫
    (SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm x))
      (AddCommGrpCat.of ℤ)).f 1

/-- The transported boundary of the barycentric subdivision of an arbitrary one-simplex. -/
public noncomputable def barycentricSubdivisionOneBoundary
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 1))) :
    AddCommGrpCat.of ℤ ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 0 :=
  subdividedStandardOneBoundaryChain ≫
    (SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm x))
      (AddCommGrpCat.of ℤ)).f 0

/-- The oriented subdivided chain of every one-simplex has its transported oriented boundary. -/
public theorem barycentricSubdivisionOneChain_boundary
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 1))) :
    barycentricSubdivisionOneChain X x ≫
        ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).d 1 0 =
      barycentricSubdivisionOneBoundary X x := by
  let F := SSet.chainComplexMap (SSet.sd.map (SSet.yonedaEquiv.symm x))
    (AddCommGrpCat.of ℤ)
  change (subdividedStandardOneFundamentalChain ≫ F.f 1) ≫ _ =
    subdividedStandardOneBoundaryChain ≫ F.f 0
  have hcomm := F.comm 1 0
  have hpre := congrArg (fun k ↦ subdividedStandardOneFundamentalChain ≫ k) hcomm
  calc
    _ = subdividedStandardOneFundamentalChain ≫ (F.f 1 ≫ _) := Category.assoc _ _ _
    _ = subdividedStandardOneFundamentalChain ≫ (_ ≫ F.f 0) := hpre
    _ = (subdividedStandardOneFundamentalChain ≫
        ((SSet.sd.obj (Δ[1] : SSet.{0})).chainComplex
          (AddCommGrpCat.of ℤ)).d 1 0) ≫ F.f 0 := (Category.assoc _ _ _).symm
    _ = _ := by rw [subdividedStandardOneFundamentalChain_boundary]

/-- The degree-one component of the oriented barycentric subdivision operator. -/
public noncomputable def barycentricSubdivisionChainMapOne (X : SSet.{0}) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X 1 ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 1 :=
  Sigma.desc (barycentricSubdivisionOneChain X)

@[reassoc (attr := simp)]
public theorem iota_barycentricSubdivisionChainMapOne
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 1))) :
    X.ιChainComplex x ≫ barycentricSubdivisionChainMapOne X =
      barycentricSubdivisionOneChain X x := by
  apply Sigma.ι_desc

/-- The oriented subdivided one-chain attached to a simplex is natural in the ambient simplicial
set. -/
public theorem barycentricSubdivisionOneChain_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y)
    (x : X.obj (Opposite.op (SimplexCategory.mk 1))) :
    barycentricSubdivisionOneChain Y (f.app _ x) =
      barycentricSubdivisionOneChain X x ≫
        (SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ)).f 1 := by
  rw [barycentricSubdivisionOneChain, barycentricSubdivisionOneChain]
  rw [← SSet.yonedaEquiv_symm_comp]
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hsd := SSet.sd.map_comp (SSet.yonedaEquiv.symm x) f
  have hmap := F.congr_map hsd
  have h₁ := congrArg (fun k ↦ k.f 1) hmap
  rw [h₁]
  rw [Functor.map_comp]
  rfl

/-- The degree-one barycentric subdivision components are natural. -/
public theorem barycentricSubdivisionChainMapOne_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f 1 ≫
        barycentricSubdivisionChainMapOne Y =
      barycentricSubdivisionChainMapOne X ≫
        (SSet.chainComplexMap (SSet.sd.map f) (AddCommGrpCat.of ℤ)).f 1 := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    iota_barycentricSubdivisionChainMapOne]
  rw [← Category.assoc, iota_barycentricSubdivisionChainMapOne,
    barycentricSubdivisionOneChain_naturality]

/-- The exact degree-one chain condition joining the constructed degree-zero and degree-one
components of barycentric subdivision. -/
public def BarycentricSubdivisionChainConditionOne (X : SSet.{0}) : Prop :=
  barycentricSubdivisionChainMapOne X ≫
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).d 1 0 =
    (X.chainComplex (AddCommGrpCat.of ℤ)).d 1 0 ≫
      barycentricSubdivisionChainMapZero X

/-- The degree-one chain condition is exactly the assertion that the explicit transported
boundary of every subdivided edge agrees with subdivision of its ordinary boundary. -/
public theorem barycentricSubdivisionChainConditionOne_iff
    (X : SSet.{0}) :
    BarycentricSubdivisionChainConditionOne X ↔
      ∀ x : X.obj (Opposite.op (SimplexCategory.mk 1)),
        barycentricSubdivisionOneBoundary X x =
          (X.ιChainComplex x ≫
            (X.chainComplex (AddCommGrpCat.of ℤ)).d 1 0) ≫
              barycentricSubdivisionChainMapZero X := by
  constructor
  · intro h x
    have hx := congrArg (fun k ↦ X.ιChainComplex x ≫ k) h
    rw [← Category.assoc, iota_barycentricSubdivisionChainMapOne,
      barycentricSubdivisionOneChain_boundary] at hx
    exact hx
  · intro h
    apply X.chainComplex_hom_ext
    intro x
    rw [← Category.assoc, iota_barycentricSubdivisionChainMapOne,
      barycentricSubdivisionOneChain_boundary]
    simpa only [Category.assoc] using h x

end SphereSixComplex
