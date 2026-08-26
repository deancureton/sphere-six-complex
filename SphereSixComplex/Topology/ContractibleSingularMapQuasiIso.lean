module

public import SphereSixComplex.Topology.StandardSimplexSimplicialSingularComparison
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance

/-!
# Singular chains of maps between contractible spaces

Every specified continuous map between two contractible spaces is itself a homotopy equivalence.
Consequently its singular-chain map is a quasi-isomorphism, with arbitrary coefficients.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap Simplicial

namespace SphereSixComplex

variable {X Y : Type}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Replacing the forward map of a homotopy equivalence by a homotopic map preserves the bundled
homotopy equivalence. -/
public noncomputable def homotopyEquivOfHomotopicTo
    (f : C(X, Y)) (e : X ≃ₕ Y) (h : f.Homotopic e.toFun) : X ≃ₕ Y where
  toFun := f
  invFun := e.invFun
  left_inv := (ContinuousMap.Homotopic.comp (.refl e.invFun) h).trans e.left_inv
  right_inv := (ContinuousMap.Homotopic.comp h (.refl e.invFun)).trans e.right_inv

/-- Any specified continuous map between contractible spaces carries a homotopy equivalence. -/
public noncomputable def homotopyEquivOfMapBetweenContractibleSpaces
    [ContractibleSpace X] [ContractibleSpace Y] (f : C(X, Y)) : X ≃ₕ Y := by
  let e := Classical.choice (ContractibleSpace.hequiv X Y)
  let hnull := id_nullhomotopic Y
  let y := Classical.choose hnull
  let hy := Classical.choose_spec hnull
  have hf : f.Homotopic (ContinuousMap.const X y) := by
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp] using
      ContinuousMap.Homotopic.comp hy (.refl f)
  have he : e.toFun.Homotopic (ContinuousMap.const X y) := by
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp] using
      ContinuousMap.Homotopic.comp hy (.refl e.toFun)
  exact homotopyEquivOfHomotopicTo f e (hf.trans he.symm)

/-- Applying singular chains with arbitrary coefficients to the forward map of a homotopy
equivalence gives a quasi-isomorphism. -/
public theorem singularChainMap_quasiIso_of_homotopyEquiv
    (R : AddCommGrpCat) (e : X ≃ₕ Y) :
    QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom e.toFun)) R) := by
  rw [quasiIso_iff]
  intro k
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso (singularHomologyIsoOfHomotopyEquiv R k e).hom
  infer_instance

/-- The singular-chain map of any continuous map between contractible spaces is a
quasi-isomorphism. -/
public theorem singularChainMap_quasiIso_of_contractibleSpaces
    [ContractibleSpace X] [ContractibleSpace Y]
    (R : AddCommGrpCat) (f : C(X, Y)) :
    QuasiIso (SSet.chainComplexMap
      (TopCat.toSSet.map (TopCat.ofHom f)) R) := by
  exact singularChainMap_quasiIso_of_homotopyEquiv R
    (homotopyEquivOfMapBetweenContractibleSpaces f)

/-- The canonical standard-simplex comparison followed by any continuous map to a contractible
space. -/
public noncomputable def standardSimplexToContractibleSingularChainMap
    {Z : Type} [TopologicalSpace Z] (R : AddCommGrpCat) (n : ℕ)
    (f : C((SSet.toTop.obj (Δ[n] : SSet.{0}) : Type), Z)) :
    (Δ[n] : SSet.{0}).chainComplex R ⟶
      (TopCat.toSSet.obj (TopCat.of Z)).chainComplex R :=
  simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R ≫
    SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) R

/-- Every such standard-simplex-to-contractible-space comparison is a quasi-isomorphism, with
arbitrary coefficients. -/
public theorem standardSimplexToContractibleSingularChainMap_quasiIso
    {Z : Type} [TopologicalSpace Z] [ContractibleSpace Z]
    (R : AddCommGrpCat) (n : ℕ)
    (f : C((SSet.toTop.obj (Δ[n] : SSet.{0}) : Type), Z)) :
    QuasiIso (standardSimplexToContractibleSingularChainMap R n f) := by
  let _ : ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
    standardSimplexRealization_contractibleSpace n
  let hstandard : QuasiIso
      (simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R) :=
    standardSimplex_simplicialToRealizationSingularChainMap_quasiIso R n
  let htarget : QuasiIso
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f)) R) :=
    singularChainMap_quasiIso_of_contractibleSpaces R f
  unfold standardSimplexToContractibleSingularChainMap
  infer_instance

end SphereSixComplex
