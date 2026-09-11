module

public import SphereSixComplex.Prerequisites.Topology.MayerVietoris
public import Mathlib.Algebra.Category.Grp.EpiMono

@[expose] public section

noncomputable section

open CategoryTheory
open scoped ContinuousMap

namespace SphereSixComplex

/-- A rank-one morphism into the standard group of integral singular cycles. -/
public abbrev IntegralSingularCycle (n : ℕ) (X : Type) [TopologicalSpace X] :=
  AddCommGrpCat.of ℤ ⟶ (integralSingularChainComplex X).cycles n

namespace IntegralSingularCycle

variable {n : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

public def chain (c : IntegralSingularCycle n X) :
    AddCommGrpCat.of ℤ ⟶ (integralSingularChainComplex X).X n :=
  c ≫ (integralSingularChainComplex X).iCycles n

public def map (c : IntegralSingularCycle n X) (f : C(X, Y)) :
    IntegralSingularCycle n Y :=
  c ≫ HomologicalComplex.cyclesMap (integralSingularChainMap f) n

public theorem chain_map (c : IntegralSingularCycle n X) (f : C(X, Y)) :
    (c.map f).chain = c.chain ≫ (integralSingularChainMap f).f n := by
  simp only [map, chain, Category.assoc, HomologicalComplex.cyclesMap_i]

public def homologyClass (c : IntegralSingularCycle n X) : IntegralSingularHomology n X :=
  ConcreteCategory.hom (c ≫ (integralSingularChainComplex X).homologyπ n) 1

public theorem homologyClass_map (c : IntegralSingularCycle n X) (f : C(X, Y)) :
    integralSingularHomologyMap n f c.homologyClass = (c.map f).homologyClass := by
  have h : (c ≫ (integralSingularChainComplex X).homologyπ n) ≫
      HomologicalComplex.homologyMap (integralSingularChainMap f) n =
      (c.map f) ≫ (integralSingularChainComplex Y).homologyπ n := by
    simp only [map, Category.assoc, HomologicalComplex.homologyπ_naturality]
  exact DFunLike.congr_fun (congrArg ConcreteCategory.hom h) 1

public theorem homologyClass_eq_of_chain_eq (c d : IntegralSingularCycle n X)
    (h : c.chain = d.chain) : c.homologyClass = d.homologyClass := by
  have hcd : c = d := (cancel_mono ((integralSingularChainComplex X).iCycles n)).mp h
  rw [hcd]

public theorem exists_representative (x : IntegralSingularHomology n X) :
    ∃ c : IntegralSingularCycle n X, c.homologyClass = x := by
  obtain ⟨y, hy⟩ :=
    (AddCommGrpCat.epi_iff_surjective ((integralSingularChainComplex X).homologyπ n)).1
      inferInstance x
  refine ⟨AddCommGrpCat.asHom y, ?_⟩
  change ConcreteCategory.hom
    (AddCommGrpCat.asHom y ≫ (integralSingularChainComplex X).homologyπ n) 1 = x
  rw [CategoryTheory.comp_apply, AddCommGrpCat.asHom_hom_apply, one_zsmul, hy]

end IntegralSingularCycle

end SphereSixComplex
