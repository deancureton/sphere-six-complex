module

public import SphereSixComplex.Topology.CellularOrientationAudit
public import Mathlib.Topology.Homotopy.TopCat.ZerothHomotopy

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicTopology
namespace SphereSixComplex

public def cwIntegralPointChain (X : TopCat) (x : X) :
    AddCommGrpCat.of ℤ ⟶ (CWIntegralSingularChainComplexObj X).X 0 :=
  (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x)

public def cwIntegralPathChain {X : TopCat} (p : TopCat.I ⟶ X) :
    AddCommGrpCat.of ℤ ⟶ (CWIntegralSingularChainComplexObj X).X 1 :=
  (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₁Equiv.symm p)

public theorem cwIntegralPathChain_boundary {X : TopCat} (p : TopCat.I ⟶ X) :
    cwIntegralPathChain p ≫ (CWIntegralSingularChainComplexObj X).d 1 0 =
      cwIntegralPointChain X (p 1) - cwIntegralPointChain X (p 0) := by
  change (TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₁Equiv.symm p) ≫
    ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).d 1 0 = _
  simp [SSet.ιChainComplex_d, Fin.sum_univ_two, cwIntegralPointChain]
  exact (sub_eq_add_neg (cwIntegralPointChain X (p 1))
    (cwIntegralPointChain X (p 0))).symm

public theorem cwIntegralPointChain_map {A X : TopCat} (i : A ⟶ X) (a : A) :
    cwIntegralPointChain A a ≫ (cwIntegralSingularChainMapObj i).f 0 =
      cwIntegralPointChain X (i a) := by
  change (TopCat.toSSet.obj A).ιChainComplex (TopCat.toSSetObj₀Equiv.symm a) ≫
    (SSet.chainComplexMap (TopCat.toSSet.map i) (AddCommGrpCat.of ℤ)).f 0 = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

public def cwRelativePathChain {A X : TopCat} (i : A ⟶ X) (p : TopCat.I ⟶ X) :
    AddCommGrpCat.of ℤ ⟶ (CWRelativeIntegralSingularChainComplex i).X 1 :=
  cwIntegralPathChain p ≫ (cwRelativeIntegralSingularChainProjection i).f 1

public theorem cwRelativePathChain_cycle {A X : TopCat} (i : A ⟶ X)
    (p : TopCat.I ⟶ X) (a b : A) (ha : p 0 = i a) (hb : p 1 = i b) :
    cwRelativePathChain i p ≫ (CWRelativeIntegralSingularChainComplex i).d 1 0 = 0 := by
  unfold cwRelativePathChain
  rw [Category.assoc, (cwRelativeIntegralSingularChainProjection i).comm,
    ← Category.assoc, cwIntegralPathChain_boundary, ha, hb,
    ← cwIntegralPointChain_map i a, ← cwIntegralPointChain_map i b,
    ← Preadditive.sub_comp, Category.assoc]
  have h := congrArg (fun f ↦ f.f 0) (cwRelativeIntegralSingularShortComplex i).zero
  change (cwIntegralSingularChainMapObj i).f 0 ≫
    (cwRelativeIntegralSingularChainProjection i).f 0 = 0 at h
  rw [h]
  exact Limits.comp_zero

public def cwRelativePathClass {A X : TopCat} (i : A ⟶ X)
    (p : TopCat.I ⟶ X) (a b : A) (ha : p 0 = i a) (hb : p 1 = i b) :
    AddCommGrpCat.of ℤ ⟶ (CWRelativeIntegralSingularChainComplex i).homology 1 :=
  (CWRelativeIntegralSingularChainComplex i).liftCycles (cwRelativePathChain i p) 0
    (by simp) (cwRelativePathChain_cycle i p a b ha hb) ≫
      (CWRelativeIntegralSingularChainComplex i).homologyπ 1

public theorem cwRelativePathClass_boundary {A X : TopCat} (i : A ⟶ X) [Mono i]
    (p : TopCat.I ⟶ X) (a b : A) (ha : p 0 = i a) (hb : p 1 = i b) :
    cwRelativePathClass i p a b ha hb ≫ cwRelativeIntegralSingularBoundary i 0 =
      (CWIntegralSingularChainComplexObj A).liftCycles
        (cwIntegralPointChain A b - cwIntegralPointChain A a) 0 (by simp) (by simp) ≫
          (CWIntegralSingularChainComplexObj A).homologyπ 0 := by
  have h := (cwRelativeIntegralSingularShortComplex_shortExact i).δ_eq
    1 0 (ComplexShape.down_mk 1 0 (by omega))
    (cwRelativePathChain i p) (cwRelativePathChain_cycle i p a b ha hb)
    (cwIntegralPathChain p) rfl
    (cwIntegralPointChain A b - cwIntegralPointChain A a) (by
      change (cwIntegralPointChain A b - cwIntegralPointChain A a) ≫
        (cwIntegralSingularChainMapObj i).f 0 =
          cwIntegralPathChain p ≫ (CWIntegralSingularChainComplexObj X).d 1 0
      rw [Preadditive.sub_comp, cwIntegralPointChain_map, cwIntegralPointChain_map,
        cwIntegralPathChain_boundary, ha, hb]) 0 (by simp)
  exact h

end SphereSixComplex
