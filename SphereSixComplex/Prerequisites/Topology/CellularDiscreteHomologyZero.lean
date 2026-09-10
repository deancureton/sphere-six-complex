module

public import SphereSixComplex.Prerequisites.Topology.CellularIntervalFundamentalClass
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace SphereSixComplex

public def cwIntegralPointClass (X : TopCat) (x : X) :
    AddCommGrpCat.of ℤ ⟶ (cwIntegralSingularChainComplexObj X).homology 0 :=
  (cwIntegralSingularChainComplexObj X).liftCycles (cwIntegralPointChain X x) 0
    (by simp) (by simp) ≫ (cwIntegralSingularChainComplexObj X).homologyπ 0

public def cwDiscreteComponentWeight (X : TopCat) [TotallyDisconnectedSpace X]
    (w : X → ℤ) : (TopCat.toSSet.obj X).π₀ → ℤ :=
  SSet.π₀.lift (fun x ↦ w (TopCat.toSSetObj₀Equiv x)) (by
    intro x y e
    let p := TopCat.toSSetObj₁Equiv e.edge
    have he := TotallyDisconnectedSpace.eq_of_continuous
      (fun t : unitInterval ↦ p (TopCat.I.homeomorph.symm t))
      (p.hom.continuous.comp TopCat.I.homeomorph.symm.continuous) 0 1
    change p 0 = p 1 at he
    simpa [p] using congrArg w he)

public def cwDiscreteHomologyZeroWeight (X : TopCat) [TotallyDisconnectedSpace X]
    (w : X → ℤ) : (cwIntegralSingularChainComplexObj X).homology 0 ⟶ AddCommGrpCat.of ℤ :=
  ((TopCat.toSSet.obj X).homology₀Iso (AddCommGrpCat.of ℤ)).hom ≫
    Sigma.desc (fun c ↦ cwDiscreteComponentWeight X w c • 𝟙 (AddCommGrpCat.of ℤ))

public theorem cwIntegralPointClass_weight (X : TopCat) [TotallyDisconnectedSpace X]
    (w : X → ℤ) (x : X) :
    cwIntegralPointClass X x ≫ cwDiscreteHomologyZeroWeight X w =
      w x • 𝟙 (AddCommGrpCat.of ℤ) := by
  change ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).liftCycles
    ((TopCat.toSSet.obj X).ιChainComplex (TopCat.toSSetObj₀Equiv.symm x)) 0
      (by simp) (by simp) ≫
    ((TopCat.toSSet.obj X).chainComplex (AddCommGrpCat.of ℤ)).homologyπ 0 ≫
    (((TopCat.toSSet.obj X).homology₀Iso (AddCommGrpCat.of ℤ)).hom ≫ _) = _
  rw [SSet.liftCycles_ιChainComplex_homologyπ_homology₀Iso_hom_assoc]
  simp [cwDiscreteComponentWeight]

public theorem cwRelativePathClass_boundary_pointClasses {A X : TopCat} (i : A ⟶ X) [Mono i]
    (p : TopCat.I ⟶ X) (a b : A) (ha : p 0 = i a) (hb : p 1 = i b) :
    cwRelativePathClass i p a b ha hb ≫ cwRelativeIntegralSingularBoundary i 0 =
      cwIntegralPointClass A b - cwIntegralPointClass A a := by
  rw [cwRelativePathClass_boundary]
  unfold cwIntegralPointClass
  rw [← Preadditive.sub_comp]
  congr 1
  rw [← cancel_mono ((cwIntegralSingularChainComplexObj A).iCycles 0)]
  simp

public theorem cwRelativePathClass_boundary_weight {A X : TopCat}
    [TotallyDisconnectedSpace A] (i : A ⟶ X) [Mono i]
    (p : TopCat.I ⟶ X) (a b : A) (ha : p 0 = i a) (hb : p 1 = i b)
    (w : A → ℤ) :
    cwRelativePathClass i p a b ha hb ≫ cwRelativeIntegralSingularBoundary i 0 ≫
      cwDiscreteHomologyZeroWeight A w = (w b - w a) • 𝟙 (AddCommGrpCat.of ℤ) := by
  rw [← Category.assoc, cwRelativePathClass_boundary_pointClasses,
    Preadditive.sub_comp, cwIntegralPointClass_weight, cwIntegralPointClass_weight, sub_zsmul]
  exact sub_eq_add_neg _ _

public theorem cyclicEvaluation_bijective {A : Type} [AddCommGroup A]
    (o : A ≃+ ℤ) (l : A →+ ℤ) (c : A) (hc : l c = 1) : Function.Bijective l := by
  have repr (x : A) : x = o x • o.symm 1 := by
    apply o.injective
    simp
  have hn : l (o.symm 1) ≠ 0 := by
    intro h
    have hc' := hc
    rw [repr c, map_zsmul, h, smul_zero] at hc'
    norm_num at hc'
  constructor
  · intro x y h
    apply o.injective
    apply mul_right_cancel₀ hn
    have hx := congrArg l (repr x)
    have hy := congrArg l (repr y)
    simpa using (hx.symm.trans h).trans hy
  · intro z
    refine ⟨z • c, ?_⟩
    simp [hc]

public def cyclicEvaluationEquiv {A : Type} [AddCommGroup A]
    (o : A ≃+ ℤ) (l : A →+ ℤ) (c : A) (hc : l c = 1) : A ≃+ ℤ :=
  AddEquiv.ofBijective l (cyclicEvaluation_bijective o l c hc)

end SphereSixComplex
