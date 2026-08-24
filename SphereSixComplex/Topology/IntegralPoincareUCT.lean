module

public import SphereSixComplex.Topology.HomologySphere
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Integral Poincare duality and UCT, in homological form

This file records the part of integral Poincare duality and the universal coefficient theorem that
can be stated using Mathlib's existing singular-homology API.  Mathlib does not yet provide
singular cohomology, cap products, or Poincare duality, so the interface below records only the
resulting perfect evaluation pairings.  It is dimension-generic and independent of the application
to Section 7.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology

namespace SphereSixComplex

/-- The homological consequences of integral Poincare duality and the integral UCT in real
dimension `d`.

The first equivalence is the composite
`H_d ≃ H^0 ≃ Hom(H_0, ℤ)`.  In positive degree `k`, the UCT evaluation map becomes an
isomorphism when `H_{k-1}` is free, giving the second family of equivalences after Poincare
duality.  The remaining fields are finite generation and the dimension bound. -/
public structure IntegralPoincareUCTData
    (d : ℕ) (X : Type) [TopologicalSpace X] where
  /-- The top-dimensional Poincare/UCT evaluation pairing. -/
  topHomologyEquivDualZero :
    IntegralSingularHomology d X ≃+ (IntegralSingularHomology 0 X →+ ℤ)
  /-- The complementary-degree pairing when the UCT `Ext` term vanishes. -/
  complementaryHomologyEquivDualOfPreviousFree : ∀ (k : Fin (d + 1)), 0 < k.1 →
    Module.Free ℤ (IntegralSingularHomology (k.1 - 1) X) →
      IntegralSingularHomology (d - k.1) X ≃+
        (IntegralSingularHomology k.1 X →+ ℤ)
  /-- Compact smooth manifolds have finitely generated integral homology. -/
  finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k X)
  /-- Homology vanishes above the real dimension. -/
  homologyAboveDimension : ∀ k, d < k → Subsingleton (IntegralSingularHomology k X)

/-- The dimension-six specialization used by the Section 7 calculation. -/
public abbrev ClosedOrientedSixManifoldHomologyTheory
    (X : Type) [TopologicalSpace X] := IntegralPoincareUCTData 6 X

/-- The alternating integral-homology rank sum through real dimension six. -/
public noncomputable def integralHomologyEulerCharacteristicSix
    (X : Type) [TopologicalSpace X] : ℤ :=
  (Module.finrank ℤ (IntegralSingularHomology 0 X) : ℤ) -
  (Module.finrank ℤ (IntegralSingularHomology 1 X) : ℤ) +
  (Module.finrank ℤ (IntegralSingularHomology 2 X) : ℤ) -
  (Module.finrank ℤ (IntegralSingularHomology 3 X) : ℤ) +
  (Module.finrank ℤ (IntegralSingularHomology 4 X) : ℤ) -
  (Module.finrank ℤ (IntegralSingularHomology 5 X) : ℤ) +
  (Module.finrank ℤ (IntegralSingularHomology 6 X) : ℤ)

namespace ClosedOrientedSixManifoldHomologyTheory

variable {X : Type} [TopologicalSpace X]

private theorem subsingleton_of_addEquiv_to_subsingleton
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H)
    (hH : Subsingleton H) : Subsingleton G := by
  constructor
  intro x y
  apply e.injective
  exact @Subsingleton.elim H hH _ _

private theorem hom_subsingleton_of_domain_subsingleton
    {G : Type} [AddCommGroup G] (hG : Subsingleton G) : Subsingleton (G →+ ℤ) := by
  constructor
  intro f g
  ext x
  have hx : x = 0 := @Subsingleton.elim G hG x 0
  simp only [hx, map_zero]

private theorem moduleFree_of_addEquiv_integer {G : Type} [AddCommGroup G]
    (e : G ≃+ ℤ) : Module.Free ℤ G :=
  Module.Free.of_equiv' (inferInstance : Module.Free ℤ ℤ) e.symm.toIntLinearEquiv

private theorem moduleFree_of_subsingleton {G : Type} [AddCommGroup G]
    (hG : Subsingleton G) : Module.Free ℤ G := by
  let _ : Subsingleton G := hG
  exact inferInstance

private theorem intDual_isTorsionFree {G : Type} [AddCommGroup G] :
    Module.IsTorsionFree ℤ (G →+ ℤ) := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro n f hnf
  by_cases hn : n = 0
  · exact Or.inl hn
  right
  ext x
  have hx := DFunLike.congr_fun hnf x
  simp only [AddMonoidHom.zero_apply, AddMonoidHom.smul_apply, smul_eq_mul] at hx
  exact (mul_eq_zero.mp hx).resolve_left hn

private theorem isTorsionFree_of_injective_to_intDual
    {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ (H →+ ℤ)) (hf : Function.Injective f) : Module.IsTorsionFree ℤ G := by
  let _ : Module.IsTorsionFree ℤ (H →+ ℤ) := intDual_isTorsionFree
  exact Function.Injective.moduleIsTorsionFree f hf (fun n x ↦ map_zsmul f n x)

public theorem homologyFive_subsingleton (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hZero : IntegralSingularHomology 0 X ≃+ ℤ)
    (hOne : Subsingleton (IntegralSingularHomology 1 X)) :
    Subsingleton (IntegralSingularHomology 5 X) := by
  let hFreeZero : Module.Free ℤ (IntegralSingularHomology 0 X) :=
    moduleFree_of_addEquiv_integer hZero
  have hDual : Subsingleton (IntegralSingularHomology 1 X →+ ℤ) :=
    hom_subsingleton_of_domain_subsingleton hOne
  exact subsingleton_of_addEquiv_to_subsingleton
    (T.complementaryHomologyEquivDualOfPreviousFree 1 (by norm_num) hFreeZero) hDual

public theorem homologyFour_subsingleton (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hOne : Subsingleton (IntegralSingularHomology 1 X))
    (hTwo : Subsingleton (IntegralSingularHomology 2 X)) :
    Subsingleton (IntegralSingularHomology 4 X) := by
  let hFreeOne : Module.Free ℤ (IntegralSingularHomology 1 X) :=
    moduleFree_of_subsingleton hOne
  have hDual : Subsingleton (IntegralSingularHomology 2 X →+ ℤ) :=
    hom_subsingleton_of_domain_subsingleton hTwo
  exact subsingleton_of_addEquiv_to_subsingleton
    (T.complementaryHomologyEquivDualOfPreviousFree 2 (by norm_num) hFreeOne) hDual

public theorem homologyThree_isTorsionFree
    (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hTwo : Subsingleton (IntegralSingularHomology 2 X)) :
    Module.IsTorsionFree ℤ (IntegralSingularHomology 3 X) := by
  let hFreeTwo : Module.Free ℤ (IntegralSingularHomology 2 X) :=
    moduleFree_of_subsingleton hTwo
  let e := T.complementaryHomologyEquivDualOfPreviousFree 3 (by norm_num) hFreeTwo
  exact isTorsionFree_of_injective_to_intDual e.toAddMonoidHom e.injective

public noncomputable def homologySixEquivInteger
    (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hZero : IntegralSingularHomology 0 X ≃+ ℤ) :
    IntegralSingularHomology 6 X ≃+ ℤ := by
  let precomp : (IntegralSingularHomology 0 X →+ ℤ) ≃+ (ℤ →+ ℤ) := {
    toFun := fun (f : IntegralSingularHomology 0 X →+ ℤ) ↦
      f.comp hZero.symm.toAddMonoidHom
    invFun := fun (f : ℤ →+ ℤ) ↦ f.comp hZero.toAddMonoidHom
    left_inv f := by
      ext x
      simp
    right_inv f := AddMonoidHom.ext_int (by simp)
    map_add' f g := AddMonoidHom.ext_int rfl }
  let evalOne : (ℤ →+ ℤ) ≃+ ℤ := {
    toFun := fun f ↦ f 1
    invFun := AddMonoidHom.mulLeft
    left_inv := fun f ↦ AddMonoidHom.ext_int (by simp)
    right_inv := by
      intro n
      change n * 1 = n
      exact mul_one n
    map_add' := by simp }
  exact T.topHomologyEquivDualZero.trans (precomp.trans evalOne)

private theorem finrank_zero_of_subsingleton_finite {G : Type} [AddCommGroup G]
    (hFinite : Module.Finite ℤ G) (hG : Subsingleton G) : Module.finrank ℤ G = 0 := by
  let _ : Module.Finite ℤ G := hFinite
  let _ : Subsingleton G := hG
  let _ : Module.Free ℤ G := inferInstance
  exact Module.finrank_eq_zero_of_subsingleton ℤ G

private theorem finrank_one_of_addEquiv_integer {G : Type} [AddCommGroup G]
    (e : G ≃+ ℤ) : Module.finrank ℤ G = 1 := by
  rw [e.toIntLinearEquiv.finrank_eq]
  simp

public theorem homologyThree_subsingleton_of_eulerCharacteristic
    (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hZero : IntegralSingularHomology 0 X ≃+ ℤ)
    (hOne : Subsingleton (IntegralSingularHomology 1 X))
    (hTwo : Subsingleton (IntegralSingularHomology 2 X))
    (hEuler : integralHomologyEulerCharacteristicSix X = 2) :
    Subsingleton (IntegralSingularHomology 3 X) := by
  have hFive := T.homologyFive_subsingleton hZero hOne
  have hFour := T.homologyFour_subsingleton hOne hTwo
  let hSix := T.homologySixEquivInteger hZero
  have h0rank : Module.finrank ℤ (IntegralSingularHomology 0 X) = 1 :=
    finrank_one_of_addEquiv_integer hZero
  have h1rank : Module.finrank ℤ (IntegralSingularHomology 1 X) = 0 :=
    finrank_zero_of_subsingleton_finite (T.finiteHomology 1) hOne
  have h2rank : Module.finrank ℤ (IntegralSingularHomology 2 X) = 0 :=
    finrank_zero_of_subsingleton_finite (T.finiteHomology 2) hTwo
  have h4rank : Module.finrank ℤ (IntegralSingularHomology 4 X) = 0 :=
    finrank_zero_of_subsingleton_finite (T.finiteHomology 4) hFour
  have h5rank : Module.finrank ℤ (IntegralSingularHomology 5 X) = 0 :=
    finrank_zero_of_subsingleton_finite (T.finiteHomology 5) hFive
  have h6rank : Module.finrank ℤ (IntegralSingularHomology 6 X) = 1 :=
    finrank_one_of_addEquiv_integer hSix
  have h3rank : Module.finrank ℤ (IntegralSingularHomology 3 X) = 0 := by
    unfold integralHomologyEulerCharacteristicSix at hEuler
    omega
  let _ : Module.Finite ℤ (IntegralSingularHomology 3 X) := T.finiteHomology 3
  let _ : Module.IsTorsionFree ℤ (IntegralSingularHomology 3 X) :=
    T.homologyThree_isTorsionFree hTwo
  exact Module.finrank_zero_iff.mp h3rank

end ClosedOrientedSixManifoldHomologyTheory

end SphereSixComplex
