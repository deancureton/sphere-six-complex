module

public import SphereSixComplex.Topology.EstablishedSphereHomology
public import SphereSixComplex.Topology.SectionSevenMayerVietorisHomologyAssembly
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Completing the Section 7 homology calculation by six-manifold duality

The Mayer--Vietoris calculation supplies the vanishing of `H₁` and `H₂`.  This file isolates the
standard general-topology input needed to finish the calculation for a compact connected complex
threefold: finite generation and dimension bounds, integral Poincaré duality, the universal
coefficient theorem, and Euler--Poincaré.  No field of the general-topology package records the
desired homology groups of the glued space.

Mathlib currently has neither singular cohomology nor Poincaré duality for manifolds.  The exact
UCT and duality interface below, and the theorem supplying it for compact complex threefolds, are
therefore isolated as an established general theorem.  The final Section 7 theorem additionally
requires the numerical Euler characteristic `2`; that geometric calculation is deliberately an
explicit hypothesis.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory
open scoped ContDiff Manifold

namespace SphereSixComplex

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

/-- The exact part of integral Poincaré duality and UCT used in real dimension six.

`cohomology k` models `H^k(X; ℤ)`.  The evaluation map is the UCT quotient
`H^k(X; ℤ) → Hom(H_k(X; ℤ), ℤ)`.  Its kernel is `Ext(H_{k-1}(X; ℤ), ℤ)`, so it is injective when
the preceding homology group is free. -/
public structure ClosedOrientedSixManifoldHomologyTheory
    (X : Type) [TopologicalSpace X] where
  /-- Integral singular cohomology in degrees zero through six. -/
  cohomology : Fin 7 → AddCommGrpCat
  /-- Cap product with the fundamental class. -/
  poincareDuality : ∀ k : Fin 7,
    cohomology k ≃+ IntegralSingularHomology (6 - k.1) X
  /-- The UCT evaluation map to the integral dual of homology. -/
  uctEvaluation : ∀ k : Fin 7,
    cohomology k →+ (IntegralSingularHomology k.1 X →+ ℤ)
  /-- The UCT evaluation map is always onto. -/
  uctEvaluation_surjective : ∀ k, Function.Surjective (uctEvaluation k)
  /-- In degree zero there is no `Ext` term. -/
  uctEvaluation_zero_injective : Function.Injective (uctEvaluation 0)
  /-- A free preceding homology group kills the UCT `Ext` term. -/
  uctEvaluation_injective_of_previous_free : ∀ (k : Fin 7), 0 < k.1 →
    Module.Free ℤ (IntegralSingularHomology (k.1 - 1) X) →
      Function.Injective (uctEvaluation k)
  /-- Compact manifolds have finitely generated integral homology. -/
  finiteHomology : ∀ k, Module.Finite ℤ (IntegralSingularHomology k X)
  /-- A six-manifold has no homology above its dimension. -/
  homologyAboveDimension : ∀ k, 6 < k → Subsingleton (IntegralSingularHomology k X)

/-- Classical finite-CW, integral UCT, and integral Poincaré-duality package for a compact complex
threefold.  A complex atlas gives the real orientation canonically; compactness gives closedness,
and the self model has no boundary.  Hausdorffness and second countability are included because
they are needed by the standard finite-CW-type theorem for manifolds. -/
public axiom establishedCompactComplexThreefoldHomologyTheory
    (X : Type) [TopologicalSpace X] [ChartedSpace ComplexModel X]
    [T2Space X] [SecondCountableTopology X]
    (hManifold : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ X)
    (hCompact : CompactSpace X) :
    ClosedOrientedSixManifoldHomologyTheory X

/-- Degree-zero homology of a connected complex manifold is infinite cyclic. -/
public noncomputable def connectedComplexManifoldHomologyZeroEquivInteger
    (X : Type) [TopologicalSpace X] [ChartedSpace ComplexModel X]
    (hConnected : ConnectedSpace X) : IntegralSingularHomology 0 X ≃+ ℤ := by
  let _ : ConnectedSpace X := hConnected
  let _ : LocallyPathConnectedSpace X :=
    ChartedSpace.locallyPathConnectedSpace ComplexModel X
  let _ : PathConnectedSpace X := PathConnectedSpace.of_locallyPathConnectedSpace
  exact (asIso ((TopCat.of X).singularHomology₀ε (AddCommGrpCat.of ℤ)))
    |>.addCommGroupIsoToAddEquiv

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

private theorem subsingleton_of_injective_to_subsingleton
    {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H)
    (hf : Function.Injective f) (hH : Subsingleton H) : Subsingleton G := by
  constructor
  intro x y
  apply hf
  exact @Subsingleton.elim H hH _ _

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
  have hEval : Function.Injective (T.uctEvaluation (1 : Fin 7)) :=
    T.uctEvaluation_injective_of_previous_free 1 (by omega) hFreeZero
  have hDual : Subsingleton (IntegralSingularHomology 1 X →+ ℤ) :=
    hom_subsingleton_of_domain_subsingleton hOne
  have hCohomology : Subsingleton (T.cohomology 1) :=
    subsingleton_of_injective_to_subsingleton _ hEval hDual
  exact subsingleton_of_addEquiv_to_subsingleton (T.poincareDuality 1).symm hCohomology

public theorem homologyFour_subsingleton (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hOne : Subsingleton (IntegralSingularHomology 1 X))
    (hTwo : Subsingleton (IntegralSingularHomology 2 X)) :
    Subsingleton (IntegralSingularHomology 4 X) := by
  let hFreeOne : Module.Free ℤ (IntegralSingularHomology 1 X) :=
    moduleFree_of_subsingleton hOne
  have hEval : Function.Injective (T.uctEvaluation (2 : Fin 7)) :=
    T.uctEvaluation_injective_of_previous_free 2 (by omega) hFreeOne
  have hDual : Subsingleton (IntegralSingularHomology 2 X →+ ℤ) :=
    hom_subsingleton_of_domain_subsingleton hTwo
  have hCohomology : Subsingleton (T.cohomology 2) :=
    subsingleton_of_injective_to_subsingleton _ hEval hDual
  exact subsingleton_of_addEquiv_to_subsingleton (T.poincareDuality 2).symm hCohomology

public theorem homologyThree_isTorsionFree
    (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hTwo : Subsingleton (IntegralSingularHomology 2 X)) :
    Module.IsTorsionFree ℤ (IntegralSingularHomology 3 X) := by
  let hFreeTwo : Module.Free ℤ (IntegralSingularHomology 2 X) :=
    moduleFree_of_subsingleton hTwo
  have hEval : Function.Injective (T.uctEvaluation (3 : Fin 7)) :=
    T.uctEvaluation_injective_of_previous_free 3 (by omega) hFreeTwo
  let f : IntegralSingularHomology 3 X →+
      (IntegralSingularHomology 3 X →+ ℤ) :=
    (T.uctEvaluation 3).comp (T.poincareDuality 3).symm.toAddMonoidHom
  have hf : Function.Injective f := hEval.comp (T.poincareDuality 3).symm.injective
  exact isTorsionFree_of_injective_to_intDual f hf

public noncomputable def homologySixEquivInteger
    (T : ClosedOrientedSixManifoldHomologyTheory X)
    (hZero : IntegralSingularHomology 0 X ≃+ ℤ) :
    IntegralSingularHomology 6 X ≃+ ℤ := by
  let evalEquiv : T.cohomology 0 ≃+ (IntegralSingularHomology 0 X →+ ℤ) :=
    AddEquiv.ofBijective (T.uctEvaluation 0)
      ⟨T.uctEvaluation_zero_injective, T.uctEvaluation_surjective 0⟩
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
  exact (T.poincareDuality 0).symm.trans (evalEquiv.trans (precomp.trans evalOne))

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

private noncomputable def addEquivOfSubsingleton
    {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (hG : Subsingleton G) (hH : Subsingleton H) : G ≃+ H where
  toFun := 0
  invFun := 0
  left_inv x := @Subsingleton.elim G hG _ _
  right_inv x := @Subsingleton.elim H hH _ _
  map_add' _ _ := by simp

namespace OpenEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly

variable {A : OpenEmbeddingStarData}

/-- The source-faithful H₁/H₂ Mayer--Vietoris computation, together with standard closed oriented
six-manifold topology and Euler characteristic `2`, gives the complete integral homology of the
six-sphere. -/
public theorem hasIntegralHomologyOfSixSphere_of_closedComplexThreefold
    (H : A.SectionSevenMayerVietorisHomologyAssembly)
    [ChartedSpace ComplexModel (A.SectionSevenMayerVietorisSpace)]
    [T2Space (A.SectionSevenMayerVietorisSpace)]
    [SecondCountableTopology (A.SectionSevenMayerVietorisSpace)]
    (hManifold : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (A.SectionSevenMayerVietorisSpace))
    (hCompact : CompactSpace (A.SectionSevenMayerVietorisSpace))
    (hConnected : ConnectedSpace (A.SectionSevenMayerVietorisSpace))
    (hEuler : integralHomologyEulerCharacteristicSix
      (A.SectionSevenMayerVietorisSpace) = 2) :
    HasIntegralHomologyOfSixSphere (A.SectionSevenMayerVietorisSpace) := by
  let T := establishedCompactComplexThreefoldHomologyTheory
    (A.SectionSevenMayerVietorisSpace) hManifold hCompact
  let hZero := connectedComplexManifoldHomologyZeroEquivInteger
    (A.SectionSevenMayerVietorisSpace) hConnected
  let hOne := H.homologyOne_subsingleton
  let hTwo := H.homologyTwo_subsingleton
  let hThree := T.homologyThree_subsingleton_of_eulerCharacteristic
    hZero hOne hTwo hEuler
  let hFour := T.homologyFour_subsingleton hOne hTwo
  let hFive := T.homologyFive_subsingleton hZero hOne
  let hSix := T.homologySixEquivInteger hZero
  have hRealization : SectionSevenHomologyRealization
      (A.SectionSevenMayerVietorisSpace) := by
    intro k
    by_cases hk0 : k = 0
    · subst k
      exact ⟨hZero.trans sectionSevenComputedHomologyZeroEquivInteger.symm⟩
    by_cases hk6 : k = 6
    · subst k
      exact ⟨hSix.trans sectionSevenComputedHomologySixEquivInteger.symm⟩
    have hComputed : Subsingleton (SectionSevenComputedHomology k) :=
      sectionSevenComputedHomology_middle_subsingleton k hk0 hk6
    have hActual : Subsingleton (IntegralSingularHomology k
        (A.SectionSevenMayerVietorisSpace)) := by
      rcases Nat.lt_trichotomy k 3 with hk | rfl | hk
      · interval_cases k
        · exact False.elim (hk0 rfl)
        · exact hOne
        · exact hTwo
      · exact hThree
      · rcases lt_or_ge k 7 with hk7 | hk7
        · interval_cases k
          · exact hFour
          · exact hFive
          · exact False.elim (hk6 rfl)
        · exact T.homologyAboveDimension k (by omega)
    exact ⟨addEquivOfSubsingleton hActual hComputed⟩
  exact hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations
    hRealization establishedSixSphereSectionSevenHomology

end OpenEmbeddingStarData.SectionSevenMayerVietorisHomologyAssembly

end SphereSixComplex
