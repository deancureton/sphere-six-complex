/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.SmoothRecognition
public import SphereSixComplex.Topology.StandardSphereHomologyBase
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Positive integral homology of the standard six-sphere

This file isolates the algebraic output required from the standard hemisphere
Mayer--Vietoris calculation. Contractible spaces already have trivial positive-degree
integral homology in Mathlib; this is proved below from homotopy invariance and the calculation
for totally disconnected spaces.

For the sphere calculation, `StandardSphereMayerVietorisInputs` records exactly the remaining
outputs of singular excision and the standard hemisphere covers: the positive-degree
suspension equivalences, the degree-one edge cases, and the circle generator. The final theorem
proves, without another topological assumption, that these data give
`SixSpherePositiveHomologyInputs`.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Limits Topology

namespace SphereSixComplex

/-! ## Homology of contractible spaces -/

/-- Positive-degree integral homology of a contractible space is a singleton. -/
public theorem subsingleton_integralSingularHomology_of_contractible
    {X : Type} [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) : Subsingleton (IntegralSingularHomology n X) := by
  have hUnit :=
    AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      AddCommGrpCat n (AddCommGrpCat.of ℤ) (TopCat.of Unit) hn
  let _ : Subsingleton (IntegralSingularHomology n Unit) :=
    AddCommGrpCat.subsingleton_of_isZero hUnit
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  let he := integralSingularHomologyEquivOfHomotopyEquiv n e
  exact ⟨fun x y ↦ he.injective (Subsingleton.elim _ _)⟩

/-- Degree-zero integral homology of a contractible space is canonically infinite cyclic. -/
public noncomputable def contractibleDegreeZeroIntegralHomologyEquiv
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IntegralSingularHomology 0 X ≃+ ℤ :=
  (asIso ((TopCat.of X).singularHomology₀ε (AddCommGrpCat.of ℤ)))
    |>.addCommGroupIsoToAddEquiv

/-! ## The finite suspension calculation -/

/-- The positive-degree sphere homology calculation absent from Mathlib. -/
public structure SixSpherePositiveHomologyInputs : Prop where
  degreeSix : Nonempty (IntegralSingularHomology 6 SixSphere ≃+ ℤ)
  otherDegrees :
    ∀ n : ℕ, n ≠ 0 → n ≠ 6 → Subsingleton (IntegralSingularHomology n SixSphere)

/-- The exact algebraic outputs of Mayer--Vietoris for the standard sphere covers through
dimension six.

The shift excludes `k = 0`: ordinary (unreduced) homology does not have a suspension
equivalence in that degree. The two degree-zero edge phenomena are therefore recorded by
`degreeOneVanishing` and `circleTop`. -/
public structure StandardSphereMayerVietorisInputs : Prop where
  suspensionShift :
    ∀ (d k : ℕ), d < 6 → k ≠ 0 →
      Nonempty
        (IntegralSingularHomology (k + 1) (StandardSphere (d + 1)) ≃+
          IntegralSingularHomology k (StandardSphere d))
  degreeOneVanishing :
    ∀ d : ℕ, 2 ≤ d → d ≤ 6 →
      Subsingleton (IntegralSingularHomology 1 (StandardSphere d))
  circleTop : Nonempty (IntegralSingularHomology 1 (StandardSphere 1) ≃+ ℤ)

private theorem subsingleton_of_addEquiv {A B : Type*} [Add A] [Add B]
    (e : A ≃+ B) [Subsingleton B] : Subsingleton A :=
  ⟨fun x y ↦ e.injective (Subsingleton.elim _ _)⟩

/-- The suspension outputs force vanishing strictly between degrees zero and six. -/
public theorem StandardSphereMayerVietorisInputs.lowerDegreeVanishing
    (h : StandardSphereMayerVietorisInputs) (n : ℕ)
    (hnPos : 0 < n) (hnTop : n < 6) :
    Subsingleton (IntegralSingularHomology n SixSphere) := by
  have hnCases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hnCases with rfl | rfl | rfl | rfl | rfl
  · exact h.degreeOneVanishing 6 (by omega) (by omega)
  · obtain ⟨e65⟩ := h.suspensionShift 5 1 (by omega) (by omega)
    letI := h.degreeOneVanishing 5 (by omega) (by omega)
    exact subsingleton_of_addEquiv e65
  · obtain ⟨e65⟩ := h.suspensionShift 5 2 (by omega) (by omega)
    obtain ⟨e54⟩ := h.suspensionShift 4 1 (by omega) (by omega)
    letI := h.degreeOneVanishing 4 (by omega) (by omega)
    exact subsingleton_of_addEquiv (e65.trans e54)
  · obtain ⟨e65⟩ := h.suspensionShift 5 3 (by omega) (by omega)
    obtain ⟨e54⟩ := h.suspensionShift 4 2 (by omega) (by omega)
    obtain ⟨e43⟩ := h.suspensionShift 3 1 (by omega) (by omega)
    letI := h.degreeOneVanishing 3 (by omega) (by omega)
    exact subsingleton_of_addEquiv ((e65.trans e54).trans e43)
  · obtain ⟨e65⟩ := h.suspensionShift 5 4 (by omega) (by omega)
    obtain ⟨e54⟩ := h.suspensionShift 4 3 (by omega) (by omega)
    obtain ⟨e43⟩ := h.suspensionShift 3 2 (by omega) (by omega)
    obtain ⟨e32⟩ := h.suspensionShift 2 1 (by omega) (by omega)
    letI := h.degreeOneVanishing 2 (by omega) (by omega)
    exact subsingleton_of_addEquiv (((e65.trans e54).trans e43).trans e32)

/-- The five positive-degree shifts carry the circle fundamental class to degree six. -/
public theorem StandardSphereMayerVietorisInputs.degreeSix
    (h : StandardSphereMayerVietorisInputs) :
    Nonempty (IntegralSingularHomology 6 SixSphere ≃+ ℤ) := by
  obtain ⟨e65⟩ := h.suspensionShift 5 5 (by omega) (by omega)
  obtain ⟨e54⟩ := h.suspensionShift 4 4 (by omega) (by omega)
  obtain ⟨e43⟩ := h.suspensionShift 3 3 (by omega) (by omega)
  obtain ⟨e32⟩ := h.suspensionShift 2 2 (by omega) (by omega)
  obtain ⟨e21⟩ := h.suspensionShift 1 1 (by omega) (by omega)
  obtain ⟨e10⟩ := h.circleTop
  exact ⟨(((((e65.trans e54).trans e43).trans e32).trans e21).trans e10)⟩

/-- Six positive-degree shifts reduce homology above dimension six to positive homology of
the zero-sphere. -/
public theorem StandardSphereMayerVietorisInputs.aboveDimensionVanishing
    (h : StandardSphereMayerVietorisInputs) (n : ℕ) (hn : 6 < n) :
    Subsingleton (IntegralSingularHomology n SixSphere) := by
  have h10 : n - 1 + 1 = n := by omega
  have h21 : n - 2 + 1 = n - 1 := by omega
  have h32 : n - 3 + 1 = n - 2 := by omega
  have h43 : n - 4 + 1 = n - 3 := by omega
  have h54 : n - 5 + 1 = n - 4 := by omega
  have h65 : n - 6 + 1 = n - 5 := by omega
  obtain ⟨e65⟩ := h.suspensionShift 5 (n - 1) (by omega) (by omega)
  rw [h10] at e65
  obtain ⟨e54⟩ := h.suspensionShift 4 (n - 2) (by omega) (by omega)
  rw [h21] at e54
  obtain ⟨e43⟩ := h.suspensionShift 3 (n - 3) (by omega) (by omega)
  rw [h32] at e43
  obtain ⟨e32⟩ := h.suspensionShift 2 (n - 4) (by omega) (by omega)
  rw [h43] at e32
  obtain ⟨e21⟩ := h.suspensionShift 1 (n - 5) (by omega) (by omega)
  rw [h54] at e21
  obtain ⟨e10⟩ := h.suspensionShift 0 (n - 6) (by omega) (by omega)
  rw [h65] at e10
  letI := standardSphereZero_positiveHomology (n - 6) (by omega)
  exact
    subsingleton_of_addEquiv
      (((((e65.trans e54).trans e43).trans e32).trans e21).trans e10)

/-- The standard sphere Mayer--Vietoris outputs assemble the complete positive-degree
integral homology calculation of `S⁶`. -/
public theorem sixSpherePositiveHomologyInputs_of_mayerVietorisInputs
    (h : StandardSphereMayerVietorisInputs) : SixSpherePositiveHomologyInputs where
  degreeSix := h.degreeSix
  otherDegrees n hnZero hnSix := by
    by_cases hnLow : n < 6
    · exact h.lowerDegreeVanishing n (by omega) hnLow
    · exact h.aboveDimensionVanishing n (by omega)

end SphereSixComplex
