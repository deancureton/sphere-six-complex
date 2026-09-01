module

public import SphereSixComplex.Topology.HurewiczWhiteheadStages
public import SphereSixComplex.Topology.CubicalSphereEuclideanComparison
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# A general higher-Hurewicz boundary

Mathlib defines higher homotopy groups using cubical generalized loops, but does not yet provide
the map induced by a continuous map or the Hurewicz homomorphism. This file supplies the former
directly and gives a precise, source- and dimension-independent contract for the latter. The
classical higher Hurewicz theorem may then be retained as one general literature blackbox by
asserting that this contract is inhabited and satisfies the usual connectivity theorem.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology ContinuousMap
open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

/-- Postcomposition of a cubical generalized loop by a continuous map. -/
public def postcomposeGenLoop
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} (f : C(X, Y)) (p : Ω^ N X x) : Ω^ N Y (f x) :=
  ⟨f.comp p.1, fun y hy ↦ congrArg f (p.property y hy)⟩

@[simp]
public theorem postcomposeGenLoop_apply
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} (f : C(X, Y)) (p : Ω^ N X x) (y : I^N) :
    postcomposeGenLoop f p y = f (p y) :=
  rfl

/-- A continuous map induces a map on cubical homotopy groups by postcomposition. -/
public def homotopyGroupMap
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map (postcomposeGenLoop f) fun _ _ h ↦
    h.comp_continuousMap f

@[simp]
public theorem homotopyGroupMap_mk
    {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (p : Ω^ N X x) :
    homotopyGroupMap f x ⟦p⟧ = ⟦postcomposeGenLoop f p⟧ :=
  rfl

/-- The construction contract for the classical natural higher Hurewicz homomorphism. -/
public structure HigherHurewiczMap where
  homomorphism :
    ∀ (n : ℕ) [Nontrivial (Fin n)]
      (X : Type) [TopologicalSpace X] (x : X),
      Additive (HomotopyGroup.Pi n X x) →+ IntegralSingularHomology n X
  naturality :
    ∀ (n : ℕ) [Nontrivial (Fin n)]
      {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) (x : X) (a : Additive (HomotopyGroup.Pi n X x)),
      homomorphism n Y (f x)
          (Additive.ofMul (homotopyGroupMap f x (Additive.toMul a))) =
        integralSingularHomologyMap n f (homomorphism n X x a)
  sphere_realization :
    ∀ (n : ℕ) [Nontrivial (Fin n)]
      (X : Type) [TopologicalSpace X] (x : X)
      (a : Additive (HomotopyGroup.Pi n X x)),
      ∃ f : C((TopCat.sphere n : Type), X),
        ∃ s : IntegralSingularHomology n (TopCat.sphere n : Type),
          integralSingularHomologyMap n f s = homomorphism n X x a

/-- The usual higher Hurewicz isomorphism property. The explicit inequality excludes the
degree-one abelianization theorem. -/
public def HigherHurewiczIsomorphismProperty (H : HigherHurewiczMap) : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n)
    (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X),
    letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
    (∀ k : ℕ, 0 < k → k < n → Subsingleton (HomotopyGroup.Pi k X x)) →
      Function.Bijective (H.homomorphism n X x)

private theorem homotopyGroupPiOne_subsingleton
    (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X] (x : X) :
    Subsingleton (HomotopyGroup.Pi 1 X x) := by
  let e : HomotopyGroup.Pi 1 X x ≃
      FundamentalGroup X x :=
    HomotopyGroup.pi1EquivFundamentalGroup
  exact ⟨fun a b ↦ e.injective (Subsingleton.elim _ _)⟩

/-- A constructed natural Hurewicz map and the general isomorphism theorem imply the former
class-surjectivity boundary. This reduction is axiom-free. -/
public theorem generalHigherHurewiczClassSurjectivity_of_map
    (H : HigherHurewiczMap) (hHurewicz : HigherHurewiczIsomorphismProperty H)
    (n : ℕ) (hn : 2 ≤ n)
    (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X]
    (hLower : ∀ k : ℕ, 0 < k → k < n →
      Subsingleton (IntegralSingularHomology k X)) :
    ∀ c : IntegralSingularHomology n X,
      ∃ f : C((TopCat.sphere n : Type), X),
        ∃ s : IntegralSingularHomology n (TopCat.sphere n : Type),
          integralSingularHomologyMap n f s = c := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  have hPiLower : ∀ k : ℕ, 0 < k → k < n →
      Subsingleton (HomotopyGroup.Pi k X x) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hkPositive hkLess
      by_cases hkOne : k = 1
      · subst k
        exact homotopyGroupPiOne_subsingleton X x
      · have hkTwo : 2 ≤ k := by omega
        let _ : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hkTwo
        have hConnected : ∀ j : ℕ, 0 < j → j < k →
            Subsingleton (HomotopyGroup.Pi j X x) := by
          intro j hjPositive hjLess
          exact ih j hjLess hjPositive (hjLess.trans hkLess)
        have hInjective := (hHurewicz k hkTwo X x hConnected).1
        let _ : Subsingleton (IntegralSingularHomology k X) :=
          hLower k hkPositive hkLess
        exact ⟨fun a b ↦ by
          have hab : Additive.ofMul a = Additive.ofMul b :=
            hInjective (Subsingleton.elim _ _)
          exact congrArg Additive.toMul hab⟩
  let _ : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  intro c
  obtain ⟨a, ha⟩ :=
    (hHurewicz n hn X x hPiLower).2 c
  obtain ⟨f, s, hs⟩ := H.sphere_realization n X x a
  exact ⟨f, s, hs.trans ha⟩

end SphereSixComplex
