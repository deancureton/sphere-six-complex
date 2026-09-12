module

public import SphereSixComplex.Prerequisites.Topology.IntegralMayerVietorisTheorem
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Homology vanishing from Mayer--Vietoris and equal finite ranks

If a union has vanishing homology in degree `k` and its degree-`k` difference map is between
free abelian groups of the same finite rank, exactness makes that map an isomorphism.
Surjectivity of the next difference map then gives vanishing in degree `k + 1`.
-/

@[expose] public section

open SphereSixComplex

namespace SphereSixComplex.IntegralMayerVietoris

/-- Equal finite ranks turn degree-`k` surjectivity into injectivity. -/
public theorem subsingleton_homology_succ
    {X : Type} [TopologicalSpace X] (U V : Set X)
    (h : ExactSequence U V) (k n : ℕ)
    (eS : IntegralSingularHomology k (U ∩ V : Set X) ≃+ (Fin n → ℤ))
    (eT : (IntegralSingularHomology k U × IntegralSingularHomology k V) ≃+
      (Fin n → ℤ))
    (hOne : Subsingleton (IntegralSingularHomology k (U ∪ V : Set X)))
    (hTwo : Function.Surjective (differenceMap U V (k + 1))) :
    Subsingleton (IntegralSingularHomology (k + 1) (U ∪ V : Set X)) := by
  obtain ⟨boundary, he⟩ := h
  have hd : Function.Surjective (differenceMap U V k) := by
    intro y
    exact ((he k).2.2 y).mp (hOne.elim _ _)
  let f : Module.End ℤ (Fin n → ℤ) :=
    ((eT.toAddMonoidHom.comp (differenceMap U V k)).comp
      eS.symm.toAddMonoidHom).toIntLinearMap
  have hfSurj : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := hd (eT.symm y)
    refine ⟨eS x, ?_⟩
    simpa [f] using congrArg eT hx
  have hf := Module.End.injective_of_surjective ℤ (Fin n → ℤ) hfSurj
  have hdInj : Function.Injective (differenceMap U V k) := by
    intro x y hxy
    apply eS.injective
    apply hf
    simpa [f] using congrArg eT hxy
  have hz : ∀ z : IntegralSingularHomology (k + 1) (U ∪ V : Set X), z = 0 := by
    intro z
    have hb : boundary k z = 0 := by
      apply hdInj
      have hh := ((he k).2.1 (boundary k z)).mpr ⟨z, rfl⟩
      simpa using hh
    obtain ⟨w, rfl⟩ := ((he k).1 z).mp hb
    obtain ⟨v, rfl⟩ := hTwo w
    exact ((he (k + 1)).2.2 (differenceMap U V (k + 1) v)).mpr ⟨v, rfl⟩
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

end SphereSixComplex.IntegralMayerVietoris
