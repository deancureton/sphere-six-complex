module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Euler characteristic of finite exact sequences over the integers

Mathlib's finite exact-sequence Euler theorem is stated over division rings. Integral homology
groups are finitely generated `Int`-modules, so this module supplies the corresponding result using
rank-nullity for commutative domains.
-/

@[expose] public section

namespace SphereSixComplex

private lemma int_finrank_eq_of_module_structures {M : Type*} [AddCommGroup M]
    (moduleOne moduleTwo : Module Int M) :
    @Module.finrank Int M _ _ moduleOne = @Module.finrank Int M _ _ moduleTwo := by
  have h : moduleOne = moduleTwo := Subsingleton.elim _ _
  cases h
  rfl

private lemma integral_finrank_range_add_finrank_ker {M N : Type*}
    [AddCommGroup M] [Module Int M] [Module.Finite Int M]
    [AddCommGroup N] [Module Int N] (f : M →ₗ[Int] N) :
    Module.finrank Int f.range + Module.finrank Int f.ker = Module.finrank Int M := by
  have hquotRange :
      @Module.finrank Int (M ⧸ f.ker) _ _ (Submodule.Quotient.module f.ker) =
        @Module.finrank Int f.range _ _ f.range.module := by
    exact @LinearEquiv.finrank_eq Int (M ⧸ f.ker) f.range _ _
      (Submodule.Quotient.module f.ker) _ f.range.module f.quotKerEquivRange
  have hExplicit :
      @Module.finrank Int f.range _ _ f.range.module +
          @Module.finrank Int f.ker _ _ f.ker.module = Module.finrank Int M := by
    rw [← hquotRange]
    exact Submodule.finrank_quotient_add_finrank _
  calc
    Module.finrank Int f.range + Module.finrank Int f.ker =
        @Module.finrank Int f.range _ _ f.range.module +
          @Module.finrank Int f.ker _ _ f.ker.module := by
      rw [int_finrank_eq_of_module_structures
        (AddCommGroup.toIntModule f.range) f.range.module,
        int_finrank_eq_of_module_structures
          (AddCommGroup.toIntModule f.ker) f.ker.module]
    _ = Module.finrank Int M := hExplicit

/-- The alternating integral finranks in a finite exact sequence sum to zero. -/
public theorem integral_sum_neg_one_pow_finrank_eq_zero_of_exact {n : Nat}
    (V : Fin (n + 2) → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module Int (V i)] [∀ i, Module.Finite Int (V i)]
    (f : (i : Fin (n + 1)) → V i.castSucc →ₗ[Int] V i.succ)
    (inj : Function.Injective (f 0))
    (h_exact : ∀ i : Fin n, Function.Exact (f i.castSucc) (f i.succ))
    (surj : Function.Surjective (f (Fin.last _))) :
    ∑ i, (-1) ^ i.val * (Module.finrank Int (V i) : Int) = 0 := by
  let d : Fin (n + 2) → Int := fun i ↦ (Module.finrank Int (V i) : Int)
  let r : Fin (n + 1) → Int := fun i ↦
    (Module.finrank Int (f i).range : Int)
  change ∑ i, (-1) ^ i.val * d i = 0
  simp_rw [← smul_eq_mul]
  refine Fin.sum_neg_one_pow_eq_zero d r ?_ (fun i ↦ ?_) ?_
  · dsimp only [d, r]
    have hModule := int_finrank_eq_of_module_structures
      (AddCommGroup.toIntModule (f 0).range) (f 0).range.module
    exact_mod_cast (hModule.trans (LinearMap.finrank_range_of_inj inj)).symm
  · have hrn := integral_finrank_range_add_finrank_ker (f i.succ)
    have hker : Module.finrank Int (f i.succ).ker =
        Module.finrank Int (f i.castSucc).range :=
      congrArg (fun S : Submodule Int (V i.succ.castSucc) ↦ Module.finrank Int S)
        (h_exact i).linearMap_ker_eq
    dsimp only [d, r]
    omega
  · have hrange := LinearMap.range_eq_top.mpr surj
    have hExplicit :
        @Module.finrank Int (f (Fin.last n)).range _ _ (f (Fin.last n)).range.module =
          Module.finrank Int (V (Fin.last (n + 1))) := by
      have h := congrArg
        (fun S : Submodule Int (V (Fin.last n).succ) ↦
          @Module.finrank Int S _ _ S.module) hrange
      simpa only [finrank_top, Fin.succ_last] using h
    have hfinrank : Module.finrank Int (f (Fin.last n)).range =
        Module.finrank Int (V (Fin.last (n + 1))) :=
      (int_finrank_eq_of_module_structures
        (AddCommGroup.toIntModule (f (Fin.last n)).range)
        (f (Fin.last n)).range.module).trans hExplicit
    dsimp only [d, r]
    exact_mod_cast hfinrank.symm

end SphereSixComplex
