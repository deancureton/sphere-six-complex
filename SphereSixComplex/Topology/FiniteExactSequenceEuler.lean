module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

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

/-- In an exact pair of maps between finitely generated `Int`-modules, the rank of the middle
term is the sum of the ranks of the two adjacent images. -/
public theorem integral_finrank_eq_add_finrank_range_of_exact {M N P : Type*}
    [AddCommGroup M] [Module Int M]
    [AddCommGroup N] [Module Int N] [Module.Finite Int N]
    [AddCommGroup P] [Module Int P]
    (f : M →ₗ[Int] N) (g : N →ₗ[Int] P) (h : Function.Exact f g) :
    Module.finrank Int N =
      Module.finrank Int f.range + Module.finrank Int g.range := by
  have hrank := integral_finrank_range_add_finrank_ker g
  have hker : Module.finrank Int g.ker = Module.finrank Int f.range :=
    congrArg (fun S : Submodule Int N ↦ Module.finrank Int S) h.linearMap_ker_eq
  omega

/-- A surjective map of `Int`-modules has an image of the same finrank as its codomain. -/
public theorem integral_finrank_range_eq_of_surjective {M N : Type*}
    [AddCommGroup M] [Module Int M] [AddCommGroup N] [Module Int N]
    (f : M →ₗ[Int] N) (h : Function.Surjective f) :
    Module.finrank Int f.range = Module.finrank Int N := by
  have hrange : f.range = ⊤ := LinearMap.range_eq_top.mpr h
  have hExplicit :
      @Module.finrank Int f.range _ _ f.range.module = Module.finrank Int N := by
    have h' := congrArg
      (fun S : Submodule Int N ↦ @Module.finrank Int S _ _ S.module) hrange
    simpa only [finrank_top] using h'
  exact (int_finrank_eq_of_module_structures
    (AddCommGroup.toIntModule f.range) f.range.module).trans hExplicit

/-- An injective map from a finitely generated `Int`-module has an image of the same finrank as
its domain. -/
public theorem integral_finrank_range_eq_of_injective {M N : Type*}
    [AddCommGroup M] [Module Int M] [Module.Finite Int M]
    [AddCommGroup N] [Module Int N]
    (f : M →ₗ[Int] N) (h : Function.Injective f) :
    Module.finrank Int f.range = Module.finrank Int M := by
  have hModule := int_finrank_eq_of_module_structures
    (AddCommGroup.toIntModule f.range) f.range.module
  exact hModule.trans (LinearMap.finrank_range_of_inj h)

/-- Three consecutive exactness assertions telescope the three interior ranks to the ranks of the
two endpoint images. -/
public theorem integral_finrank_alternating_step_of_exact
    {V₀ V₁ V₂ V₃ V₄ : Type*}
    [AddCommGroup V₀] [Module Int V₀]
    [AddCommGroup V₁] [Module Int V₁] [Module.Finite Int V₁]
    [AddCommGroup V₂] [Module Int V₂] [Module.Finite Int V₂]
    [AddCommGroup V₃] [Module Int V₃] [Module.Finite Int V₃]
    [AddCommGroup V₄] [Module Int V₄]
    (f₀ : V₀ →ₗ[Int] V₁) (f₁ : V₁ →ₗ[Int] V₂)
    (f₂ : V₂ →ₗ[Int] V₃) (f₃ : V₃ →ₗ[Int] V₄)
    (h₁ : Function.Exact f₀ f₁) (h₂ : Function.Exact f₁ f₂)
    (h₃ : Function.Exact f₂ f₃) :
    (Module.finrank Int V₁ : Int) - Module.finrank Int V₂ +
        Module.finrank Int V₃ =
      Module.finrank Int f₀.range + Module.finrank Int f₃.range := by
  have hRank₁ := integral_finrank_eq_add_finrank_range_of_exact f₀ f₁ h₁
  have hRank₂ := integral_finrank_eq_add_finrank_range_of_exact f₁ f₂ h₂
  have hRank₃ := integral_finrank_eq_add_finrank_range_of_exact f₂ f₃ h₃
  have hRank₁' : (Module.finrank Int V₁ : Int) =
      Module.finrank Int f₀.range + Module.finrank Int f₁.range := by
    exact_mod_cast hRank₁
  have hRank₂' : (Module.finrank Int V₂ : Int) =
      Module.finrank Int f₁.range + Module.finrank Int f₂.range := by
    exact_mod_cast hRank₂
  have hRank₃' : (Module.finrank Int V₃ : Int) =
      Module.finrank Int f₂.range + Module.finrank Int f₃.range := by
    exact_mod_cast hRank₃
  omega

/-- Finrank is additive on products of finitely generated `Int`-modules.  Unlike Mathlib's
free-module result, this applies when either module has torsion. -/
public theorem integral_finrank_prod {M N : Type*}
    [AddCommGroup M] [Module Int M] [Module.Finite Int M]
    [AddCommGroup N] [Module Int N] [Module.Finite Int N] :
    Module.finrank Int (M × N) =
      Module.finrank Int M + Module.finrank Int N := by
  let prodModule : Module Int (M × N) := Prod.instModule
  have hProduct : @Module.finrank Int (M × N) _ _ prodModule =
      Module.finrank Int M + Module.finrank Int N := by
    let _ : Module Int (M × N) := prodModule
    let f := LinearMap.inl Int M N
    let g := LinearMap.snd Int M N
    have hmiddle := integral_finrank_eq_add_finrank_range_of_exact f g
      Function.Exact.inl_snd
    have hleft : Module.finrank Int f.range = Module.finrank Int M :=
      integral_finrank_range_eq_of_injective f LinearMap.inl_injective
    have hright : Module.finrank Int g.range = Module.finrank Int N :=
      integral_finrank_range_eq_of_surjective g LinearMap.snd_surjective
    omega
  exact (int_finrank_eq_of_module_structures
    (AddCommGroup.toIntModule (M × N)) prodModule).trans hProduct

/-- Exactness with finitely generated outer terms makes the middle term finitely generated over
`Int`, without requiring the second map to be onto its original codomain. -/
public theorem integral_module_finite_of_exact {M N P : Type*}
    [AddCommGroup M] [Module Int M] [Module.Finite Int M]
    [AddCommGroup N] [Module Int N]
    [AddCommGroup P] [Module Int P] [Module.Finite Int P]
    (f : M →ₗ[Int] N) (g : N →ₗ[Int] P) (h : Function.Exact f g) :
    Module.Finite Int N := by
  let _ : IsNoetherian Int P := by infer_instance
  let _ : Module Int g.range := g.range.module
  let _ : IsNoetherian Int g.range := isNoetherian_submodule' g.range
  let _ : Module.Finite Int g.range := by infer_instance
  apply Module.Finite.of_exact (f := f) (g := g.rangeRestrict)
  · intro y
    constructor
    · intro hy
      apply (h y).mp
      exact congrArg Subtype.val hy
    · intro hy
      apply Subtype.ext
      exact (h y).mpr hy
  · exact LinearMap.surjective_rangeRestrict g

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
