module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

namespace LinearMap
variable {R : Type*} [Ring R] {A B C : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C]

/-- A projective quotient splits an exact sequence, preserving its inclusion and projection. -/
theorem exists_equiv_prod_of_exact
    (j : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hj : Function.Injective j) (hex : Function.Exact j g)
    (hg : Function.Surjective g) [Module.Projective R C] :
    ∃ e : B ≃ₗ[R] (A × C),
      (∀ a, e (j a) = (a, 0)) ∧ ∀ b, (e b).2 = g b := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g LinearMap.id hg
  have hgs (c : C) : g (s c) = c := DFunLike.congr_fun hs c
  let f := j.coprod s
  have hgf (p : A × C) : g (f p) = p.2 := by
    change g (j p.1 + s p.2) = p.2
    rw [map_add, hex.apply_apply_eq_zero, hgs, zero_add]
  have hfi : Function.Injective f := by
    intro p q hpq
    have h₂ : p.2 = q.2 := (hgf p).symm.trans ((congrArg g hpq).trans (hgf q))
    apply Prod.ext
    · apply hj
      change j p.1 + s p.2 = j q.1 + s q.2 at hpq
      rw [h₂] at hpq
      exact add_right_cancel hpq
    · exact h₂
  have hfs : Function.Surjective f := by
    intro b
    have hz : g (b - s (g b)) = 0 := by rw [map_sub, hgs, sub_self]
    obtain ⟨a, ha⟩ := (hex _).mp hz
    refine ⟨(a, g b), ?_⟩
    change j a + s (g b) = b
    rw [ha, sub_add_cancel]
  let e := (LinearEquiv.ofBijective f ⟨hfi, hfs⟩).symm
  refine ⟨e, ?_, ?_⟩
  · intro a
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change j a = j a + s 0
    rw [map_zero, add_zero]
  · intro b
    have h := hgf (e b)
    change g (e.symm (e b)) = (e b).2 at h
    rw [e.symm_apply_apply] at h
    exact h.symm
end LinearMap

namespace LinearMap
variable {R : Type*} [Ring R]
  {A B C D E : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
  [Module R A] [Module R B] [Module R C] [Module R D] [Module R E]

/-- A splitting of a four-map exact sequence with the canonical quotient and kernel coordinates. -/
theorem exists_equiv_coker_prod_ker
    (a : A →ₗ[R] B) (b : B →ₗ[R] C) (c : C →ₗ[R] D) (d : D →ₗ[R] E)
    (hab : Function.Exact a b) (hbc : Function.Exact b c) (hcd : Function.Exact c d)
    [Module.Projective R (LinearMap.ker d)] :
    ∃ e : C ≃ₗ[R] ((B ⧸ LinearMap.range a) × LinearMap.ker d),
      (∀ y, e (b y) = (Submodule.Quotient.mk y, 0)) ∧
      ∀ x, ((e x).2 : D) = c x := by
  let j : (B ⧸ LinearMap.range a) →ₗ[R] C :=
    (LinearMap.range a).liftQ b (by
      rintro _ ⟨x, rfl⟩
      exact hab.apply_apply_eq_zero x)
  let g : C →ₗ[R] LinearMap.ker d :=
    c.codRestrict (LinearMap.ker d) (fun x ↦ hcd.apply_apply_eq_zero x)
  have hj : Function.Injective j :=
    LinearMap.injective_range_liftQ_of_exact hab
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := (hcd y).mp hy
    exact ⟨x, Subtype.ext hx⟩
  have hex : Function.Exact j g := by
    intro x
    constructor
    · intro hx
      have hx' : c x = 0 := congrArg Subtype.val hx
      obtain ⟨y, hy⟩ := (hbc x).mp hx'
      exact ⟨Submodule.Quotient.mk y, hy⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact Subtype.ext (hbc.apply_apply_eq_zero z)
  obtain ⟨e, he₁, he₂⟩ := exists_equiv_prod_of_exact j g hj hex hg
  refine ⟨e, ?_, ?_⟩
  · intro y
    exact he₁ (Submodule.Quotient.mk y)
  · intro x
    exact congrArg Subtype.val (he₂ x)
end LinearMap

namespace LinearMap
variable {R : Type*} [Ring R] {F G C H I : Type*}
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup C] [AddCommGroup H] [AddCommGroup I]
  [Module R F] [Module R G] [Module R C] [Module R H] [Module R I]

/-- An exact sequence with coordinate inclusion and projection has the remaining two factors
as its middle term. This applies to the torus-attachment Mayer–Vietoris maps. -/
theorem exists_equiv_of_exact_inl_snd
    (b : (F × G) →ₗ[R] C) (c : C →ₗ[R] (H × I))
    (hab : Function.Exact (LinearMap.inl R F G) b)
    (hbc : Function.Exact b c)
    (hcd : Function.Exact c (LinearMap.snd R H I))
    [Module.Projective R H] :
    ∃ e : C ≃ₗ[R] (G × H),
      (∀ y, e (b (0, y)) = (y, 0)) ∧ ∀ x, (e x).2 = (c x).1 := by
  let j := b.comp (LinearMap.inr R F G)
  let g := (LinearMap.fst R H I).comp c
  have hj : Function.Injective j := by
    intro x y hxy
    apply sub_eq_zero.mp
    have hz : b (0, x - y) = 0 := by
      change j (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨f, hf⟩ := (hab (0, x - y)).mp hz
    exact (congrArg Prod.snd hf).symm
  have hg : Function.Surjective g := by
    intro h
    obtain ⟨x, hx⟩ := (hcd (h, 0)).mp rfl
    exact ⟨x, congrArg Prod.fst hx⟩
  have hex : Function.Exact j g := by
    intro x
    constructor
    · intro hx
      have hc : c x = 0 := Prod.ext hx (hcd.apply_apply_eq_zero x)
      obtain ⟨⟨f, y⟩, hy⟩ := (hbc x).mp hc
      refine ⟨y, ?_⟩
      change b (0, y) = x
      have hb : b (f, 0) = 0 := hab.apply_apply_eq_zero f
      have hadd := b.map_add (f, 0) (0, y)
      simp only [Prod.mk_add_mk, add_zero, zero_add] at hadd
      rw [hb, zero_add] at hadd
      exact hadd.symm.trans hy
    · rintro ⟨y, rfl⟩
      exact congrArg Prod.fst (hbc.apply_apply_eq_zero (0, y))
  obtain ⟨e, he₁, he₂⟩ := exists_equiv_prod_of_exact j g hj hex hg
  exact ⟨e, he₁, he₂⟩
end LinearMap

end
