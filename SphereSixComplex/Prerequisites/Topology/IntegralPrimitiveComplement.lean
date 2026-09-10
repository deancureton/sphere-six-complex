module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

@[expose] public section
namespace SphereSixComplex

public theorem integerProjection_first_isUnit
    {G : Type*} [AddCommGroup G] (p : ℤ × G →+ ℤ)
    (hp : ∀ g, p (0, g) = 0) (x : ℤ × G) (hx : p x = 1) :
    IsUnit x.1 := by
  have he : x = x.1 • (1, (0 : G)) + (0, x.2) := by
    ext <;> simp
  have hm : x.1 * p (1, 0) = 1 := by
    rw [he, map_add, map_zsmul, hp, add_zero] at hx
    simpa using hx
  exact IsUnit.of_mul_eq_one _ hm

public noncomputable def integerPrimitiveComplementEquiv
    {G : Type*} [AddCommGroup G] (x : ℤ × G) (h : IsUnit x.1) :
    ℤ × G ≃+ ℤ × G := by
  let u := h.unit
  have hu : (u : ℤ) = x.1 := h.unit_spec
  exact
    { toFun := fun y ↦ (y.1 * x.1, y.1 • x.2 + y.2)
      invFun := fun y ↦ (y.1 * ↑(u⁻¹), y.2 - (y.1 * ↑(u⁻¹)) • x.2)
      left_inv := by
        intro y
        have ht : y.1 * x.1 * ↑(u⁻¹) = y.1 := by rw [← hu, mul_assoc]; simp
        ext <;> simp [ht]
      right_inv := by
        intro y
        have ht : y.1 * ↑(u⁻¹) * x.1 = y.1 := by rw [← hu, mul_assoc]; simp
        ext <;> simp [ht]
      map_add' := by
        intro a b
        ext <;> simp [add_mul, add_zsmul]
        abel }

public theorem integerPrimitiveComplementEquiv_first
    {G : Type*} [AddCommGroup G] (x : ℤ × G) (h : IsUnit x.1) :
    integerPrimitiveComplementEquiv x h (1, 0) = x := by
  ext <;> simp [integerPrimitiveComplementEquiv]

public theorem integerPrimitiveComplementEquiv_tail
    {G : Type*} [AddCommGroup G] (x : ℤ × G) (h : IsUnit x.1) (g : G) :
    integerPrimitiveComplementEquiv x h (0, g) = (0, g) := by
  ext <;> simp [integerPrimitiveComplementEquiv]

public noncomputable def integerProjectionComplementEquiv
    {G : Type*} [AddCommGroup G] (p : ℤ × G →+ ℤ)
    (hp : ∀ g, p (0, g) = 0) (x : ℤ × G) (hx : p x = 1) :
    ℤ × G ≃+ ℤ × G :=
  integerPrimitiveComplementEquiv x (integerProjection_first_isUnit p hp x hx)

public theorem integerProjection_tail_zero_of_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℤ × (ι → ℤ) →+ ℤ)
    (hp : ∀ i, p (0, Pi.single i 1) = 0) (g : ι → ℤ) :
    p (0, g) = 0 := by
  let q := p.comp (AddMonoidHom.inr ℤ (ι → ℤ))
  change q g = 0
  rw [pi_eq_sum_univ' g, map_sum]
  simp only [map_zsmul]
  have hq (i : ι) : q (Pi.single i 1) = 0 := hp i
  simp only [hq, smul_zero, Finset.sum_const_zero]

public def integerHeadTailEquiv (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun x := (x 0, fun i ↦ x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := Fin.cons_self_tail x
  right_inv _ := rfl
  map_add' _ _ := rfl

public theorem integerHeadTailEquiv_first (n : ℕ) :
    integerHeadTailEquiv n (Pi.single 0 1) = (1, 0) := by
  change ((Pi.single 0 (1 : ℤ) : Fin (n + 1) → ℤ) 0,
    fun i : Fin n ↦ (Pi.single 0 (1 : ℤ) : Fin (n + 1) → ℤ) i.succ) = _
  ext i <;> simp

public theorem integerHeadTailEquiv_tail (n : ℕ) (j : Fin n) :
    integerHeadTailEquiv n (Pi.single j.succ 1) = (0, Pi.single j 1) := by
  change ((Pi.single j.succ (1 : ℤ) : Fin (n + 1) → ℤ) 0,
    fun i : Fin n ↦ (Pi.single j.succ (1 : ℤ) : Fin (n + 1) → ℤ) i.succ) = _
  ext i <;> simp [Pi.single_apply]

public theorem exists_equiv_of_integer_primitive_complement
    {H : Type*} [AddCommGroup H] (n : ℕ) [Fintype (Fin n)]
    (e : (Fin (n + 1) → ℤ) ≃+ H) (x : H) (p : H →+ ℤ)
    (hp : ∀ j : Fin n, p (e (Pi.single j.succ 1)) = 0) (hx : p x = 1) :
    ∃ f : (Fin (n + 1) → ℤ) ≃+ H,
      f (Pi.single 0 1) = x ∧
      ∀ j : Fin n, f (Pi.single j.succ 1) = e (Pi.single j.succ 1) := by
  let t := integerHeadTailEquiv n
  let q := p.comp (e.toAddMonoidHom.comp t.symm.toAddMonoidHom)
  have hq (j : Fin n) : q (0, Pi.single j 1) = 0 := by
    change p (e (t.symm (0, Pi.single j 1))) = 0
    rw [← integerHeadTailEquiv_tail n j]
    simpa only [t, AddEquiv.symm_apply_apply] using hp j
  have hy : q (t (e.symm x)) = 1 := by
    change p (e (t.symm (t (e.symm x)))) = 1
    simpa only [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply] using hx
  let c := integerProjectionComplementEquiv q
    (integerProjection_tail_zero_of_single q hq) (t (e.symm x)) hy
  refine ⟨t.trans (c.trans (t.symm.trans e)), ?_, ?_⟩
  · change e (t.symm (c (t (Pi.single 0 1)))) = x
    rw [integerHeadTailEquiv_first]
    change e (t.symm (integerPrimitiveComplementEquiv _ _ (1, 0))) = x
    rw [integerPrimitiveComplementEquiv_first]
    simp only [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]
  · intro j
    change e (t.symm (c (t (Pi.single j.succ 1)))) = _
    rw [integerHeadTailEquiv_tail]
    change e (t.symm (integerPrimitiveComplementEquiv _ _ (0, Pi.single j 1))) = _
    rw [integerPrimitiveComplementEquiv_tail, ← integerHeadTailEquiv_tail n j]
    simp only [t, AddEquiv.symm_apply_apply]

public theorem additive_bijective_of_basis_readout
    {ι G H : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ (ι → ℤ)) (r : H ≃+ (ι → ℤ)) (f : G →+ H)
    (h : ∀ i, r (f (e.symm (Pi.single i 1))) = Pi.single i 1) :
    Function.Bijective f := by
  have he (x : G) : r (f x) = e x := by
    have hx : x = e.symm (e x) := (e.symm_apply_apply x).symm
    rw [hx, pi_eq_sum_univ' (e x), map_sum, map_sum, map_sum]
    simp only [map_zsmul, h]
    simp only [map_sum, map_zsmul, AddEquiv.apply_symm_apply]
  have hf : (f : G → H) = fun x ↦ r.symm (e x) := by
    funext x
    exact r.injective (by simpa only [AddEquiv.apply_symm_apply] using he x)
  rw [hf]
  exact r.symm.bijective.comp e.bijective

end SphereSixComplex
