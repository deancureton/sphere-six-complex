module

public import SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Abelianization of a cyclic extension of an abelian group

Let `G` be an extension `1 → Λ → G → ZMod m → 1` of a cyclic group by an abelian group, let
`gen ∈ G` lift the standard generator, let `act` be conjugation by `gen` acting on `Λ`, and let
`twist ∈ Λ` be `gen ^ m`.  Then

```
G^ab ≅ ((Λ ⧸ (act - 1) Λ) × ℤ) ⧸ ⟨(-[twist], m)⟩,
```

the right-hand side being `MultipleFiberHOnePresentation (act - 1) twist m`.

Two facts drive the proof.  Conjugation by `gen` is the identity on `Λ` modulo `(act - 1) Λ`, and
`Λ` is abelian, so every commutator of `G` lands in `(act - 1) Λ` — this is
`commutator_le_differenceSubgroup`.  Conversely `gen ^ k` lies in `Λ` only when `m ∣ k`, which is
what makes the meridian coordinate exactly `ℤ ⧸ m` relative to the twist.

This is the group theory behind the `H₁` computation of a multiple fibre: `Λ` is the first homology
of the fibre, `ZMod m` the cyclic deck group of the covering, `act` the monodromy and `twist` the
twist.  Nothing in this file refers to that setting.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Topology.CyclicExtension

open SphereSixComplex.Topology.PaperLemmaSevenThirteenAlgebra

variable {m : ℕ} {Λ G : Type*} [AddCommGroup Λ] [Group G]

/-- `G` presented as an extension of `ZMod m` by the abelian group `Λ`, with a chosen lift of the
standard generator of `ZMod m`. -/
public structure Data (m : ℕ) (Λ G : Type*) [AddCommGroup Λ] [Group G] where
  /-- The inclusion of the abelian kernel. -/
  incl : Λ → G
  /-- The inclusion is a homomorphism. -/
  incl_add : ∀ a b, incl (a + b) = incl a * incl b
  /-- The kernel injects. -/
  incl_injective : Function.Injective incl
  /-- The projection onto the cyclic quotient. -/
  proj : G →* Multiplicative (ZMod m)
  /-- Exactness at `G`: the kernel of `proj` is the image of `incl`. -/
  proj_eq_one_iff : ∀ x, proj x = 1 ↔ ∃ l, incl l = x
  /-- A lift of the standard generator. -/
  gen : G
  /-- The lift projects to the standard generator. -/
  proj_gen : proj gen = Multiplicative.ofAdd 1
  /-- Conjugation by the lift, as an automorphism of the kernel. -/
  act : Λ ≃ₗ[ℤ] Λ
  /-- Conjugation by the lift is `act`. -/
  conj_incl : ∀ l, gen * incl l * gen⁻¹ = incl (act l)
  /-- The `m`-th power of the lift, as an element of the kernel. -/
  twist : Λ
  /-- The lift has `m`-th power `twist`. -/
  gen_pow : gen ^ m = incl twist

namespace Data

variable (E : Data m Λ G)

/-- The endomorphism `act - 1` of the kernel, whose image is the commutator subgroup of `G`. -/
public def difference : Λ →ₗ[ℤ] Λ := (E.act : Λ →ₗ[ℤ] Λ) - LinearMap.id

public theorem difference_apply (l : Λ) : E.difference l = E.act l - l := rfl

public theorem incl_zero : E.incl 0 = 1 := by
  have h : E.incl 0 * E.incl 0 = E.incl 0 * 1 := by
    rw [mul_one, ← E.incl_add, add_zero]
  exact mul_left_cancel h

public theorem incl_neg (l : Λ) : E.incl (-l) = (E.incl l)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← E.incl_add, neg_add_cancel, E.incl_zero]

public theorem incl_sub (a b : Λ) : E.incl (a - b) = E.incl a * (E.incl b)⁻¹ := by
  rw [sub_eq_add_neg, E.incl_add, E.incl_neg]

/-- Conjugating the kernel by `gen⁻¹` acts by `act.symm`. -/
public theorem conj_incl_symm (l : Λ) : E.gen⁻¹ * E.incl l * E.gen = E.incl (E.act.symm l) := by
  have h := E.conj_incl (E.act.symm l)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [← h]
  group

/-- Moving the kernel past an integer power of the lift changes it only inside the image of
`act - 1`. -/
public theorem exists_incl_mul_zpow (k : ℤ) (l : Λ) :
    ∃ w : Λ, E.gen ^ k * E.incl l = E.incl w * E.gen ^ k ∧
      w - l ∈ LinearMap.range E.difference := by
  have key : ∀ k : ℤ, ∃ w : Λ, E.gen ^ k * E.incl l * (E.gen ^ k)⁻¹ = E.incl w ∧
      w - l ∈ LinearMap.range E.difference := by
    intro k
    induction k using Int.induction_on with
    | zero => exact ⟨l, by simp, by simp⟩
    | succ n ih =>
        obtain ⟨w, hw, hmem⟩ := ih
        refine ⟨E.act w, ?_, ?_⟩
        · have hstep : E.gen ^ ((n : ℤ) + 1) * E.incl l * (E.gen ^ ((n : ℤ) + 1))⁻¹ =
              E.gen * (E.gen ^ (n : ℤ) * E.incl l * (E.gen ^ (n : ℤ))⁻¹) * E.gen⁻¹ := by
            rw [zpow_add_one]
            group
          rw [hstep, hw, E.conj_incl]
        · have hrw : E.act w - l = E.difference w + (w - l) := by
            rw [E.difference_apply]; abel
          rw [hrw]
          exact add_mem ⟨w, rfl⟩ hmem
    | pred n ih =>
        obtain ⟨w, hw, hmem⟩ := ih
        refine ⟨E.act.symm w, ?_, ?_⟩
        · have hstep : E.gen ^ (-(n : ℤ) - 1) * E.incl l * (E.gen ^ (-(n : ℤ) - 1))⁻¹ =
              E.gen⁻¹ * (E.gen ^ (-(n : ℤ)) * E.incl l * (E.gen ^ (-(n : ℤ)))⁻¹) * E.gen := by
            rw [zpow_sub_one]
            group
          rw [hstep, hw, E.conj_incl_symm]
        · have hrw : E.act.symm w - l = -E.difference (E.act.symm w) + (w - l) := by
            rw [E.difference_apply, LinearEquiv.apply_symm_apply]; abel
          rw [hrw]
          exact add_mem (neg_mem ⟨E.act.symm w, rfl⟩) hmem
  obtain ⟨w, hw, hmem⟩ := key k
  refine ⟨w, ?_, hmem⟩
  rw [← hw]
  group

/-- Every element of `G` is an integer power of the lift times an element of the kernel. -/
public theorem exists_zpow_mul_incl (x : G) : ∃ (k : ℤ) (l : Λ), x = E.gen ^ k * E.incl l := by
  obtain ⟨k, hk⟩ := ZMod.intCast_surjective (n := m) (Multiplicative.toAdd (E.proj x))
  have hproj : E.proj (E.gen ^ k) = E.proj x := by
    rw [map_zpow, E.proj_gen, ← ofAdd_zsmul, zsmul_eq_mul, mul_one, hk,
      ofAdd_toAdd]
  have hmem : E.proj ((E.gen ^ k)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hproj, inv_mul_cancel]
  obtain ⟨l, hl⟩ := (E.proj_eq_one_iff _).mp hmem
  refine ⟨k, l, ?_⟩
  rw [hl]
  group

/-- The image in `G` of `(act - 1) Λ`. -/
public def differenceSubgroup : Subgroup G where
  carrier := {x | ∃ w : Λ, E.incl (E.difference w) = x}
  one_mem' := ⟨0, by rw [map_zero, E.incl_zero]⟩
  mul_mem' := by
    rintro a b ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, by rw [map_add, E.incl_add]⟩
  inv_mem' := by
    rintro a ⟨p, rfl⟩
    exact ⟨-p, by rw [map_neg, E.incl_neg]⟩

public theorem mem_differenceSubgroup {x : G} :
    x ∈ E.differenceSubgroup ↔ ∃ w : Λ, E.incl (E.difference w) = x := Iff.rfl

/-- The commutator subgroup of `G` lands in `(act - 1) Λ`: modulo that image the lift commutes with
the kernel, and the kernel is abelian. -/
public theorem commutator_le_differenceSubgroup : commutator G ≤ E.differenceSubgroup := by
  rw [commutator, Subgroup.commutator_le]
  intro a _ b _
  obtain ⟨i, l, rfl⟩ := E.exists_zpow_mul_incl a
  obtain ⟨j, μ, rfl⟩ := E.exists_zpow_mul_incl b
  obtain ⟨w₁, h₁, -⟩ := E.exists_incl_mul_zpow i l
  obtain ⟨w₂, h₂, -⟩ := E.exists_incl_mul_zpow j μ
  obtain ⟨w₃, h₃, m₃⟩ := E.exists_incl_mul_zpow i w₂
  obtain ⟨w₄, h₄, m₄⟩ := E.exists_incl_mul_zpow j w₁
  have hab : (E.gen ^ i * E.incl l) * (E.gen ^ j * E.incl μ) =
      E.incl (w₁ + w₃) * E.gen ^ (i + j) := by
    rw [h₁, h₂, E.incl_add]
    calc E.incl w₁ * E.gen ^ i * (E.incl w₂ * E.gen ^ j)
        = E.incl w₁ * (E.gen ^ i * E.incl w₂) * E.gen ^ j := by group
      _ = E.incl w₁ * (E.incl w₃ * E.gen ^ i) * E.gen ^ j := by rw [h₃]
      _ = E.incl w₁ * E.incl w₃ * E.gen ^ (i + j) := by rw [zpow_add]; group
  have hba : (E.gen ^ j * E.incl μ) * (E.gen ^ i * E.incl l) =
      E.incl (w₂ + w₄) * E.gen ^ (i + j) := by
    rw [h₁, h₂, E.incl_add]
    calc E.incl w₂ * E.gen ^ j * (E.incl w₁ * E.gen ^ i)
        = E.incl w₂ * (E.gen ^ j * E.incl w₁) * E.gen ^ i := by group
      _ = E.incl w₂ * (E.incl w₄ * E.gen ^ j) * E.gen ^ i := by rw [h₄]
      _ = E.incl w₂ * E.incl w₄ * E.gen ^ (i + j) := by
            rw [add_comm i j, zpow_add]; group
  obtain ⟨p, hp⟩ := m₃
  obtain ⟨q, hq⟩ := m₄
  refine ⟨p - q, ?_⟩
  rw [map_sub, hp, hq, show (w₃ - w₂) - (w₄ - w₁) = (w₁ + w₃) - (w₂ + w₄) by abel,
    E.incl_sub, commutatorElement_def]
  calc E.incl (w₁ + w₃) * (E.incl (w₂ + w₄))⁻¹
      = E.incl (w₁ + w₃) * E.gen ^ (i + j) *
          ((E.incl (w₂ + w₄) * E.gen ^ (i + j))⁻¹) := by group
    _ = _ := by rw [← hab, ← hba]; group

/-- The kernel inclusion as a monoid homomorphism. -/
public def inclHom : Multiplicative Λ →* G where
  toFun l := E.incl (Multiplicative.toAdd l)
  map_one' := E.incl_zero
  map_mul' _ _ := E.incl_add _ _

public theorem incl_zsmul (j : ℤ) (l : Λ) : E.incl (j • l) = E.incl l ^ j := by
  simpa [inclHom, ofAdd_zsmul] using map_zpow E.inclHom (Multiplicative.ofAdd l) j

/-- The kernel's contribution to the abelianization of `G`. -/
public def kernelToAbelianization : Λ →ₗ[ℤ] Additive (Abelianization G) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun l => Additive.ofMul (Abelianization.of (E.incl l))
      map_zero' := by simp [E.incl_zero]
      map_add' := fun a b => by simp [E.incl_add] }

@[simp] public theorem kernelToAbelianization_apply (l : Λ) :
    E.kernelToAbelianization l = Additive.ofMul (Abelianization.of (E.incl l)) := rfl

/-- Conjugation is trivial on the abelianization, so `act - 1` dies there. -/
public theorem kernelToAbelianization_difference (x : Λ) :
    E.kernelToAbelianization (E.difference x) = 0 := by
  have hact : Abelianization.of (E.incl (E.act x)) = Abelianization.of (E.incl x) := by
    rw [← E.conj_incl x, map_mul, map_mul, map_inv,
      mul_comm (Abelianization.of E.gen) (Abelianization.of (E.incl x)), mul_assoc,
      mul_inv_cancel, mul_one]
  rw [kernelToAbelianization_apply, E.difference_apply, E.incl_sub, map_mul, map_inv, hact]
  simp

/-- The comparison map from the multiple-fibre presentation to the abelianization of `G`. -/
public def toAbelianization :
    MultipleFiberHOnePresentation E.difference E.twist (m : ℤ) →ₗ[ℤ]
      Additive (Abelianization G) :=
  multipleFiberLift E.difference E.twist (m : ℤ) E.kernelToAbelianization
    E.kernelToAbelianization_difference (Additive.ofMul (Abelianization.of E.gen)) (by
      rw [kernelToAbelianization_apply, ← ofMul_zpow, ← map_zpow, zpow_natCast, E.gen_pow])

@[simp] public theorem toAbelianization_mk (l : Λ) (k : ℤ) :
    E.toAbelianization (Submodule.Quotient.mk (Submodule.Quotient.mk l, k)) =
      Additive.ofMul (Abelianization.of (E.incl l) * Abelianization.of E.gen ^ k) := by
  rw [toAbelianization, multipleFiberLift_mk, kernelToAbelianization_apply, ← ofMul_zpow,
    ← ofMul_mul]

public theorem toAbelianization_surjective : Function.Surjective E.toAbelianization := by
  intro y
  obtain ⟨x, hx⟩ := Quot.exists_rep (Additive.toMul y)
  obtain ⟨k, l, rfl⟩ := E.exists_zpow_mul_incl x
  refine ⟨Submodule.Quotient.mk (Submodule.Quotient.mk l, k), ?_⟩
  rw [toAbelianization_mk]
  have hval : Abelianization.of (E.gen ^ k * E.incl l) = Additive.toMul y := hx
  rw [map_mul, map_zpow, mul_comm] at hval
  rw [hval]
  rfl

public theorem toAbelianization_injective : Function.Injective E.toAbelianization := by
  have key : ∀ y, E.toAbelianization y = 0 → y = 0 := by
    intro y hy
    obtain ⟨⟨lq, k⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ lq
    rw [toAbelianization_mk] at hy
    have h1 : Abelianization.of (E.incl l * E.gen ^ k) = 1 := by
      rw [map_mul, map_zpow]
      exact hy
    have h2 : E.incl l * E.gen ^ k ∈ commutator G := by
      rw [← Abelianization.ker_of, MonoidHom.mem_ker]
      exact h1
    obtain ⟨μ, hμ⟩ := E.commutator_le_differenceSubgroup h2
    have hprojl : E.proj (E.incl l) = 1 := (E.proj_eq_one_iff _).mpr ⟨l, rfl⟩
    have hprojd : E.proj (E.incl (E.difference μ)) = 1 :=
      (E.proj_eq_one_iff _).mpr ⟨E.difference μ, rfl⟩
    have hgk : E.proj (E.gen ^ k) = 1 := by
      have hcong := congrArg E.proj hμ
      rw [hprojd, map_mul, hprojl, one_mul] at hcong
      exact hcong.symm
    have hzero : ((k : ℤ) : ZMod m) = 0 := by
      rw [map_zpow, E.proj_gen, ← ofAdd_zsmul, zsmul_eq_mul, mul_one] at hgk
      exact hgk
    obtain ⟨j, rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd k m).mp hzero
    have hgpow : E.gen ^ ((m : ℤ) * j) = E.incl (j • E.twist) := by
      rw [zpow_mul, zpow_natCast, E.gen_pow, E.incl_zsmul]
    have heq : E.difference μ = l + j • E.twist := by
      apply E.incl_injective
      rw [E.incl_add, ← hgpow, hμ]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨j, ?_⟩
    have hmk : (Submodule.Quotient.mk l : Λ ⧸ LinearMap.range E.difference) =
        -(j • Submodule.Quotient.mk E.twist) := by
      have : (Submodule.Quotient.mk (E.difference μ) :
          Λ ⧸ LinearMap.range E.difference) = 0 :=
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨μ, rfl⟩
      rw [heq] at this
      rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul] at this
      linear_combination (norm := abel) this
    rw [multipleFiberRelationMap]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_mk, smul_neg, Prod.mk.injEq]
    exact ⟨by rw [hmk], by rw [smul_eq_mul, mul_comm]⟩
  intro a b hab
  have hsub : E.toAbelianization (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (key _ hsub)

/-- **The abelianization of a cyclic extension.**  If `1 → Λ → G → ZMod m → 1` with `Λ` abelian,
`gen` lifting the standard generator, `act` conjugation by `gen` and `twist = gen ^ m`, then the
abelianization of `G` is the multiple-fibre presentation of `act - 1` at `twist` and `m`. -/
public noncomputable def abelianizationEquiv :
    MultipleFiberHOnePresentation E.difference E.twist (m : ℤ) ≃ₗ[ℤ]
      Additive (Abelianization G) :=
  LinearEquiv.ofBijective E.toAbelianization
    ⟨E.toAbelianization_injective, E.toAbelianization_surjective⟩

@[simp] public theorem abelianizationEquiv_mk (l : Λ) (k : ℤ) :
    E.abelianizationEquiv (Submodule.Quotient.mk (Submodule.Quotient.mk l, k)) =
      Additive.ofMul (Abelianization.of (E.incl l) * Abelianization.of E.gen ^ k) :=
  E.toAbelianization_mk l k

end Data

end SphereSixComplex.Topology.CyclicExtension

end

end
