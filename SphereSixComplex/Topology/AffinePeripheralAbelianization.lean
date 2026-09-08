module
import all SphereSixComplex.LatticeData
public import SphereSixComplex.Topology.PaperVanKampenAlgebraAdapter

@[expose] public section
noncomputable section
namespace SphereSixComplex.Topology
open LatticeData

public theorem affineCore_translation_eq_of_gamma_eq
    {G H : Type*} [Group G] [AddCommGroup H]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (f : G →* Multiplicative H) {a b : Lattice} (hab : gamma a = gamma b) :
    f (Additive.toMul (C.translation a)) = f (Additive.toMul (C.translation b)) := by
  let t : Lattice →+ H := f.toAdditiveLeft.comp C.translation
  have hi₁ (v : Lattice) : t (A₁.mulVec v) = t v := by
    have h := congrArg f (C.conjugate_one v)
    simpa [t, map_mul, map_inv, mul_assoc, mul_comm, mul_left_comm,
      paperMonodromyOne] using h.symm
  have hi₂ (v : Lattice) : t (A₂.mulVec v) = t v := by
    have h := congrArg f (C.conjugate_two v)
    simpa [t, map_mul, map_inv, mul_assoc, mul_comm, mul_left_comm,
      paperMonodromyTwo] using h.symm
  have hk : dualCoinvariantRelations ≤ t.toIntLinearMap.ker := by
    rw [dualCoinvariantRelations]
    apply Submodule.span_le.mpr
    simp only [dualMonodromyDifferences]
    rintro x (⟨v, rfl⟩ | ⟨v, rfl⟩)
    · change t (A₁.mulVec v - v) = 0
      rw [map_sub, hi₁, sub_self]
    · change t (A₂.mulVec v - v) = 0
      rw [map_sub, hi₂, sub_self]
  have hzero : t (a - b) = 0 := hk (by
    rw [dualCoinvariantRelations_eq_ker_gamma]
    change gamma (a - b) = 0
    rw [map_sub, hab, sub_self])
  have ht : t a = t b := sub_eq_zero.mp ((map_sub t a b).symm.trans hzero)
  exact congrArg (fun h : H ↦ Multiplicative.ofAdd h) ht

public theorem affineCore_peripheral_twelfth_abelian
    {G H : Type*} [Group G] [AddCommGroup H]
    (C : AffineTorusCorePiOneData G Lattice paperMonodromyOne paperMonodromyTwo)
    (f : G →* Multiplicative H)
    (h₁ : f C.rhoOne ^ 3 = f (Additive.toMul (C.translation (-epsilon))))
    (h₂ : f C.rhoTwo ^ 4 = f (Additive.toMul (C.translation epsilon'))) :
    f ((C.rhoOne * C.rhoTwo)⁻¹) ^ 12 =
      f (Additive.toMul (C.translation (Pi.single (0 : Fin 4) 1))) := by
  have ht := affineCore_translation_eq_of_gamma_eq C f
    (a := (4 : ℤ) • (-epsilon) + (3 : ℤ) • epsilon')
    (b := -(Pi.single (0 : Fin 4) 1)) (by norm_num [gamma, epsilon, epsilon'])
  have hp : f (C.rhoOne * C.rhoTwo) ^ 12 =
      f (Additive.toMul (C.translation (-(Pi.single (0 : Fin 4) 1)))) := by
    rw [map_mul, mul_pow]
    rw [show (12 : ℕ) = 3 * 4 by decide, pow_mul, h₁]
    rw [show (3 * 4 : ℕ) = 4 * 3 by decide, pow_mul, h₂]
    rw [← ht]
    rw [map_add, C.translation.map_zsmul, C.translation.map_zsmul]
    simp only [toMul_add, toMul_zsmul, map_mul, map_zpow]
    norm_num
  rw [map_inv, inv_pow, hp]
  simp

end SphereSixComplex.Topology
end
