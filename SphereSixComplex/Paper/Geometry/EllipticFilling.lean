module

public import SphereSixComplex.Paper.TriangleGroup.Representation
public import SphereSixComplex.Prerequisites.Geometry.FiniteCyclicAffineAction

/-!
# Elliptic logarithmic-transform fillings

The finite local quotient used at the elliptic points.  The analytic construction of the
disc, torus family, and affine fixed-point criterion is kept as explicit data.  From that data
we construct the cyclic diagonal action, prove its exact freeness criterion, and install the
charted-space structure supplied by Mathlib for free properly discontinuous quotients.
-/

open SphereSixComplex.LatticeData
open SphereSixComplex.TriangleGroup

noncomputable section

namespace SphereSixComplex.Geometry

/-- Data retained from the local analytic construction in §5.  The last field is precisely
Lemma 5.5's affine fixed-point computation, expressed using the invariant character `gamma`. -/
public structure EllipticActionData (m : ℕ) [NeZero m]
    (Base Torus : Type*) [AddCommGroup Torus] where
  rotation : Equiv.Perm Base
  center : Base
  offCenter : Base
  offCenter_ne : offCenter ≠ center
  rotation_pow : rotation ^ m = 1
  rotation_fixed_iff : ∀ k, 0 < k → k < m → ∀ z,
    (rotation ^ k) z = z ↔ z = center
  automorphism : Torus ≃+ Torus
  translation : Torus
  translationVector : Lattice
  translation_fixed : automorphism translation = translation
  automorphism_pow : automorphism.toEquiv ^ m = 1
  translation_torsion : m • translation = 0
  fiber_fixed_iff : ∀ k, 0 < k → k < m →
    ((∃ x : Torus, (affineEquiv automorphism translation ^ k) x = x) ↔
      (m : ℤ) ∣ (k : ℤ) * gamma translationVector)

namespace EllipticActionData

variable {m : ℕ} [NeZero m] {Base Torus : Type*} [AddCommGroup Torus]
    (D : EllipticActionData m Base Torus)

@[expose] public def fiberGenerator : Equiv.Perm Torus :=
  affineEquiv D.automorphism D.translation

@[expose] public def diagonalGenerator : Equiv.Perm (Base × Torus) :=
  D.rotation.prodCongr D.fiberGenerator

public theorem fiberGenerator_pow : D.fiberGenerator ^ m = 1 :=
  affineEquiv_pow_eq_one D.automorphism D.translation D.translation_fixed m
    D.automorphism_pow D.translation_torsion

public theorem diagonalGenerator_pow_apply (k : ℕ) (z : Base) (x : Torus) :
    (D.diagonalGenerator ^ k) (z, x) =
      ((D.rotation ^ k) z, (D.fiberGenerator ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      rfl

public theorem diagonalGenerator_pow : D.diagonalGenerator ^ m = 1 := by
  apply Equiv.ext
  rintro ⟨z, x⟩
  have hpair := D.diagonalGenerator_pow_apply m z x
  have hr := congrArg (fun e : Equiv.Perm Base ↦ e z) D.rotation_pow
  have hf := congrArg (fun e : Equiv.Perm Torus ↦ e x) D.fiberGenerator_pow
  rw [hpair, hr, hf]
  rfl


@[expose] public noncomputable def representation :
    FiniteCyclic m →* Equiv.Perm (Base × Torus) :=
  cyclicRepresentation m D.diagonalGenerator D.diagonalGenerator_pow

@[simp]
public theorem representation_generator :
    D.representation (cyclicGenerator m) = D.diagonalGenerator :=
  cyclicRepresentation_generator m D.diagonalGenerator D.diagonalGenerator_pow

@[expose, instance_reducible] public noncomputable def diagonalAction :
    MulAction (FiniteCyclic m) (Base × Torus) where
  smul g p := D.representation g p
  one_smul p := by
    change D.representation 1 p = p
    rw [map_one]
    rfl
  mul_smul g h p := by
    change D.representation (g * h) p =
      D.representation g (D.representation h p)
    rw [map_mul]
    rfl


public theorem generator_pow_smul (k : ℕ) (p : Base × Torus) :
    letI := D.diagonalAction
    cyclicGenerator m ^ k • p = (D.diagonalGenerator ^ k) p := by
  change D.representation (cyclicGenerator m ^ k) p = _
  rw [map_pow, D.representation_generator]

public theorem diagonal_fixed_iff_fiber_fixed {k : ℕ}
    (hk : 0 < k) (hkm : k < m) :
    (∃ p : Base × Torus, (D.diagonalGenerator ^ k) p = p) ↔
      ∃ x : Torus, (D.fiberGenerator ^ k) x = x := by
  constructor
  · rintro ⟨⟨z, x⟩, h⟩
    have hpair := D.diagonalGenerator_pow_apply k z x
    rw [h] at hpair
    exact ⟨x, (congrArg Prod.snd hpair).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨(D.center, x), ?_⟩
    rw [D.diagonalGenerator_pow_apply, hx]
    rw [(D.rotation_fixed_iff k hk hkm D.center).mpr rfl]

public theorem diagonal_fixed_iff_divides {k : ℕ}
    (hk : 0 < k) (hkm : k < m) :
    (∃ p : Base × Torus, (D.diagonalGenerator ^ k) p = p) ↔
      (m : ℤ) ∣ (k : ℤ) * gamma D.translationVector := by
  rw [D.diagonal_fixed_iff_fiber_fixed hk hkm]
  exact D.fiber_fixed_iff k hk hkm

public theorem isCancelSMul_iff_no_fixed_powers :
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic m) (Base × Torus) ↔
      ∀ k, 0 < k → k < m →
        ¬ ∃ p : Base × Torus, (D.diagonalGenerator ^ k) p = p := by
  let _ := D.diagonalAction
  constructor
  · intro hfree k hk hkm hfixed
    obtain ⟨p, hp⟩ := hfixed
    have hsmul : cyclicGenerator m ^ k • p = p := by
      rw [D.generator_pow_smul]
      exact hp
    exact cyclicGenerator_pow_ne_one hk hkm (IsCancelSMul.eq_one_of_smul hsmul)
  · intro hfree
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro g p hp
    let k := (Multiplicative.toAdd g).val
    by_cases hk : k = 0
    · change (Multiplicative.toAdd g).val = 0 at hk
      rw [cyclic_eq_generator_pow g, hk, pow_zero]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have hklt : k < m := ZMod.val_lt _
      exfalso
      apply hfree k hkpos hklt
      refine ⟨p, ?_⟩
      rw [← D.generator_pow_smul]
      rwa [← cyclic_eq_generator_pow g]

public theorem isCancelSMul_iff_character :
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic m) (Base × Torus) ↔
      ∀ k, 0 < k → k < m →
        ¬ (m : ℤ) ∣ (k : ℤ) * gamma D.translationVector := by
  rw [D.isCancelSMul_iff_no_fixed_powers]
  constructor <;> intro h k hk hkm
  · simpa only [D.diagonal_fixed_iff_divides hk hkm] using h k hk hkm
  · simpa only [D.diagonal_fixed_iff_divides hk hkm] using h k hk hkm


end EllipticActionData

public theorem epsilon_character_free :
    ∀ k : ℕ, 0 < k → k < 3 →
      ¬ (3 : ℤ) ∣ (k : ℤ) * gamma epsilon := by
  intro k hk hkm hdiv
  rw [gamma_epsilon, mul_one] at hdiv
  omega

public theorem neg_epsilonPrime_character_free :
    ∀ k : ℕ, 0 < k → k < 4 →
      ¬ (4 : ℤ) ∣ (k : ℤ) * gamma (-epsilon') := by
  intro k hk hkm hdiv
  rw [gamma_neg_epsilon'] at hdiv
  omega

public theorem epsilon_action_free {Base Torus : Type*} [AddCommGroup Torus]
    (D : EllipticActionData 3 Base Torus) (hv : D.translationVector = epsilon) :
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic 3) (Base × Torus) := by
  rw [D.isCancelSMul_iff_character]
  intro k hk hkm hdiv
  rw [hv, gamma_epsilon, mul_one] at hdiv
  omega

public theorem neg_epsilonPrime_action_free {Base Torus : Type*} [AddCommGroup Torus]
    (D : EllipticActionData 4 Base Torus) (hv : D.translationVector = -epsilon') :
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic 4) (Base × Torus) := by
  rw [D.isCancelSMul_iff_character]
  intro k hk hkm hdiv
  rw [hv, gamma_neg_epsilon'] at hdiv
  omega



end SphereSixComplex.Geometry
