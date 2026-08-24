module

public import SphereSixComplex.Geometry.EllipticFamilySpecialization

/-!
# The affine fixed-point criterion on the two elliptic period fibres

This file proves the remaining coefficient calculation for the actual period-torus fibres.
-/

namespace SphereSixComplex.Geometry.EllipticFixedPointCriterion

open Matrix SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup
open SphereSixComplex.Periods SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticFamilySpecialization

noncomputable section

/-- Real scalar extension of the invariant integral character `gamma`. -/
@[expose] public noncomputable def gammaReal : RealPeriods →ₗ[ℝ] ℝ :=
  Fintype.linearCombination ℝ
    (fun i : Fin 4 ↦ ((gamma (integralBasisVector i) : ℤ) : ℝ))

public theorem lattice_eq_sum_integralBasisVector (v : Lattice) :
    v = ∑ i, v i • integralBasisVector i := by
  symm
  simpa [Pi.basisFun_repr, Pi.basisFun_apply, integralBasisVector] using
    (Pi.basisFun ℤ (Fin 4)).sum_repr v

public theorem gammaReal_integer (v : Lattice) :
    gammaReal (integerToReal v) = (gamma v : ℤ) := by
  have hgamma : gamma v = ∑ i, v i * gamma (integralBasisVector i) := by
    calc
      gamma v = gamma (∑ i, v i • integralBasisVector i) :=
        congrArg gamma (lattice_eq_sum_integralBasisVector v)
      _ = ∑ i, v i * gamma (integralBasisVector i) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simpa [smul_eq_mul] using gamma.map_smul (v i) (integralBasisVector i)
  rw [gammaReal, Fintype.linearCombination_apply]
  simp only [integerToReal, smul_eq_mul]
  exact_mod_cast hgamma.symm

public theorem gammaReal_rhoLambdaReal_gOne (u : RealPeriods) :
    gammaReal (rhoLambdaReal g₁ u) = gammaReal u := by
  let L := gammaReal.comp (rhoLambdaReal g₁).toLinearMap
  have hL : L = gammaReal := by
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro i
    rw [← integerToReal_integralBasisVector]
    simp [L, gammaReal_integer, rhoLambdaReal_integer, gamma_A₁]
  exact DFunLike.congr_fun hL u

public theorem gammaReal_rhoLambdaReal_gTwo (u : RealPeriods) :
    gammaReal (rhoLambdaReal g₂ u) = gammaReal u := by
  let L := gammaReal.comp (rhoLambdaReal g₂).toLinearMap
  have hL : L = gammaReal := by
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro i
    rw [← integerToReal_integralBasisVector]
    simp [L, gammaReal_integer, rhoLambdaReal_integer, gamma_A₂]
  exact DFunLike.congr_fun hL u

/-- Real coefficients of a vector in the canonical full-rank period basis. -/
@[expose] public noncomputable def periodCoordinates (x : PeriodDomain)
    (z : ComplexTwoSpace) : RealPeriods :=
  (fullRankDomain x).realEquiv.symm z

public theorem periodCoordinates_periodVector (x : PeriodDomain) (v : Lattice) :
    periodCoordinates x (periodVector x.1 v) = integerToReal v := by
  apply (fullRankDomain x).realEquiv.injective
  change (fullRankDomain x).realEquiv
      ((fullRankDomain x).realEquiv.symm (periodVector x.1 v)) = _
  rw [(fullRankDomain x).realEquiv.apply_symm_apply]
  exact ((fullRankDomain x).map_integer v).symm

public theorem periodCoordinates_transport (g : Delta) (x : PeriodDomain)
    (z : ComplexTwoSpace) :
    periodCoordinates (rhoParameters g x) (periodTransport g x z) =
      rhoLambdaReal g (periodCoordinates x z) := by
  simp [periodCoordinates, periodTransport]

public theorem gammaReal_periodCoordinates_periodVector (x : PeriodDomain) (v : Lattice) :
    gammaReal (periodCoordinates x (periodVector x.1 v)) = (gamma v : ℤ) := by
  rw [periodCoordinates_periodVector, gammaReal_integer]

/-- The invariant character evaluated on the real period coordinates of a cover vector. -/
@[expose] public noncomputable def gammaCoordinate (x : PeriodDomain) :
    ComplexTwoSpace →ₗ[ℝ] ℝ :=
  gammaReal.comp (fullRankDomain x).realEquiv.symm.toLinearMap

public theorem gammaCoordinate_periodVector (x : PeriodDomain) (v : Lattice) :
    gammaCoordinate x (periodVector x.1 v) = (gamma v : ℤ) :=
  gammaReal_periodCoordinates_periodVector x v

section EllipticFibres

variable {U : TriangleUniformization} (F : PeriodFunctions U)

public theorem gammaReal_orderThreeTransport (z : ComplexTwoSpace) :
    gammaReal (periodCoordinates (parameterMap F U.zOne)
      (periodTransport g₁ (parameterMap F U.zOne) z)) =
      gammaReal (periodCoordinates (parameterMap F U.zOne) z) := by
  have h := periodCoordinates_transport g₁ (parameterMap F U.zOne) z
  rw [parameterMap_zOne_fixed F] at h
  rw [h, gammaReal_rhoLambdaReal_gOne]

public theorem gammaCoordinate_orderThreeTransport (z : ComplexTwoSpace) :
    gammaCoordinate (parameterMap F U.zOne)
        (periodTransport g₁ (parameterMap F U.zOne) z) =
      gammaCoordinate (parameterMap F U.zOne) z :=
  gammaReal_orderThreeTransport F z

public theorem gammaReal_orderFourTransport (z : ComplexTwoSpace) :
    gammaReal (periodCoordinates (parameterMap F U.zTwo)
      (periodTransport g₂ (parameterMap F U.zTwo) z)) =
      gammaReal (periodCoordinates (parameterMap F U.zTwo) z) := by
  have h := periodCoordinates_transport g₂ (parameterMap F U.zTwo) z
  rw [parameterMap_zTwo_fixed F] at h
  rw [h, gammaReal_rhoLambdaReal_gTwo]

public theorem gammaCoordinate_orderFourTransport (z : ComplexTwoSpace) :
    gammaCoordinate (parameterMap F U.zTwo)
        (periodTransport g₂ (parameterMap F U.zTwo) z) =
      gammaCoordinate (parameterMap F U.zTwo) z :=
  gammaReal_orderFourTransport F z

public theorem gammaCoordinate_orderThreeTranslation :
    gammaCoordinate (parameterMap F U.zOne)
      ((3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) = (3 : ℝ)⁻¹ := by
  have hs : ((3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) =
      (3 : ℝ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon := by
    ext i
    simp [Complex.real_smul]
  rw [hs]
  rw [map_smul, gammaCoordinate_periodVector, gamma_epsilon]
  norm_num

public theorem gammaCoordinate_orderFourTranslation :
    gammaCoordinate (parameterMap F U.zTwo)
      ((4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) =
        -(4 : ℝ)⁻¹ := by
  have hs : ((4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) =
      (4 : ℝ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon') := by
    ext i
    simp [Complex.real_smul]
  rw [hs]
  rw [map_smul, gammaCoordinate_periodVector, gamma_neg_epsilon']
  norm_num

public theorem quotient_eq_iff_exists_period {x : Parameters} (z w : ComplexTwoSpace) :
    (Quotient.mk _ z : AdditiveTorus x) = Quotient.mk _ w ↔
      ∃ v : Lattice, periodVector x v + w = z := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    rcases g.toAdd.2 with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change g.toAdd.1 + w = z at hg
    change periodVector x v = g.toAdd.1 at hv
    rwa [hv]
  · rintro ⟨v, hv⟩
    let g : PeriodGroup x := Multiplicative.ofAdd ⟨periodVector x v, ⟨v, rfl⟩⟩
    refine ⟨g, ?_⟩
    exact hv

public theorem nsmul_orderThreeTranslation_mk (k : ℕ) :
    k • orderThreeTranslation (parameterMap F U.zOne).1 =
      Quotient.mk _ (k • ((3 : ℂ)⁻¹ •
        periodVector (parameterMap F U.zOne).1 epsilon)) := by
  change k • additiveTorusProjectionHom (parameterMap F U.zOne).1
      ((3 : ℂ)⁻¹ • periodVector (parameterMap F U.zOne).1 epsilon) = _
  exact (map_nsmul (additiveTorusProjectionHom (parameterMap F U.zOne).1) _ _).symm

public theorem nsmul_orderFourTranslation_mk (k : ℕ) :
    k • orderFourTranslation (parameterMap F U.zTwo).1 =
      Quotient.mk _ (k • ((4 : ℂ)⁻¹ •
        periodVector (parameterMap F U.zTwo).1 (-epsilon'))) := by
  change k • additiveTorusProjectionHom (parameterMap F U.zTwo).1
      ((4 : ℂ)⁻¹ • periodVector (parameterMap F U.zTwo).1 (-epsilon')) = _
  exact (map_nsmul (additiveTorusProjectionHom (parameterMap F U.zTwo).1) _ _).symm

public theorem orderThree_coverEquation_impossible (k : ℕ) (hk : 0 < k) (hkm : k < 3)
    (z : ComplexTwoSpace) (v : Lattice)
    (T : ComplexTwoSpace)
    (hT : gammaCoordinate (parameterMap F U.zOne) T =
      gammaCoordinate (parameterMap F U.zOne) z)
    (h : periodVector (parameterMap F U.zOne).1 v + z =
      T + k • ((3 : ℂ)⁻¹ •
        periodVector (parameterMap F U.zOne).1 epsilon)) : False := by
  have hc := congrArg (gammaCoordinate (parameterMap F U.zOne)) h
  simp only [map_add, map_nsmul] at hc
  rw [gammaCoordinate_periodVector, hT, gammaCoordinate_orderThreeTranslation] at hc
  have hre : (3 : ℝ) * (gamma v : ℤ) = k := by
    simp only [nsmul_eq_mul] at hc
    norm_num at hc ⊢
    linarith
  have hint : (3 : ℤ) * gamma v = k := by
    exact_mod_cast hre
  have hdiv : (3 : ℤ) ∣ (k : ℤ) * gamma epsilon := by
    rw [gamma_epsilon, mul_one]
    exact ⟨gamma v, by omega⟩
  exact epsilon_character_free k hk hkm hdiv

public theorem orderFour_coverEquation_impossible (k : ℕ) (hk : 0 < k) (hkm : k < 4)
    (z : ComplexTwoSpace) (v : Lattice)
    (T : ComplexTwoSpace)
    (hT : gammaCoordinate (parameterMap F U.zTwo) T =
      gammaCoordinate (parameterMap F U.zTwo) z)
    (h : periodVector (parameterMap F U.zTwo).1 v + z =
      T + k • ((4 : ℂ)⁻¹ •
        periodVector (parameterMap F U.zTwo).1 (-epsilon'))) : False := by
  have hc := congrArg (gammaCoordinate (parameterMap F U.zTwo)) h
  simp only [map_add, map_nsmul] at hc
  rw [gammaCoordinate_periodVector, hT, gammaCoordinate_orderFourTranslation] at hc
  have hre : (4 : ℝ) * (gamma v : ℤ) = -(k : ℝ) := by
    simp only [nsmul_eq_mul] at hc
    norm_num at hc ⊢
    linarith
  have hint : (4 : ℤ) * gamma v = -(k : ℤ) := by
    exact_mod_cast hre
  have hdiv : (4 : ℤ) ∣ (k : ℤ) * gamma (-epsilon') := by
    rw [gamma_neg_epsilon']
    exact ⟨-gamma v, by omega⟩
  exact neg_epsilonPrime_character_free k hk hkm hdiv

public theorem orderThreeFiberAutomorphism_pow_mk (k : ℕ) (z : ComplexTwoSpace) :
    ((orderThreeFiberAutomorphism F).toEquiv ^ k) (Quotient.mk _ z) =
      Quotient.mk _ (((periodTransport g₁ (parameterMap F U.zOne)).toEquiv ^ k) z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      change orderThreeFiberAutomorphism F
        (Quotient.mk _ (((periodTransport g₁ (parameterMap F U.zOne)).toEquiv ^ k) z)) = _
      rw [orderThreeFiberAutomorphism_mk]
      rw [pow_succ', Equiv.Perm.mul_apply]
      rfl

public theorem orderFourFiberAutomorphism_pow_mk (k : ℕ) (z : ComplexTwoSpace) :
    ((orderFourFiberAutomorphism F).toEquiv ^ k) (Quotient.mk _ z) =
      Quotient.mk _ (((periodTransport g₂ (parameterMap F U.zTwo)).toEquiv ^ k) z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      change orderFourFiberAutomorphism F
        (Quotient.mk _ (((periodTransport g₂ (parameterMap F U.zTwo)).toEquiv ^ k) z)) = _
      rw [orderFourFiberAutomorphism_mk]
      rw [pow_succ', Equiv.Perm.mul_apply]
      rfl

public theorem gammaCoordinate_orderThreeTransport_pow (k : ℕ) (z : ComplexTwoSpace) :
    gammaCoordinate (parameterMap F U.zOne)
        (((periodTransport g₁ (parameterMap F U.zOne)).toEquiv ^ k) z) =
      gammaCoordinate (parameterMap F U.zOne) z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change gammaCoordinate (parameterMap F U.zOne)
        (periodTransport g₁ (parameterMap F U.zOne)
          (((periodTransport g₁ (parameterMap F U.zOne)).toEquiv ^ k) z)) = _
      rw [gammaCoordinate_orderThreeTransport, ih]

public theorem gammaCoordinate_orderFourTransport_pow (k : ℕ) (z : ComplexTwoSpace) :
    gammaCoordinate (parameterMap F U.zTwo)
        (((periodTransport g₂ (parameterMap F U.zTwo)).toEquiv ^ k) z) =
      gammaCoordinate (parameterMap F U.zTwo) z := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change gammaCoordinate (parameterMap F U.zTwo)
        (periodTransport g₂ (parameterMap F U.zTwo)
          (((periodTransport g₂ (parameterMap F U.zTwo)).toEquiv ^ k) z)) = _
      rw [gammaCoordinate_orderFourTransport, ih]

public theorem orderThree_affine_pow_no_fixed (k : ℕ) (hk : 0 < k) (hkm : k < 3) :
    ¬ ∃ q : AdditiveTorus (parameterMap F U.zOne).1,
      (affineEquiv (orderThreeFiberAutomorphism F)
        (orderThreeTranslation (parameterMap F U.zOne).1) ^ k) q = q := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | _ z =>
    rw [affineEquiv_pow_apply _ _ (orderThreeFiberAutomorphism_translation F),
      orderThreeFiberAutomorphism_pow_mk, nsmul_orderThreeTranslation_mk] at hq
    rw [← additiveTorus_mk_add] at hq
    obtain ⟨v, hv⟩ := (quotient_eq_iff_exists_period _ _).mp hq
    exact orderThree_coverEquation_impossible F k hk hkm z v _
      (gammaCoordinate_orderThreeTransport_pow F k z) hv

public theorem orderFour_affine_pow_no_fixed (k : ℕ) (hk : 0 < k) (hkm : k < 4) :
    ¬ ∃ q : AdditiveTorus (parameterMap F U.zTwo).1,
      (affineEquiv (orderFourFiberAutomorphism F)
        (orderFourTranslation (parameterMap F U.zTwo).1) ^ k) q = q := by
  rintro ⟨q, hq⟩
  induction q using Quotient.inductionOn with
  | _ z =>
    rw [affineEquiv_pow_apply _ _ (orderFourFiberAutomorphism_translation F),
      orderFourFiberAutomorphism_pow_mk, nsmul_orderFourTranslation_mk] at hq
    rw [← additiveTorus_mk_add] at hq
    obtain ⟨v, hv⟩ := (quotient_eq_iff_exists_period _ _).mp hq
    exact orderFour_coverEquation_impossible F k hk hkm z v _
      (gammaCoordinate_orderFourTransport_pow F k z) hv

/-- Lemma 5.5 for the actual order-three period torus. -/
public theorem orderThreeFiberFixedPointCriterion :
    OrderThreeFiberFixedPointCriterion F := by
  intro k hk hkm
  constructor
  · exact fun h ↦ (orderThree_affine_pow_no_fixed F k hk hkm h).elim
  · intro hdiv
    exact (epsilon_character_free k hk hkm hdiv).elim

/-- Lemma 5.5 for the actual order-four period torus. -/
public theorem orderFourFiberFixedPointCriterion :
    OrderFourFiberFixedPointCriterion F := by
  intro k hk hkm
  constructor
  · exact fun h ↦ (orderFour_affine_pow_no_fixed F k hk hkm h).elim
  · intro hdiv
    exact (neg_epsilonPrime_character_free k hk hkm hdiv).elim

/-- Unconditional elliptic fibre data on the actual order-three period torus. -/
@[expose] public noncomputable def orderThreeFiberData :
    EllipticFiberData 3 (AdditiveTorus (parameterMap F U.zOne).1) :=
  EllipticFamilySpecialization.orderThreeFiberData F
    (orderThreeFiberFixedPointCriterion F)

/-- Unconditional elliptic fibre data on the actual order-four period torus. -/
@[expose] public noncomputable def orderFourFiberData :
    EllipticFiberData 4 (AdditiveTorus (parameterMap F U.zTwo).1) :=
  EllipticFamilySpecialization.orderFourFiberData F
    (orderFourFiberFixedPointCriterion F)

/-- The complete order-three Cayley-disc action on the actual fixed period torus. -/
@[expose] public noncomputable def orderThreeActionData :
    EllipticActionData 3 ComplexUnitDisc
      (AdditiveTorus (parameterMap F U.zOne).1) :=
  (orderThreeFiberData F).orderThreeActionData

/-- The complete order-four Cayley-disc action on the actual fixed period torus. -/
@[expose] public noncomputable def orderFourActionData :
    EllipticActionData 4 ComplexUnitDisc
      (AdditiveTorus (parameterMap F U.zTwo).1) :=
  (orderFourFiberData F).orderFourActionData

/-- The unconditional order-three local elliptic action is free. -/
public theorem orderThreeAction_free :
    let D := orderThreeActionData F
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic 3)
      (ComplexUnitDisc × AdditiveTorus (parameterMap F U.zOne).1) := by
  exact orderThreeActualAction_free F (orderThreeFiberFixedPointCriterion F)

/-- The unconditional order-four local elliptic action is free. -/
public theorem orderFourAction_free :
    let D := orderFourActionData F
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic 4)
      (ComplexUnitDisc × AdditiveTorus (parameterMap F U.zTwo).1) := by
  exact orderFourActualAction_free F (orderFourFiberFixedPointCriterion F)

end EllipticFibres

end

end SphereSixComplex.Geometry.EllipticFixedPointCriterion
