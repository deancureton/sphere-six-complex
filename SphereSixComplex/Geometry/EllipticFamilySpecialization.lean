module

public import SphereSixComplex.Geometry.EllipticLocalCoordinates
public import SphereSixComplex.Geometry.GlobalDeckQuotient

/-!
# Specializing the elliptic fillings to the analytic torus family

This file supplies the additive-group structure missing from the orbit-quotient presentation of
an individual period torus, records the generator transports at the two elliptic fixed points,
and isolates the one remaining local trivialization/fixed-point calculation needed to identify
those fibres with the affine models used by the elliptic filling API.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.EllipticFamilySpecialization

open SphereSixComplex.LatticeData SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.FamilyEquivariance
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLocalCoordinates

noncomputable section

/-- A tagged copy of the existing orbit quotient, equipped below with its natural additive group
structure.  The underlying type is definitionally the actual complex torus fibre. -/
public abbrev AdditiveTorus (x : Parameters) := Torus x

public theorem orbitRel_add {x : Parameters} {a₁ a₂ b₁ b₂ : ComplexTwoSpace}
    (ha : MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace a₁ a₂)
    (hb : MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace b₁ b₂) :
    MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace (a₁ + b₁) (a₂ + b₂) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at ha hb ⊢
  rcases ha with ⟨ga, hga⟩
  rcases hb with ⟨gb, hgb⟩
  let g : PeriodGroup x := Multiplicative.ofAdd ⟨ga.toAdd.1 + gb.toAdd.1,
    AddSubgroup.add_mem _ ga.toAdd.2 gb.toAdd.2⟩
  refine ⟨g, ?_⟩
  change (ga.toAdd.1 + gb.toAdd.1) + (a₂ + b₂) = a₁ + b₁
  change ga.toAdd.1 + a₂ = a₁ at hga
  change gb.toAdd.1 + b₂ = b₁ at hgb
  rw [← hga, ← hgb]
  abel

public theorem orbitRel_neg {x : Parameters} {a b : ComplexTwoSpace}
    (h : MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace a b) :
    MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace (-a) (-b) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  rcases h with ⟨g, hg⟩
  let g' : PeriodGroup x := Multiplicative.ofAdd ⟨-g.toAdd.1,
    AddSubgroup.neg_mem _ g.toAdd.2⟩
  refine ⟨g', ?_⟩
  change -g.toAdd.1 + -b = -a
  change g.toAdd.1 + b = a at hg
  rw [← hg]
  abel

@[instance_reducible] public noncomputable instance additiveTorusAdd (x : Parameters) :
    Add (AdditiveTorus x) where
  add := Quotient.map₂ (· + ·) fun _ _ ha _ _ hb ↦ orbitRel_add (x := x) ha hb

@[instance_reducible] public noncomputable instance additiveTorusZero (x : Parameters) :
    Zero (AdditiveTorus x) where
  zero := Quotient.mk _ 0

@[instance_reducible] public noncomputable instance additiveTorusNeg (x : Parameters) :
    Neg (AdditiveTorus x) where
  neg := Quotient.map Neg.neg fun _ _ h ↦ orbitRel_neg (x := x) h

@[simp]
public theorem additiveTorus_mk_add (x : Parameters) (a b : ComplexTwoSpace) :
    (Quotient.mk _ (a + b) : AdditiveTorus x) =
      (Quotient.mk _ a : AdditiveTorus x) +
        (Quotient.mk _ b : AdditiveTorus x) := by
  change Quotient.mk _ (a + b) =
    Quotient.map₂ (· + ·) _ (Quotient.mk _ a) (Quotient.mk _ b)
  rfl

@[simp]
public theorem additiveTorus_mk_zero (x : Parameters) :
    (Quotient.mk _ 0 : AdditiveTorus x) = 0 := by rfl

@[simp]
public theorem additiveTorus_mk_neg (x : Parameters) (a : ComplexTwoSpace) :
    (Quotient.mk _ (-a) : AdditiveTorus x) = -(Quotient.mk _ a) := by
  change Quotient.mk _ (-a) = Quotient.map Neg.neg _ (Quotient.mk _ a)
  rfl

public noncomputable instance (x : Parameters) : AddCommGroup (AdditiveTorus x) where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc p q r := by
    induction p using Quotient.inductionOn with
    | _ p => induction q using Quotient.inductionOn with
      | _ q => induction r using Quotient.inductionOn with
        | _ r => simp only [← additiveTorus_mk_add, add_assoc]
  zero_add p := by
    induction p using Quotient.inductionOn with
    | _ p => simp only [← additiveTorus_mk_zero, ← additiveTorus_mk_add, zero_add]
  add_zero p := by
    induction p using Quotient.inductionOn with
    | _ p => simp only [← additiveTorus_mk_zero, ← additiveTorus_mk_add, add_zero]
  neg_add_cancel p := by
    induction p using Quotient.inductionOn with
    | _ p =>
      simp only [← additiveTorus_mk_neg, ← additiveTorus_mk_add, neg_add_cancel,
        additiveTorus_mk_zero]
  add_comm p q := by
    induction p using Quotient.inductionOn with
    | _ p => induction q using Quotient.inductionOn with
      | _ q => simp only [← additiveTorus_mk_add, add_comm]

/-- Projection to the additive presentation of the actual period torus. -/
@[expose] public def additiveTorusProjection (x : Parameters) :
    ComplexTwoSpace → AdditiveTorus x := Quotient.mk _

@[simp]
public theorem additiveTorusProjection_add (x : Parameters) (a b : ComplexTwoSpace) :
    additiveTorusProjection x (a + b) =
      additiveTorusProjection x a + additiveTorusProjection x b :=
  additiveTorus_mk_add x a b

/-- The descended first-generator transport is additive between the corresponding actual
period-torus fibres. -/
@[expose] public noncomputable def generatorOneAddEquiv (x : PeriodDomain) :
    AdditiveTorus x.1 ≃+ AdditiveTorus (transformOne x.1) where
  toEquiv := (generatorOneTorusHomeomorph x.1 x.tau_ne_zero).toEquiv
  map_add' p q := by
    induction p using Quotient.inductionOn with
    | _ p => induction q using Quotient.inductionOn with
      | _ q =>
        rw [← additiveTorus_mk_add]
        change Quotient.mk _ (rightOneLinearEquiv x.1 x.tau_ne_zero (p + q)) = _
        rw [map_add, additiveTorus_mk_add]
        exact congrArg₂ (fun a b ↦ a + b)
          (generatorOneTorusHomeomorph_mk x.1 x.tau_ne_zero p).symm
          (generatorOneTorusHomeomorph_mk x.1 x.tau_ne_zero q).symm

/-- The descended second-generator transport is additive between the corresponding actual
period-torus fibres. -/
@[expose] public noncomputable def generatorTwoAddEquiv (x : PeriodDomain) :
    AdditiveTorus x.1 ≃+ AdditiveTorus (transformTwo x.1) where
  toEquiv := (generatorTwoTorusHomeomorph x.1 x.tau_ne_zero).toEquiv
  map_add' p q := by
    induction p using Quotient.inductionOn with
    | _ p => induction q using Quotient.inductionOn with
      | _ q =>
        rw [← additiveTorus_mk_add]
        change Quotient.mk _ (rightTwoLinearEquiv x.1 x.tau_ne_zero (p + q)) = _
        rw [map_add, additiveTorus_mk_add]
        exact congrArg₂ (fun a b ↦ a + b)
          (generatorTwoTorusHomeomorph_mk x.1 x.tau_ne_zero p).symm
          (generatorTwoTorusHomeomorph_mk x.1 x.tau_ne_zero q).symm

@[simp]
public theorem generatorOneAddEquiv_mk (x : PeriodDomain) (z : ComplexTwoSpace) :
    generatorOneAddEquiv x (Quotient.mk _ z) =
      Quotient.mk _ (rightOneLinearEquiv x.1 x.tau_ne_zero z) :=
  generatorOneTorusHomeomorph_mk x.1 x.tau_ne_zero z

@[simp]
public theorem generatorTwoAddEquiv_mk (x : PeriodDomain) (z : ComplexTwoSpace) :
    generatorTwoAddEquiv x (Quotient.mk _ z) =
      Quotient.mk _ (rightTwoLinearEquiv x.1 x.tau_ne_zero z) :=
  generatorTwoTorusHomeomorph_mk x.1 x.tau_ne_zero z

/-- The vector-space projection as an additive homomorphism. -/
@[expose] public noncomputable def additiveTorusProjectionHom (x : Parameters) :
    ComplexTwoSpace →+ AdditiveTorus x where
  toFun := additiveTorusProjection x
  map_zero' := additiveTorus_mk_zero x
  map_add' := additiveTorusProjection_add x

/-- Every integral period vanishes in the actual period torus. -/
@[simp]
public theorem additiveTorusProjection_periodVector (x : Parameters) (v : Lattice) :
    additiveTorusProjection x (periodVector x v) = 0 := by
  rw [← additiveTorus_mk_zero]
  apply Quotient.sound
  change MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace (periodVector x v) 0
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  let g : PeriodGroup x := Multiplicative.ofAdd
    ⟨periodVector x v, ⟨v, rfl⟩⟩
  refine ⟨g, ?_⟩
  change periodVector x v + 0 = periodVector x v
  exact add_zero _

/-- The order-three translation is the one-third period represented by the invariant vector
`epsilon`. -/
@[expose] public noncomputable def orderThreeTranslation (x : Parameters) : AdditiveTorus x :=
  additiveTorusProjection x ((3 : ℂ)⁻¹ • periodVector x epsilon)

/-- The order-four translation is the one-quarter period represented by `-epsilon'`. -/
@[expose] public noncomputable def orderFourTranslation (x : Parameters) : AdditiveTorus x :=
  additiveTorusProjection x ((4 : ℂ)⁻¹ • periodVector x (-epsilon'))

public theorem orderThreeTranslation_torsion (x : Parameters) :
    3 • orderThreeTranslation x = 0 := by
  change 3 • additiveTorusProjectionHom x ((3 : ℂ)⁻¹ • periodVector x epsilon) = 0
  rw [← map_nsmul (additiveTorusProjectionHom x)]
  rw [show 3 • ((3 : ℂ)⁻¹ • periodVector x epsilon) = periodVector x epsilon by
    ext i
    simp]
  exact additiveTorusProjection_periodVector x epsilon

public theorem orderFourTranslation_torsion (x : Parameters) :
    4 • orderFourTranslation x = 0 := by
  change 4 • additiveTorusProjectionHom x ((4 : ℂ)⁻¹ • periodVector x (-epsilon')) = 0
  rw [← map_nsmul (additiveTorusProjectionHom x)]
  rw [show 4 • ((4 : ℂ)⁻¹ • periodVector x (-epsilon')) =
      periodVector x (-epsilon') by
    ext i
    simp]
  exact additiveTorusProjection_periodVector x (-epsilon')

/-- The first-generator fibre transport carries the canonical order-three twist to itself in
the transformed fibre. -/
public theorem generatorOne_orderThreeTranslation (x : PeriodDomain) :
    generatorOneAddEquiv x (orderThreeTranslation x.1) =
      orderThreeTranslation (transformOne x.1) := by
  change generatorOneAddEquiv x
      (Quotient.mk _ ((3 : ℂ)⁻¹ • periodVector x.1 epsilon)) =
    Quotient.mk _ ((3 : ℂ)⁻¹ • periodVector (transformOne x.1) epsilon)
  rw [generatorOneAddEquiv_mk]
  rw [map_smul]
  apply congrArg (additiveTorusProjection (transformOne x.1))
  rw [rightOneLinearEquiv_apply, ← generatorOne_periodVector x.1 x.tau_ne_zero]
  congr 2
  rw [a₁_apply, A₁_epsilon]

/-- The second-generator fibre transport carries the canonical order-four twist to itself in
the transformed fibre. -/
public theorem generatorTwo_orderFourTranslation (x : PeriodDomain) :
    generatorTwoAddEquiv x (orderFourTranslation x.1) =
      orderFourTranslation (transformTwo x.1) := by
  change generatorTwoAddEquiv x
      (Quotient.mk _ ((4 : ℂ)⁻¹ • periodVector x.1 (-epsilon'))) =
    Quotient.mk _ ((4 : ℂ)⁻¹ • periodVector (transformTwo x.1) (-epsilon'))
  rw [generatorTwoAddEquiv_mk]
  rw [map_smul]
  apply congrArg (additiveTorusProjection (transformTwo x.1))
  rw [rightTwoLinearEquiv_apply, ← generatorTwo_periodVector x.1 x.tau_ne_zero]
  congr 2
  rw [a₂_apply, Matrix.mulVec_neg, A₂_epsilon']

section FixedFibres

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Equivariance makes the period parameter at the order-three source point fixed by the target
generator. -/
public theorem parameterMap_zOne_fixed :
    rhoParameters g₁ (parameterMap F U.zOne) = parameterMap F U.zOne := by
  rw [rhoParameters_g₁_apply]
  apply Subtype.ext
  change transformOne (parameterMap F U.zOne).1 = (parameterMap F U.zOne).1
  rw [parameterMap_val, ← F.transform_one U.zOne, U.zOne_fixed]

/-- Equivariance makes the period parameter at the order-four source point fixed by the target
generator. -/
public theorem parameterMap_zTwo_fixed :
    rhoParameters g₂ (parameterMap F U.zTwo) = parameterMap F U.zTwo := by
  rw [rhoParameters_g₂_apply]
  apply Subtype.ext
  change transformTwo (parameterMap F U.zTwo).1 = (parameterMap F U.zTwo).1
  rw [parameterMap_val, ← F.transform_two U.zTwo, U.zTwo_fixed]

public theorem transformOne_parameterMap_zOne :
    transformOne (parameterMap F U.zOne).1 = (parameterMap F U.zOne).1 := by
  have h := parameterMap_zOne_fixed F
  rw [rhoParameters_g₁_apply] at h
  exact congrArg Subtype.val h

public theorem transformTwo_parameterMap_zTwo :
    transformTwo (parameterMap F U.zTwo).1 = (parameterMap F U.zTwo).1 := by
  have h := parameterMap_zTwo_fixed F
  rw [rhoParameters_g₂_apply] at h
  exact congrArg Subtype.val h

/-- Transport of the additive torus presentation along equality of period parameters. -/
@[expose] public noncomputable def additiveTorusCast {x y : Parameters} (h : x = y) :
    AdditiveTorus x ≃+ AdditiveTorus y := by
  subst y
  exact AddEquiv.refl _

@[simp]
public theorem additiveTorusCast_mk {x y : Parameters} (h : x = y) (z : ComplexTwoSpace) :
    additiveTorusCast h (Quotient.mk _ z) = (Quotient.mk _ z : AdditiveTorus y) := by
  subst y
  rfl

@[simp]
public theorem additiveTorusCast_orderThreeTranslation {x y : Parameters} (h : x = y) :
    additiveTorusCast h (orderThreeTranslation x) = orderThreeTranslation y := by
  subst y
  rfl

@[simp]
public theorem additiveTorusCast_orderFourTranslation {x y : Parameters} (h : x = y) :
    additiveTorusCast h (orderFourTranslation x) = orderFourTranslation y := by
  subst y
  rfl

/-- The first transport becomes an additive automorphism on the actual torus over the fixed
order-three parameter. -/
@[expose] public noncomputable def orderThreeFiberAutomorphism :
    AdditiveTorus (parameterMap F U.zOne).1 ≃+ AdditiveTorus (parameterMap F U.zOne).1 :=
  (generatorOneAddEquiv (parameterMap F U.zOne)).trans
    (additiveTorusCast (transformOne_parameterMap_zOne F))

/-- The second transport becomes an additive automorphism on the actual torus over the fixed
order-four parameter. -/
@[expose] public noncomputable def orderFourFiberAutomorphism :
    AdditiveTorus (parameterMap F U.zTwo).1 ≃+ AdditiveTorus (parameterMap F U.zTwo).1 :=
  (generatorTwoAddEquiv (parameterMap F U.zTwo)).trans
    (additiveTorusCast (transformTwo_parameterMap_zTwo F))

@[simp]
public theorem orderThreeFiberAutomorphism_translation :
    orderThreeFiberAutomorphism F
        (orderThreeTranslation (parameterMap F U.zOne).1) =
      orderThreeTranslation (parameterMap F U.zOne).1 := by
  rw [orderThreeFiberAutomorphism, AddEquiv.trans_apply,
    generatorOne_orderThreeTranslation, additiveTorusCast_orderThreeTranslation]

@[simp]
public theorem orderFourFiberAutomorphism_translation :
    orderFourFiberAutomorphism F
        (orderFourTranslation (parameterMap F U.zTwo).1) =
      orderFourTranslation (parameterMap F U.zTwo).1 := by
  rw [orderFourFiberAutomorphism, AddEquiv.trans_apply,
    generatorTwo_orderFourTranslation, additiveTorusCast_orderFourTranslation]

@[simp]
public theorem orderThreeFiberAutomorphism_mk (z : ComplexTwoSpace) :
    orderThreeFiberAutomorphism F (Quotient.mk _ z) =
      Quotient.mk _ (periodTransport g₁ (parameterMap F U.zOne) z) := by
  rw [orderThreeFiberAutomorphism, AddEquiv.trans_apply, generatorOneAddEquiv_mk,
    additiveTorusCast_mk, periodTransport_gOne]
  rfl

@[simp]
public theorem orderFourFiberAutomorphism_mk (z : ComplexTwoSpace) :
    orderFourFiberAutomorphism F (Quotient.mk _ z) =
      Quotient.mk _ (periodTransport g₂ (parameterMap F U.zTwo) z) := by
  rw [orderFourFiberAutomorphism, AddEquiv.trans_apply, generatorTwoAddEquiv_mk,
    additiveTorusCast_mk, periodTransport_gTwo]
  rfl

public theorem periodTransport_gOne_three (z : ComplexTwoSpace) :
    periodTransport g₁ (parameterMap F U.zOne)
        (periodTransport g₁ (parameterMap F U.zOne)
          (periodTransport g₁ (parameterMap F U.zOne) z)) = z := by
  have h₂ := periodTransport_mul g₁ g₁ (parameterMap F U.zOne)
  rw [parameterMap_zOne_fixed F] at h₂
  have h₃ := periodTransport_mul (g₁ * g₁) g₁ (parameterMap F U.zOne)
  rw [parameterMap_zOne_fixed F, h₂] at h₃
  have hz := DFunLike.congr_fun h₃ z
  rw [show (g₁ * g₁) * g₁ = g₁ ^ 3 by simp [pow_succ], g₁_pow_three,
    periodTransport_one] at hz
  simpa [LinearEquiv.mul_apply] using hz.symm

public theorem periodTransport_gTwo_four (z : ComplexTwoSpace) :
    periodTransport g₂ (parameterMap F U.zTwo)
        (periodTransport g₂ (parameterMap F U.zTwo)
          (periodTransport g₂ (parameterMap F U.zTwo)
            (periodTransport g₂ (parameterMap F U.zTwo) z))) = z := by
  have h₂ := periodTransport_mul g₂ g₂ (parameterMap F U.zTwo)
  rw [parameterMap_zTwo_fixed F] at h₂
  have h₃ := periodTransport_mul (g₂ * g₂) g₂ (parameterMap F U.zTwo)
  rw [parameterMap_zTwo_fixed F, h₂] at h₃
  have h₄ := periodTransport_mul ((g₂ * g₂) * g₂) g₂ (parameterMap F U.zTwo)
  rw [parameterMap_zTwo_fixed F, h₃] at h₄
  have hz := DFunLike.congr_fun h₄ z
  rw [show ((g₂ * g₂) * g₂) * g₂ = g₂ ^ 4 by
      simp [pow_succ], g₂_pow_four,
    periodTransport_one] at hz
  simpa [LinearEquiv.mul_apply] using hz.symm

public theorem orderThreeFiberAutomorphism_pow :
    (orderThreeFiberAutomorphism F).toEquiv ^ 3 = 1 := by
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ z =>
    change orderThreeFiberAutomorphism F
        (orderThreeFiberAutomorphism F
          (orderThreeFiberAutomorphism F (Quotient.mk _ z))) = Quotient.mk _ z
    rw [orderThreeFiberAutomorphism_mk, orderThreeFiberAutomorphism_mk,
      orderThreeFiberAutomorphism_mk, periodTransport_gOne_three]

public theorem orderFourFiberAutomorphism_pow :
    (orderFourFiberAutomorphism F).toEquiv ^ 4 = 1 := by
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ z =>
    change orderFourFiberAutomorphism F
        (orderFourFiberAutomorphism F
          (orderFourFiberAutomorphism F
            (orderFourFiberAutomorphism F (Quotient.mk _ z)))) = Quotient.mk _ z
    rw [orderFourFiberAutomorphism_mk, orderFourFiberAutomorphism_mk,
      orderFourFiberAutomorphism_mk, orderFourFiberAutomorphism_mk,
      periodTransport_gTwo_four]

/-- The exact remaining arithmetic condition on the actual order-three fibre.  All other fields
of `EllipticFiberData` are proved below from period transport and `epsilon`. -/
@[expose] public def OrderThreeFiberFixedPointCriterion : Prop :=
  ∀ k : ℕ, 0 < k → k < 3 →
    ((∃ x : AdditiveTorus (parameterMap F U.zOne).1,
      (affineEquiv (orderThreeFiberAutomorphism F)
        (orderThreeTranslation (parameterMap F U.zOne).1) ^ k) x = x) ↔
      (3 : ℤ) ∣ (k : ℤ) * gamma epsilon)

/-- The exact remaining arithmetic condition on the actual order-four fibre. -/
@[expose] public def OrderFourFiberFixedPointCriterion : Prop :=
  ∀ k : ℕ, 0 < k → k < 4 →
    ((∃ x : AdditiveTorus (parameterMap F U.zTwo).1,
      (affineEquiv (orderFourFiberAutomorphism F)
        (orderFourTranslation (parameterMap F U.zTwo).1) ^ k) x = x) ↔
      (4 : ℤ) ∣ (k : ℤ) * gamma (-epsilon'))

/-- Actual order-three torus-fibre data, conditional only on its explicit affine fixed-point
calculation. -/
@[expose] public noncomputable def orderThreeFiberData
    (hfixed : OrderThreeFiberFixedPointCriterion F) :
    EllipticFiberData 3 (AdditiveTorus (parameterMap F U.zOne).1) where
  automorphism := orderThreeFiberAutomorphism F
  translation := orderThreeTranslation (parameterMap F U.zOne).1
  translationVector := epsilon
  translation_fixed := orderThreeFiberAutomorphism_translation F
  automorphism_pow := orderThreeFiberAutomorphism_pow F
  translation_torsion := orderThreeTranslation_torsion _
  fiber_fixed_iff := by simpa [OrderThreeFiberFixedPointCriterion] using hfixed

/-- Actual order-four torus-fibre data, conditional only on its explicit affine fixed-point
calculation. -/
@[expose] public noncomputable def orderFourFiberData
    (hfixed : OrderFourFiberFixedPointCriterion F) :
    EllipticFiberData 4 (AdditiveTorus (parameterMap F U.zTwo).1) where
  automorphism := orderFourFiberAutomorphism F
  translation := orderFourTranslation (parameterMap F U.zTwo).1
  translationVector := -epsilon'
  translation_fixed := orderFourFiberAutomorphism_translation F
  automorphism_pow := orderFourFiberAutomorphism_pow F
  translation_torsion := orderFourTranslation_torsion _
  fiber_fixed_iff := by simpa [OrderFourFiberFixedPointCriterion] using hfixed

/-- The resulting explicit order-three affine action on the Cayley disc and the actual fixed
period torus is free. -/
public theorem orderThreeActualAction_free
    (hfixed : OrderThreeFiberFixedPointCriterion F) :
    let D := (orderThreeFiberData F hfixed).orderThreeActionData
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic 3)
      (ComplexUnitDisc × AdditiveTorus (parameterMap F U.zOne).1) := by
  exact EllipticFiberData.orderThreeActionData_free (orderThreeFiberData F hfixed) rfl

/-- The resulting explicit order-four affine action on the Cayley disc and the actual fixed
period torus is free. -/
public theorem orderFourActualAction_free
    (hfixed : OrderFourFiberFixedPointCriterion F) :
    let D := (orderFourFiberData F hfixed).orderFourActionData
    letI := D.diagonalAction
    IsCancelSMul (FiniteCyclic 4)
      (ComplexUnitDisc × AdditiveTorus (parameterMap F U.zTwo).1) := by
  exact EllipticFiberData.orderFourActionData_free (orderFourFiberData F hfixed) rfl

/-- Smoothness of the actual descended first-generator deck transport follows from the local
biholomorphism property of the varying-torus projection. -/
public theorem familyDeckMap_gOne_contMDiff
    (n : WithTop ℕ∞)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (familyDeckMap F g₁) :=
  familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph F n hprojection g₁

/-- Smoothness of the actual descended second-generator deck transport follows from the same
varying-family local-biholomorphism hypothesis. -/
public theorem familyDeckMap_gTwo_contMDiff
    (n : WithTop ℕ∞)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (familyDeckMap F g₂) :=
  familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph F n hprojection g₂

end FixedFibres

end


end SphereSixComplex.Geometry.EllipticFamilySpecialization
