module

public import SphereSixComplex.Paper.Geometry.TorusFamily
public import Mathlib.Topology.Homeomorph.Quotient

/-!
# Equivariance of the torus family

The three triangle-group generators preserve the period lattices, up to the fibrewise complex
linear changes of coordinates occurring in the period-matrix identities.
-/

open scoped Manifold

namespace SphereSixComplex.Geometry.FamilyEquivariance

open Matrix SphereSixComplex.Geometry SphereSixComplex.Geometry.ComplexTorus
  SphereSixComplex.Periods SphereSixComplex.TriangleGroup

public noncomputable section

/-- Casting an integral matrix-vector product to `ℂ` commutes with matrix-vector
multiplication. -/
public theorem int_mulVec_cast (A : Matrix (Fin 4) (Fin 4) ℤ) (n : IntegerPeriods) :
    (fun i ↦ ((A *ᵥ n) i : ℂ)) = A.map (Int.castRingHom ℂ) *ᵥ (fun i ↦ (n i : ℂ)) := by
  ext i
  change (Int.castRingHom ℂ) ((A *ᵥ n) i) =
    (A.map (Int.castRingHom ℂ) *ᵥ ((Int.castRingHom ℂ) ∘ n)) i
  exact RingHom.map_mulVec (Int.castRingHom ℂ) A n i

/-- The first generator's period-vector equivariance. -/
public theorem generatorOne_periodVector (x : Parameters) (htau : x.tau ≠ 0)
    (n : IntegerPeriods) :
    periodVector (transformOne x) (a₁ n) = rightOne x *ᵥ periodVector x n := by
  change periodMatrix (transformOne x) *ᵥ (fun i ↦ ((a₁ n) i : ℂ)) = _
  rw [a₁_apply, int_mulVec_cast]
  change periodMatrix (transformOne x) *ᵥ (A₁Complex *ᵥ (fun i ↦ (n i : ℂ))) = _
  rw [Matrix.mulVec_mulVec, generatorOne_equivariance x htau,
    ← Matrix.mulVec_mulVec]
  rfl

/-- The second generator's period-vector equivariance. -/
public theorem generatorTwo_periodVector (x : Parameters) (htau : x.tau ≠ 0)
    (n : IntegerPeriods) :
    periodVector (transformTwo x) (a₂ n) = rightTwo x *ᵥ periodVector x n := by
  change periodMatrix (transformTwo x) *ᵥ (fun i ↦ ((a₂ n) i : ℂ)) = _
  rw [a₂_apply, int_mulVec_cast]
  change periodMatrix (transformTwo x) *ᵥ (A₂Complex *ᵥ (fun i ↦ (n i : ℂ))) = _
  rw [Matrix.mulVec_mulVec, generatorTwo_equivariance x htau,
    ← Matrix.mulVec_mulVec]
  rfl

/-- The cusp generator's period-vector equivariance. -/
public theorem cusp_periodVector (x : Parameters) (n : IntegerPeriods) :
    periodVector (transformCusp x) (m₀ n) = periodVector x n := by
  change periodMatrix (transformCusp x) *ᵥ (fun i ↦ ((m₀ n) i : ℂ)) = _
  rw [m₀_apply, int_mulVec_cast]
  change periodMatrix (transformCusp x) *ᵥ (M₀Complex *ᵥ (fun i ↦ (n i : ℂ))) = _
  rw [Matrix.mulVec_mulVec, cusp_equivariance]
  rfl

/-- The first generator's fibre coordinate change as a complex-linear equivalence. -/
@[expose] public def rightOneLinearEquiv (x : Parameters) (htau : x.tau ≠ 0) :
    ComplexTwoSpace ≃ₗ[ℂ] ComplexTwoSpace :=
  (rightOne x).toLinearEquiv'
    (Matrix.invertibleOfIsUnitDet (rightOne x) (rightOne_isUnit_det x htau))

@[simp]
public theorem rightOneLinearEquiv_apply (x : Parameters) (htau : x.tau ≠ 0)
    (z : ComplexTwoSpace) :
    rightOneLinearEquiv x htau z = rightOne x *ᵥ z := by
  change Matrix.toLin' (rightOne x) z = _
  rfl

/-- The second generator's fibre coordinate change as a complex-linear equivalence. -/
@[expose] public def rightTwoLinearEquiv (x : Parameters) (htau : x.tau ≠ 0) :
    ComplexTwoSpace ≃ₗ[ℂ] ComplexTwoSpace :=
  (rightTwo x).toLinearEquiv'
    (Matrix.invertibleOfIsUnitDet (rightTwo x) (rightTwo_isUnit_det x htau))

@[simp]
public theorem rightTwoLinearEquiv_apply (x : Parameters) (htau : x.tau ≠ 0)
    (z : ComplexTwoSpace) :
    rightTwoLinearEquiv x htau z = rightTwo x *ᵥ z := by
  change Matrix.toLin' (rightTwo x) z = _
  rfl

/-- The continuous complex-linear form of the first fibre coordinate change. -/
@[expose] public def rightOneContinuousLinearEquiv (x : Parameters) (htau : x.tau ≠ 0) :
    ComplexTwoSpace ≃L[ℂ] ComplexTwoSpace :=
  (rightOneLinearEquiv x htau).toContinuousLinearEquiv

/-- The continuous complex-linear form of the second fibre coordinate change. -/
@[expose] public def rightTwoContinuousLinearEquiv (x : Parameters) (htau : x.tau ≠ 0) :
    ComplexTwoSpace ≃L[ℂ] ComplexTwoSpace :=
  (rightTwoLinearEquiv x htau).toContinuousLinearEquiv

/-- An additive equivalence of coefficient lattices and an equivariant additive equivalence of
fibres identify the corresponding orbit relations. -/
public theorem orbitRel_iff_of_period_equivariant (x y : Parameters)
    (eN : IntegerPeriods ≃+ IntegerPeriods)
    (eZ : ComplexTwoSpace ≃+ ComplexTwoSpace)
    (heq : ∀ n, eZ (periodVector x n) = periodVector y (eN n))
    (z w : ComplexTwoSpace) :
    (MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace) z w ↔
      (MulAction.orbitRel (PeriodGroup y) ComplexTwoSpace) (eZ z) (eZ w) := by
  simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    have hgmem := g.toAdd.property
    change ∃ a, periodHom x a = (g.toAdd : ComplexTwoSpace) at hgmem
    rcases hgmem with ⟨a, ha⟩
    change periodVector x a = (g.toAdd : ComplexTwoSpace) at ha
    let g' : PeriodGroup y := Multiplicative.ofAdd
      ⟨periodVector y (eN a), ⟨eN a, rfl⟩⟩
    refine ⟨g', ?_⟩
    change periodVector y (eN a) + eZ w = eZ z
    rw [← heq, ← eZ.map_add]
    apply congrArg eZ
    rw [ha]
    exact hg
  · rintro ⟨g, hg⟩
    have hgmem := g.toAdd.property
    change ∃ b, periodHom y b = (g.toAdd : ComplexTwoSpace) at hgmem
    rcases hgmem with ⟨b, hb⟩
    change periodVector y b = (g.toAdd : ComplexTwoSpace) at hb
    let a := eN.symm b
    let g' : PeriodGroup x := Multiplicative.ofAdd
      ⟨periodVector x a, ⟨a, rfl⟩⟩
    refine ⟨g', ?_⟩
    change periodVector x a + w = z
    apply eZ.injective
    rw [eZ.map_add, heq]
    rw [show eN a = b by exact eN.apply_symm_apply b]
    rw [hb]
    exact hg

/-- The first generator identifies the source and transformed period-lattice orbit relations. -/
public theorem generatorOne_orbitRel_iff (x : Parameters) (htau : x.tau ≠ 0)
    (z w : ComplexTwoSpace) :
    (MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace) z w ↔
      (MulAction.orbitRel (PeriodGroup (transformOne x)) ComplexTwoSpace)
        (rightOneLinearEquiv x htau z) (rightOneLinearEquiv x htau w) := by
  apply orbitRel_iff_of_period_equivariant x (transformOne x) a₁.toAddEquiv
    (rightOneLinearEquiv x htau).toAddEquiv
  intro n
  change rightOneLinearEquiv x htau (periodVector x n) =
    periodVector (transformOne x) (a₁ n)
  rw [rightOneLinearEquiv_apply]
  exact (generatorOne_periodVector x htau n).symm

/-- The second generator identifies the source and transformed period-lattice orbit relations. -/
public theorem generatorTwo_orbitRel_iff (x : Parameters) (htau : x.tau ≠ 0)
    (z w : ComplexTwoSpace) :
    (MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace) z w ↔
      (MulAction.orbitRel (PeriodGroup (transformTwo x)) ComplexTwoSpace)
        (rightTwoLinearEquiv x htau z) (rightTwoLinearEquiv x htau w) := by
  apply orbitRel_iff_of_period_equivariant x (transformTwo x) a₂.toAddEquiv
    (rightTwoLinearEquiv x htau).toAddEquiv
  intro n
  change rightTwoLinearEquiv x htau (periodVector x n) =
    periodVector (transformTwo x) (a₂ n)
  rw [rightTwoLinearEquiv_apply]
  exact (generatorTwo_periodVector x htau n).symm


/-- The first triangle-group generator descends to a homeomorphism of complex tori. -/
@[expose] public def generatorOneTorusHomeomorph (x : Parameters) (htau : x.tau ≠ 0) :
    Torus x ≃ₜ Torus (transformOne x) :=
  Homeomorph.Quotient.congr (rightOneContinuousLinearEquiv x htau).toHomeomorph
    (generatorOne_orbitRel_iff x htau)

/-- The second triangle-group generator descends to a homeomorphism of complex tori. -/
@[expose] public def generatorTwoTorusHomeomorph (x : Parameters) (htau : x.tau ≠ 0) :
    Torus x ≃ₜ Torus (transformTwo x) :=
  Homeomorph.Quotient.congr (rightTwoContinuousLinearEquiv x htau).toHomeomorph
    (generatorTwo_orbitRel_iff x htau)


@[simp]
public theorem generatorOneTorusHomeomorph_mk (x : Parameters) (htau : x.tau ≠ 0)
    (z : ComplexTwoSpace) :
    generatorOneTorusHomeomorph x htau (Quotient.mk _ z) =
      Quotient.mk _ (rightOneLinearEquiv x htau z) :=
  rfl

@[simp]
public theorem generatorTwoTorusHomeomorph_mk (x : Parameters) (htau : x.tau ≠ 0)
    (z : ComplexTwoSpace) :
    generatorTwoTorusHomeomorph x htau (Quotient.mk _ z) =
      Quotient.mk _ (rightTwoLinearEquiv x htau z) :=
  rfl










end

end SphereSixComplex.Geometry.FamilyEquivariance
