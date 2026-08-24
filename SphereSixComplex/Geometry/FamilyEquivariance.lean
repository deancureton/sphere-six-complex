module

public import SphereSixComplex.Geometry.TorusFamily
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

/-- The cusp generator identifies the source and transformed period-lattice orbit relations. -/
public theorem cusp_orbitRel_iff (x : Parameters) (z w : ComplexTwoSpace) :
    (MulAction.orbitRel (PeriodGroup x) ComplexTwoSpace) z w ↔
      (MulAction.orbitRel (PeriodGroup (transformCusp x)) ComplexTwoSpace) z w := by
  simpa using orbitRel_iff_of_period_equivariant x (transformCusp x) m₀.toAddEquiv
    (AddEquiv.refl ComplexTwoSpace) (fun n ↦ (cusp_periodVector x n).symm) z w

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

/-- The cusp generator descends to a homeomorphism of complex tori. -/
@[expose] public def cuspTorusHomeomorph (x : Parameters) :
    Torus x ≃ₜ Torus (transformCusp x) :=
  Homeomorph.Quotient.congr (Homeomorph.refl ComplexTwoSpace) (cusp_orbitRel_iff x)

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

@[simp]
public theorem cuspTorusHomeomorph_mk (x : Parameters) (z : ComplexTwoSpace) :
    cuspTorusHomeomorph x (Quotient.mk _ z) = Quotient.mk _ z :=
  rfl

/-- The torus homeomorphism over the triangle-group generator `g₁`. -/
@[expose] public def rhoGOneTorusHomeomorph (x : PeriodDomain) :
    Torus x.1 ≃ₜ Torus (rhoParameters g₁ x).1 := by
  rw [rhoParameters_g₁_apply]
  change Torus x.1 ≃ₜ Torus (transformOne x.1)
  exact generatorOneTorusHomeomorph x.1 x.tau_ne_zero

/-- The torus homeomorphism over the triangle-group generator `g₂`. -/
@[expose] public def rhoGTwoTorusHomeomorph (x : PeriodDomain) :
    Torus x.1 ≃ₜ Torus (rhoParameters g₂ x).1 := by
  rw [rhoParameters_g₂_apply]
  change Torus x.1 ≃ₜ Torus (transformTwo x.1)
  exact generatorTwoTorusHomeomorph x.1 x.tau_ne_zero

/-- The torus homeomorphism over the cusp generator `g₀`. -/
@[expose] public def rhoGZeroTorusHomeomorph (x : PeriodDomain) :
    Torus x.1 ≃ₜ Torus (rhoParameters g₀ x).1 := by
  rw [rhoParameters_g₀_apply]
  change Torus x.1 ≃ₜ Torus (transformCusp x.1)
  exact cuspTorusHomeomorph x.1

/-- A smooth lift of a map between period quotients makes its descended map smooth. -/
public theorem quotientMap_contMDiff_of_contMDiff_lift
    (x y : Parameters) (n : WithTop ℕ∞)
    [ProperlyDiscontinuousSMul (PeriodGroup x) ComplexTwoSpace]
    [ProperlyDiscontinuousSMul (PeriodGroup y) ComplexTwoSpace]
    [IsManifold (modelWithCornersSelf ℂ ComplexTwoSpace) n (Torus x)]
    [IsManifold (modelWithCornersSelf ℂ ComplexTwoSpace) n (Torus y)]
    (e : ComplexTwoSpace → ComplexTwoSpace)
    (he : ContMDiff (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n e)
    (F : Torus x → Torus y)
    (hF : ∀ z, F (Quotient.mk _ z) = Quotient.mk _ (e z)) :
    ContMDiff (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n F := by
  intro q
  induction q using Quotient.inductionOn with
  | _ z =>
    let px : ComplexTwoSpace → Torus x := quotientProjection
    let py : ComplexTwoSpace → Torus y := quotientProjection
    have hpx : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace)
        (modelWithCornersSelf ℂ ComplexTwoSpace) n px :=
      quotientProjection_isLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace) n
        (fun g ↦ periodTranslation_contMDiff x g n)
    have hpy : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace)
        (modelWithCornersSelf ℂ ComplexTwoSpace) n py :=
      quotientProjection_isLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace) n
        (fun g ↦ periodTranslation_contMDiff y g n)
    let s := (hpx z).localInverse
    have hs : ContMDiffAt (modelWithCornersSelf ℂ ComplexTwoSpace)
        (modelWithCornersSelf ℂ ComplexTwoSpace) n s (px z) :=
      (hpx z).localInverse_contMDiffAt
    have hes : ContMDiffAt (modelWithCornersSelf ℂ ComplexTwoSpace)
        (modelWithCornersSelf ℂ ComplexTwoSpace) n (e ∘ s) (px z) :=
      he.contMDiffAt.comp (px z) hs
    have hsz : s (px z) = z :=
      (hpx z).localInverse_left_inv (hpx z).localInverse_mem_target
    have hrhs : ContMDiffAt (modelWithCornersSelf ℂ ComplexTwoSpace)
        (modelWithCornersSelf ℂ ComplexTwoSpace) n (py ∘ e ∘ s) (px z) :=
      (hpy (e z)).contMDiffAt.comp_of_eq hes (by simp [hsz])
    have hright := (hpx z).localInverse_eventuallyEq_right
    have hevent : Filter.EventuallyEq (nhds (px z)) F (py ∘ e ∘ s) := by
      filter_upwards [hright] with q hq
      calc
        F q = F (px (s q)) := congrArg F hq.symm
        _ = py (e (s q)) := hF (s q)
    exact hrhs.congr_of_eventuallyEq hevent

/-- A homeomorphism of period quotients whose lift and inverse lift are smooth is a local
diffeomorphism. -/
public theorem quotientHomeomorph_isLocalDiffeomorph_of_contMDiff_lifts
    (x y : Parameters) (hx : FullRank x) (hy : FullRank y) (n : WithTop ℕ∞)
    (e : ComplexTwoSpace ≃ₜ ComplexTwoSpace)
    (he : ContMDiff (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n e)
    (heinv : ContMDiff (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n e.symm)
    (F : Torus x ≃ₜ Torus y)
    (hF : ∀ z, F (Quotient.mk _ z) = Quotient.mk _ (e z))
    (hFinv : ∀ z, F.symm (Quotient.mk _ z) = Quotient.mk _ (e.symm z)) :
    letI := periodLattice_properlyDiscontinuousSMul hx
    letI := periodLattice_properlyDiscontinuousSMul hy
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n F := by
  let hproperX : ProperlyDiscontinuousSMul (PeriodGroup x) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hx
  let hproperY : ProperlyDiscontinuousSMul (PeriodGroup y) ComplexTwoSpace :=
    periodLattice_properlyDiscontinuousSMul hy
  have hmx := (torus_isManifold_and_projection_isLocalDiffeomorph x hx n).1
  have hmy := (torus_isManifold_and_projection_isLocalDiffeomorph y hy n).1
  let hmanifoldX : IsManifold (modelWithCornersSelf ℂ ComplexTwoSpace) n (Torus x) := hmx
  let hmanifoldY : IsManifold (modelWithCornersSelf ℂ ComplexTwoSpace) n (Torus y) := hmy
  let D : Torus x ≃ₘ^n⟮(modelWithCornersSelf ℂ ComplexTwoSpace),
      (modelWithCornersSelf ℂ ComplexTwoSpace)⟯ Torus y :=
    { toEquiv := F.toEquiv
      contMDiff_toFun := quotientMap_contMDiff_of_contMDiff_lift x y n e he F hF
      contMDiff_invFun :=
        quotientMap_contMDiff_of_contMDiff_lift y x n e.symm heinv F.symm hFinv }
  exact D.isLocalDiffeomorph

/-- The first generator's descended torus homeomorphism is a local complex diffeomorphism. -/
public theorem generatorOneTorusHomeomorph_isLocalDiffeomorph
    (x : PeriodDomain) (n : WithTop ℕ∞) :
    let hx := FullRank.ofSetupInequalities x.1 x.2
    let hy := FullRank.ofSetupInequalities (transformOne x.1)
      (setupInequalities_transformOne x.1 x.2)
    letI := periodLattice_properlyDiscontinuousSMul hx
    letI := periodLattice_properlyDiscontinuousSMul hy
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n
      (generatorOneTorusHomeomorph x.1 x.tau_ne_zero) := by
  let e := (rightOneContinuousLinearEquiv x.1 x.tau_ne_zero).toHomeomorph
  let F := generatorOneTorusHomeomorph x.1 x.tau_ne_zero
  apply quotientHomeomorph_isLocalDiffeomorph_of_contMDiff_lifts x.1 (transformOne x.1)
    (FullRank.ofSetupInequalities x.1 x.2)
    (FullRank.ofSetupInequalities (transformOne x.1)
      (setupInequalities_transformOne x.1 x.2)) n e
  · exact (rightOneContinuousLinearEquiv x.1 x.tau_ne_zero).contDiff.contMDiff
  · exact (rightOneContinuousLinearEquiv x.1 x.tau_ne_zero).symm.contDiff.contMDiff
  · exact generatorOneTorusHomeomorph_mk x.1 x.tau_ne_zero
  · intro z
    apply F.injective
    rw [F.apply_symm_apply]
    rw [generatorOneTorusHomeomorph_mk]
    congr 1
    exact (e.apply_symm_apply z).symm

/-- The second generator's descended torus homeomorphism is a local complex diffeomorphism. -/
public theorem generatorTwoTorusHomeomorph_isLocalDiffeomorph
    (x : PeriodDomain) (n : WithTop ℕ∞) :
    let hx := FullRank.ofSetupInequalities x.1 x.2
    let hy := FullRank.ofSetupInequalities (transformTwo x.1)
      (setupInequalities_transformTwo x.1 x.2)
    letI := periodLattice_properlyDiscontinuousSMul hx
    letI := periodLattice_properlyDiscontinuousSMul hy
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n
      (generatorTwoTorusHomeomorph x.1 x.tau_ne_zero) := by
  let e := (rightTwoContinuousLinearEquiv x.1 x.tau_ne_zero).toHomeomorph
  let F := generatorTwoTorusHomeomorph x.1 x.tau_ne_zero
  apply quotientHomeomorph_isLocalDiffeomorph_of_contMDiff_lifts x.1 (transformTwo x.1)
    (FullRank.ofSetupInequalities x.1 x.2)
    (FullRank.ofSetupInequalities (transformTwo x.1)
      (setupInequalities_transformTwo x.1 x.2)) n e
  · exact (rightTwoContinuousLinearEquiv x.1 x.tau_ne_zero).contDiff.contMDiff
  · exact (rightTwoContinuousLinearEquiv x.1 x.tau_ne_zero).symm.contDiff.contMDiff
  · exact generatorTwoTorusHomeomorph_mk x.1 x.tau_ne_zero
  · intro z
    apply F.injective
    rw [F.apply_symm_apply]
    rw [generatorTwoTorusHomeomorph_mk]
    congr 1
    exact (e.apply_symm_apply z).symm

/-- The cusp generator's descended torus homeomorphism is a local complex diffeomorphism. -/
public theorem cuspTorusHomeomorph_isLocalDiffeomorph
    (x : PeriodDomain) (n : WithTop ℕ∞) :
    let hx := FullRank.ofSetupInequalities x.1 x.2
    let hy := FullRank.ofSetupInequalities (transformCusp x.1)
      (setupInequalities_transformCusp x.1 x.2)
    letI := periodLattice_properlyDiscontinuousSMul hx
    letI := periodLattice_properlyDiscontinuousSMul hy
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexTwoSpace)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n (cuspTorusHomeomorph x.1) := by
  let e := Homeomorph.refl ComplexTwoSpace
  let F := cuspTorusHomeomorph x.1
  apply quotientHomeomorph_isLocalDiffeomorph_of_contMDiff_lifts x.1 (transformCusp x.1)
    (FullRank.ofSetupInequalities x.1 x.2)
    (FullRank.ofSetupInequalities (transformCusp x.1)
      (setupInequalities_transformCusp x.1 x.2)) n e contMDiff_id contMDiff_id
  · exact cuspTorusHomeomorph_mk x.1
  · intro z
    apply F.injective
    rw [F.apply_symm_apply]
    rw [cuspTorusHomeomorph_mk]
    rfl

end

end SphereSixComplex.Geometry.FamilyEquivariance
