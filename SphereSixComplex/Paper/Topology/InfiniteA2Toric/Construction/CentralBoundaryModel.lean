module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryCharts
public import SphereSixComplex.Prerequisites.Topology.OnePointGluing

@[expose] public section
noncomputable section
open Set Topology
open scoped OnePoint
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
open SphereSixComplex SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def sphereMap (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) : C(OnePoint ℂ, ActualLocalCuspCentralOrbitQuotient W) :=
  ContinuousMap.onePointOfInv
    ⟨axisOrbit W false i, continuous_axisOrbit W false i⟩
    ⟨upperOrbit W i, continuous_upperOrbit W i⟩
    (fun z hz => (lower_upperOrbit_eq_iff W i i z z⁻¹).mpr ⟨rfl, hz, rfl⟩)

@[simp] theorem sphereMap_coe (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) : sphereMap W i z = axisOrbit W false i z := rfl

@[simp] theorem sphereMap_infty (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) : sphereMap W i ∞ = constructedCentralOriginOrbit W true :=
  upperOrbit_zero W i

def poleSetoid : Setoid (Fin 3 × OnePoint ℂ) where
  r p q := p = q ∨ (p.2 = (0 : ℂ) ∧ q.2 = (0 : ℂ)) ∨ (p.2 = ∞ ∧ q.2 = ∞)
  iseqv := by
    constructor
    · intro p; exact Or.inl rfl
    · intro p q h; rcases h with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
    · intro p q r h h'
      rcases h with rfl | ⟨hp, hq⟩ | ⟨hp, hq⟩
      · exact h'
      · rcases h' with rfl | ⟨hq', hr⟩ | ⟨hq', hr⟩
        · exact Or.inr (Or.inl ⟨hp, hq⟩)
        · exact Or.inr (Or.inl ⟨hp, hr⟩)
        · exact (OnePoint.coe_ne_infty (0 : ℂ) (hq.symm.trans hq')).elim
      · rcases h' with rfl | ⟨hq', hr⟩ | ⟨hq', hr⟩
        · exact Or.inr (Or.inr ⟨hp, hq⟩)
        · exact (OnePoint.coe_ne_infty (0 : ℂ) (hq'.symm.trans hq)).elim
        · exact Or.inr (Or.inr ⟨hp, hr⟩)

/-- Three complex spheres with their zero poles identified and their infinity poles identified. -/
def Spheres := Quotient poleSetoid

instance : TopologicalSpace Spheres := inferInstanceAs (TopologicalSpace (Quotient poleSetoid))
instance : CompactSpace Spheres := inferInstanceAs (CompactSpace (Quotient poleSetoid))

def mk (i : Fin 3) (z : OnePoint ℂ) : Spheres := Quotient.mk _ (i, z)

theorem continuous_mk : Continuous (fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) :=
  continuous_quotient_mk'

theorem mk_eq_mk (i j : Fin 3) (z w : OnePoint ℂ) :
    mk i z = mk j w ↔
      (i = j ∧ z = w) ∨ (z = (0 : ℂ) ∧ w = (0 : ℂ)) ∨ (z = ∞ ∧ w = ∞) := by
  change Quotient.mk poleSetoid (i, z) = Quotient.mk poleSetoid (j, w) ↔ _
  rw [Quotient.eq]
  change ((i, z) = (j, w) ∨ _) ↔ _
  rw [Prod.mk.injEq]

@[simp] theorem mk_zero (i : Fin 3) : mk i (0 : ℂ) = mk 0 (0 : ℂ) :=
  (mk_eq_mk _ _ _ _).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))

@[simp] theorem mk_infty (i : Fin 3) : mk i ∞ = mk 0 ∞ :=
  (mk_eq_mk _ _ _ _).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem sphereMap_eq_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p q : Fin 3 × OnePoint ℂ) :
    sphereMap W p.1 p.2 = sphereMap W q.1 q.2 ↔ poleSetoid.r p q := by
  change sphereMap W p.1 p.2 = sphereMap W q.1 q.2 ↔
    p = q ∨ (p.2 = (0 : ℂ) ∧ q.2 = (0 : ℂ)) ∨ (p.2 = ∞ ∧ q.2 = ∞)
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => simp
    | coe z =>
      simp [Ne.symm (lower_axisOrbit_ne_upper_pole W j z)]
  | coe z =>
    induction q using OnePoint.rec with
    | infty => simp [lower_axisOrbit_ne_upper_pole W i z]
    | coe w =>
      simp only [sphereMap_coe, lower_axisOrbit_eq_iff,
        Prod.mk.injEq, OnePoint.coe_eq_coe, OnePoint.coe_ne_infty, and_false, or_false]
      exact or_comm

theorem sphereMap_not_mem_singletonPhaseImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : OnePoint ℂ) : sphereMap W i z ∉ singletonPhaseImage W := by
  induction z using OnePoint.rec with
  | infty =>
    rw [sphereMap_infty, ← axisOrbit_zero W true 0]
    exact axisOrbit_not_mem_singletonPhaseImage W true 0 0
  | coe z => exact axisOrbit_not_mem_singletonPhaseImage W false i z

def modelMap (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Spheres → ↥((singletonPhaseImage W)ᶜ) :=
  Quotient.lift
    (fun p => ⟨sphereMap W p.1 p.2, sphereMap_not_mem_singletonPhaseImage W p.1 p.2⟩)
    (fun p q h => Subtype.ext ((sphereMap_eq_iff W p q).mpr h))

theorem continuous_modelMap (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (modelMap W) := by
  apply Continuous.quotient_lift
  apply Continuous.subtype_mk
  exact continuous_prod_of_discrete_left.mpr fun i => (sphereMap W i).continuous

theorem modelMap_bijective (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Function.Bijective (modelMap W) := by
  constructor
  · intro p q h
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        exact Quotient.sound ((sphereMap_eq_iff W p q).mp (congrArg Subtype.val h))
  · rintro ⟨x, hx⟩
    obtain ⟨i, z, hz | hz⟩ := (not_mem_singletonPhaseImage_iff_exists_axis W x).mp hx
    · exact ⟨Quotient.mk _ (i, (z : OnePoint ℂ)), Subtype.ext hz.symm⟩
    · by_cases hz0 : z = 0
      · subst z
        exact ⟨Quotient.mk _ (i, ∞), Subtype.ext (by
          change sphereMap W i ∞ = x
          rw [sphereMap_infty]
          exact (upperOrbit_zero W i).symm.trans hz.symm)⟩
      · refine ⟨Quotient.mk _ (i, (z⁻¹ : ℂ)), Subtype.ext ?_⟩
        exact (upperOrbit_eq_lower_inv W i z hz0).symm.trans hz.symm

/-- The actual nonsingleton central locus is three spheres sharing two poles. -/
def homeomorph (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Spheres ≃ₜ ↥((singletonPhaseImage W)ᶜ) := by
  let _ := AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (modelMap W) (modelMap_bijective W)) (continuous_modelMap W)


@[simp] theorem homeomorph_mk_coe
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) :
    ((homeomorph W (mk i z)) : ActualLocalCuspCentralOrbitQuotient W) =
      axisOrbit W false i z := rfl

@[simp] theorem homeomorph_mk_infty
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) :
    ((homeomorph W (mk i ∞)) : ActualLocalCuspCentralOrbitQuotient W) =
      constructedCentralOriginOrbit W true := sphereMap_infty W i

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
