module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryModel
public import SphereSixComplex.Prerequisites.Topology.QuotientHomotopy
public import Mathlib.Topology.Algebra.GroupWithZero

@[expose] public section
noncomputable section
open Set Topology
open scoped OnePoint
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary

/-- The finite-coordinate chart, including the common zero pole. -/
def finitePart : Set Spheres := {x | x ≠ mk 0 ∞}
/-- The reciprocal chart, including the common infinity pole. -/
def reciprocalPart : Set Spheres := {x | x ≠ mk 0 (0 : ℂ)}

theorem mk_mem_finitePart (i : Fin 3) (z : OnePoint ℂ) :
    mk i z ∈ finitePart ↔ z ≠ ∞ := by
  simp [finitePart, mk_eq_mk]
  tauto

theorem mk_mem_reciprocalPart (i : Fin 3) (z : OnePoint ℂ) :
    mk i z ∈ reciprocalPart ↔ z ≠ (0 : ℂ) := by
  simp [reciprocalPart, mk_eq_mk]
  tauto

theorem isQuotientMap_mk : IsQuotientMap (fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) :=
  isQuotientMap_quotient_mk'

theorem isOpen_finitePart : IsOpen finitePart := by
  apply isQuotientMap_mk.isCoinducing.isOpen_preimage.mp
  have he : (fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) ⁻¹' finitePart =
      Prod.snd ⁻¹' ({∞}ᶜ : Set (OnePoint ℂ)) := by
    ext p
    exact mk_mem_finitePart p.1 p.2
  rw [he]
  exact isClosed_singleton.isOpen_compl.preimage continuous_snd

theorem isOpen_reciprocalPart : IsOpen reciprocalPart := by
  apply isQuotientMap_mk.isCoinducing.isOpen_preimage.mp
  have he : (fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) ⁻¹' reciprocalPart =
      Prod.snd ⁻¹' ({((0 : ℂ) : OnePoint ℂ)}ᶜ : Set (OnePoint ℂ)) := by
    ext p
    exact mk_mem_reciprocalPart p.1 p.2
  rw [he]
  exact isClosed_singleton.isOpen_compl.preimage continuous_snd

theorem finitePart_union_reciprocalPart : finitePart ∪ reciprocalPart = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hx : x = mk 0 ∞
  · subst x
    right
    simp [reciprocalPart, mk_eq_mk]
  · exact Or.inl hx

private def finiteCoe (p : Fin 3 × ℂ) : Fin 3 × OnePoint ℂ := (p.1, p.2)

private theorem isEmbedding_finiteCoe : IsEmbedding finiteCoe :=
  IsEmbedding.id.prodMap OnePoint.isOpenEmbedding_coe.isEmbedding

private theorem finiteCoe_range : Set.range finiteCoe =
    (fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) ⁻¹' finitePart := by
  ext p
  rcases p with ⟨i, z⟩
  rw [Set.mem_preimage, mk_mem_finitePart]
  induction z using OnePoint.rec with
  | infty => simp [finiteCoe]
  | coe z =>
    constructor
    · intro _; exact OnePoint.coe_ne_infty z
    · intro _; exact ⟨(i, z), rfl⟩

private def finiteRepresentatives : (Fin 3 × ℂ) ≃ₜ
    ((fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) ⁻¹' finitePart) :=
  isEmbedding_finiteCoe.toHomeomorph.trans (Homeomorph.setCongr finiteCoe_range)

def finiteChart (p : Fin 3 × ℂ) : finitePart :=
  ⟨mk p.1 (p.2 : OnePoint ℂ), (mk_mem_finitePart _ _).mpr (OnePoint.coe_ne_infty p.2)⟩

theorem isQuotientMap_finiteChart : IsQuotientMap finiteChart := by
  have h := (isQuotientMap_mk.restrictPreimage_isOpen isOpen_finitePart).comp
    finiteRepresentatives.isQuotientMap
  exact h

theorem finiteChart_eq_iff (p q : Fin 3 × ℂ) :
    finiteChart p = finiteChart q ↔ p = q ∨ (p.2 = 0 ∧ q.2 = 0) := by
  rw [Subtype.ext_iff]
  change mk _ _ = mk _ _ ↔ _
  rw [mk_eq_mk]
  simp [Prod.ext_iff]

instance : ContractibleSpace finitePart := by
  apply isQuotientMap_finiteChart.contractibleSpace_of_smul (finiteChart (0, 0))
  · intro i
    apply (finiteChart_eq_iff _ _).mpr
    exact Or.inr ⟨rfl, rfl⟩
  · intro t p q h
    rcases (finiteChart_eq_iff p q).mp h with rfl | ⟨hp, hq⟩
    · rfl
    · apply (finiteChart_eq_iff _ _).mpr
      exact Or.inr ⟨by simp [hp], by simp [hq]⟩


private def puncturedCoe (p : Fin 3 × ℂˣ) : Fin 3 × OnePoint ℂ := (p.1, (p.2 : ℂ))

private theorem isEmbedding_puncturedCoe : IsEmbedding puncturedCoe :=
  IsEmbedding.id.prodMap (OnePoint.isOpenEmbedding_coe.isEmbedding.comp Units.isEmbedding_val₀)

private theorem puncturedCoe_range : Set.range puncturedCoe =
    (fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) ⁻¹' (finitePart ∩ reciprocalPart) := by
  ext p
  rcases p with ⟨i, z⟩
  simp only [Set.mem_preimage, Set.mem_inter_iff, mk_mem_finitePart, mk_mem_reciprocalPart]
  induction z using OnePoint.rec with
  | infty => simp [puncturedCoe]
  | coe z =>
    constructor
    · rintro ⟨⟨j, u⟩, h⟩
      have hz : (u : ℂ) = z := OnePoint.coe_eq_coe.mp (congrArg Prod.snd h)
      exact ⟨OnePoint.coe_ne_infty z, by
        rw [← hz]; exact fun h => u.ne_zero (OnePoint.coe_eq_coe.mp h)⟩
    · rintro ⟨_, hz⟩
      have hz' : z ≠ 0 := fun h => hz (by rw [h])
      exact ⟨(i, Units.mk0 z hz'), rfl⟩

private def puncturedRepresentatives : (Fin 3 × ℂˣ) ≃ₜ
    ((fun p : Fin 3 × OnePoint ℂ => mk p.1 p.2) ⁻¹' (finitePart ∩ reciprocalPart)) :=
  isEmbedding_puncturedCoe.toHomeomorph.trans (Homeomorph.setCongr puncturedCoe_range)

def puncturedChart (p : Fin 3 × ℂˣ) : ↥(finitePart ∩ reciprocalPart) :=
  ⟨mk p.1 ((p.2 : ℂ) : OnePoint ℂ),
    (mk_mem_finitePart _ _).mpr (OnePoint.coe_ne_infty _),
    (mk_mem_reciprocalPart _ _).mpr (fun h => p.2.ne_zero (OnePoint.coe_eq_coe.mp h))⟩

theorem isQuotientMap_puncturedChart : IsQuotientMap puncturedChart :=
  (isQuotientMap_mk.restrictPreimage_isOpen
    (isOpen_finitePart.inter isOpen_reciprocalPart)).comp puncturedRepresentatives.isQuotientMap

theorem puncturedChart_injective : Function.Injective puncturedChart := by
  rintro ⟨i, z⟩ ⟨j, w⟩ h
  have he := (mk_eq_mk i j (z : ℂ) (w : ℂ)).mp (congrArg Subtype.val h)
  rcases he with ⟨hij, hzw⟩ | ⟨hz, _⟩ | ⟨hz, _⟩
  · exact Prod.ext hij (Units.ext (OnePoint.coe_eq_coe.mp hzw))
  · exact (z.ne_zero (OnePoint.coe_eq_coe.mp hz)).elim
  · exact (OnePoint.coe_ne_infty _ hz).elim

def overlapHomeomorph : (Fin 3 × ℂˣ) ≃ₜ ↥(finitePart ∩ reciprocalPart) :=
  (Equiv.ofBijective puncturedChart
    ⟨puncturedChart_injective, isQuotientMap_puncturedChart.surjective⟩).toHomeomorphOfContinuousOpen
    isQuotientMap_puncturedChart.continuous
    (isQuotientMap_puncturedChart.isCoinducing.isOpenMap_of_injective puncturedChart_injective)

@[simp] theorem overlapHomeomorph_apply (p : Fin 3 × ℂˣ) :
    (overlapHomeomorph p : Spheres) = mk p.1 ((p.2 : ℂ) : OnePoint ℂ) := rfl


open SphereSixComplex SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

private def upperSphereMap (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) : C(OnePoint ℂ, ActualLocalCuspCentralOrbitQuotient W) :=
  ContinuousMap.onePointOfInv
    ⟨upperOrbit W i, continuous_upperOrbit W i⟩
    ⟨axisOrbit W false i, continuous_axisOrbit W false i⟩
    (fun z hz => upperOrbit_eq_lower_inv W i z hz)

private theorem upperSphereMap_not_mem
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : OnePoint ℂ) : upperSphereMap W i z ∉ singletonPhaseImage W := by
  induction z using OnePoint.rec with
  | infty => exact axisOrbit_not_mem_singletonPhaseImage W false i 0
  | coe z => exact upperOrbit_not_mem_singletonPhaseImage W i z

private def reciprocalRepresentativesMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : Fin 3 × OnePoint ℂ) : Spheres :=
  (homeomorph W).symm ⟨upperSphereMap W p.1 p.2, upperSphereMap_not_mem W p.1 p.2⟩

private theorem homeomorph_reciprocalRepresentativesMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : Fin 3 × OnePoint ℂ) :
    ((homeomorph W (reciprocalRepresentativesMap W p)) : ActualLocalCuspCentralOrbitQuotient W) =
      upperSphereMap W p.1 p.2 := by
  simp [reciprocalRepresentativesMap]

private theorem continuous_reciprocalRepresentativesMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Continuous (reciprocalRepresentativesMap W) :=
  (homeomorph W).symm.continuous.comp
    ((continuous_prod_of_discrete_left.mpr fun i => (upperSphereMap W i).continuous).subtype_mk _)

private theorem reciprocalRepresentativesMap_infty
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    reciprocalRepresentativesMap W (i, ∞) = mk 0 (0 : ℂ) := by
  apply (homeomorph W).injective
  apply Subtype.ext
  rw [homeomorph_reciprocalRepresentativesMap, homeomorph_mk_coe]
  change upperSphereMap W i ∞ = axisOrbit W false 0 0
  change axisOrbit W false i 0 = axisOrbit W false 0 0
  rw [axisOrbit_zero, axisOrbit_zero]

private theorem reciprocalRepresentativesMap_mem
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p : Fin 3 × OnePoint ℂ) :
    reciprocalRepresentativesMap W p ∈ reciprocalPart ↔ p.2 ≠ ∞ := by
  rcases p with ⟨i, z⟩
  induction z using OnePoint.rec with
  | infty => simp [reciprocalRepresentativesMap_infty, reciprocalPart]
  | coe z =>
    refine iff_of_true ?_ (OnePoint.coe_ne_infty z)
    intro h
    have he := congrArg (fun x => ((homeomorph W x) : ActualLocalCuspCentralOrbitQuotient W)) h
    rw [homeomorph_reciprocalRepresentativesMap, homeomorph_mk_coe] at he
    change upperOrbit W i z = axisOrbit W false 0 0 at he
    exact ((lower_upperOrbit_eq_iff W 0 i 0 z).mp he.symm).2.1 rfl

private theorem reciprocalRepresentativesMap_surjective
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    Function.Surjective (reciprocalRepresentativesMap W) := by
  intro x
  induction x using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨i, z⟩
    induction z using OnePoint.rec with
    | infty =>
      refine ⟨(i, (0 : ℂ)), ?_⟩
      apply (homeomorph W).injective
      apply Subtype.ext
      change ((homeomorph W (reciprocalRepresentativesMap W (i, (0 : ℂ)))) :
        ActualLocalCuspCentralOrbitQuotient W) = (homeomorph W (mk i ∞) : _)
      rw [homeomorph_reciprocalRepresentativesMap, homeomorph_mk_infty]
      change upperOrbit W i 0 = _
      exact upperOrbit_zero W i
    | coe z =>
      by_cases hz : z = 0
      · subst z
        exact ⟨(i, ∞), (reciprocalRepresentativesMap_infty W i).trans (mk_zero i).symm⟩
      refine ⟨(i, (z⁻¹ : ℂ)), ?_⟩
      apply (homeomorph W).injective
      apply Subtype.ext
      change ((homeomorph W (reciprocalRepresentativesMap W (i, (z⁻¹ : ℂ)))) :
        ActualLocalCuspCentralOrbitQuotient W) = (homeomorph W (mk i (z : OnePoint ℂ)) : _)
      rw [homeomorph_reciprocalRepresentativesMap, homeomorph_mk_coe]
      change upperOrbit W i z⁻¹ = axisOrbit W false i z
      simpa only [inv_inv] using upperOrbit_eq_lower_inv W i z⁻¹ (inv_ne_zero hz)

private theorem isQuotientMap_reciprocalRepresentativesMap
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsQuotientMap (reciprocalRepresentativesMap W) := by
  let _ := AnalyticData.actualLocalCuspFilling_t2 W
  let _ : T2Space (ActualLocalCuspCentralOrbitQuotient W) :=
    (actualLocalCuspCentralOrbitMap_isEmbedding W).t2Space
  let _ : T2Space Spheres := (homeomorph W).isEmbedding.t2Space
  exact (continuous_reciprocalRepresentativesMap W).isClosedMap.isQuotientMap
    (continuous_reciprocalRepresentativesMap W) (reciprocalRepresentativesMap_surjective W)

private def reciprocalRepresentatives
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    (Fin 3 × ℂ) ≃ₜ ((reciprocalRepresentativesMap W) ⁻¹' reciprocalPart) :=
  finiteRepresentatives.trans (Homeomorph.setCongr (by
    ext p
    exact (mk_mem_finitePart p.1 p.2).trans (reciprocalRepresentativesMap_mem W p).symm))

@[no_expose] def reciprocalChart (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : Fin 3 × ℂ) : reciprocalPart :=
  ⟨reciprocalRepresentativesMap W (p.1, (p.2 : OnePoint ℂ)),
    (reciprocalRepresentativesMap_mem W _).mpr (OnePoint.coe_ne_infty p.2)⟩

theorem homeomorph_reciprocalChart
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) (z : ℂ) :
    ((homeomorph W (reciprocalChart W (i, z))) : ActualLocalCuspCentralOrbitQuotient W) =
      upperOrbit W i z :=
  homeomorph_reciprocalRepresentativesMap W (i, (z : OnePoint ℂ))

@[simp] theorem reciprocalChart_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3) :
    (reciprocalChart W (i, 0) : Spheres) = mk 0 ∞ := by
  apply (homeomorph W).injective
  apply Subtype.ext
  rw [homeomorph_reciprocalChart, homeomorph_mk_infty, upperOrbit_zero]

theorem reciprocalChart_coe_of_ne_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (i : Fin 3)
    (z : ℂ) (hz : z ≠ 0) :
    (reciprocalChart W (i, z) : Spheres) = mk i ((z⁻¹ : ℂ) : OnePoint ℂ) := by
  apply (homeomorph W).injective
  apply Subtype.ext
  rw [homeomorph_reciprocalChart, homeomorph_mk_coe, upperOrbit_eq_lower_inv W i z hz]

theorem isQuotientMap_reciprocalChart
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IsQuotientMap (reciprocalChart W) :=
  ((isQuotientMap_reciprocalRepresentativesMap W).restrictPreimage_isOpen
    isOpen_reciprocalPart).comp (reciprocalRepresentatives W).isQuotientMap

theorem reciprocalChart_eq_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (p q : Fin 3 × ℂ) :
    reciprocalChart W p = reciprocalChart W q ↔ p = q ∨ (p.2 = 0 ∧ q.2 = 0) := by
  rw [Subtype.ext_iff]
  change (homeomorph W).symm _ = (homeomorph W).symm _ ↔ _
  rw [(homeomorph W).symm.injective.eq_iff, Subtype.ext_iff]
  change upperOrbit W p.1 p.2 = upperOrbit W q.1 q.2 ↔ _
  rw [upperOrbit_eq_iff]
  simp only [Prod.ext_iff]
  exact or_comm

theorem contractibleSpace_reciprocalPart
    (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    ContractibleSpace reciprocalPart := by
  apply (isQuotientMap_reciprocalChart W).contractibleSpace_of_smul (reciprocalChart W (0, 0))
  · intro i
    exact (reciprocalChart_eq_iff W _ _).mpr (Or.inr ⟨rfl, rfl⟩)
  · intro t p q h
    rcases (reciprocalChart_eq_iff W p q).mp h with rfl | ⟨hp, hq⟩
    · rfl
    · apply (reciprocalChart_eq_iff W _ _).mpr
      exact Or.inr ⟨by simp [hp], by simp [hq]⟩

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
