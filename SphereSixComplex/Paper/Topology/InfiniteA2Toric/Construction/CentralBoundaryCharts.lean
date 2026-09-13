module

public import SphereSixComplex.Paper.Topology.StandardA2ToricCentralFiberOneCells
import all SphereSixComplex.Paper.Topology.StandardA2ToricCentralFiberOneCells

public import SphereSixComplex.Paper.Topology.StandardA2ToricBoundaryFaceCoverage
public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.SingletonPhaseSurjectivity

public section
noncomputable section
open Set Matrix
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
open SphereSixComplex SphereSixComplex.Periods
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspCombinatorics CuspPhaseEstimates

variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def axisPoint (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) (z : ℂ) : actualLocalCuspCentralSubMulAction W := by
  have ht : carrierHeight (inclusion (upper, 0) (singleAxis i z)) = 0 := by
    fin_cases i <;> simp [carrierHeight_inclusion, rawHeight, singleAxis]
  exact ⟨⟨inclusion (upper, 0) (singleAxis i z), by
    change carrierHeight _ ∈ Metric.ball 0 W.localWitness.radius
    rw [ht, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos⟩, ht⟩

def axisOrbit (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) (z : ℂ) : ActualLocalCuspCentralOrbitQuotient W :=
  Quotient.mk _ (axisPoint W upper i z)

theorem axisPoint_support (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) (z : ℂ) (hz : z ≠ 0) :
    componentSupport constructedModel ((axisPoint W upper i z).1.1 : Carrier) =
      (a2Triangle upper 0) '' {j | j ≠ i} := by
  ext v
  change inclusion (upper, 0) (singleAxis i z) ∈ carrierCentralComponent v ↔ _
  rw [singleAxis_component_iff _ _ _ hz]
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨j, hj, he⟩ <;> exact ⟨j, hj, he.symm⟩

theorem axisOrbit_injOn_nonzero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) : Set.InjOn (axisOrbit W upper i) {0}ᶜ := by
  intro z hz w hw h
  have hz' : z ≠ 0 := hz
  have hw' : w ≠ 0 := hw
  let T : Set ToricLattice := (a2Triangle upper 0) '' {j | j ≠ i}
  have hT : T.Finite := Set.toFinite T
  have hn : T.Nonempty := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨_, ⟨j, hj, rfl⟩⟩
  have he := centralOrbitRel_coe_eq_of_same_componentSupport W T hT hn
    (axisPoint W upper i z) (axisPoint W upper i w)
    (axisPoint_support W upper i z hz') (axisPoint_support W upper i w hw')
    (Quotient.exact h)
  have hinj := (inclusion_isOpenEmbedding (upper, 0)).injective he
  simpa [singleAxis] using congrFun hinj i

private theorem singleAxis_zero (i : Fin 3) : singleAxis i 0 = 0 := by
  funext j
  simp [singleAxis]

private theorem singleAxis_first (z : ℂ) : singleAxis 0 z = lowerAxisZero z := by
  funext i
  fin_cases i <;> rfl

private theorem singleAxis_last (z : ℂ) : singleAxis 2 z = upperAxisTwo z := by
  funext i
  fin_cases i <;> rfl

theorem axisPoint_support_ncard
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) (z : ℂ) :
    (componentSupport constructedModel ((axisPoint W upper i z).1.1 : Carrier)).ncard =
      if z = 0 then 3 else 2 := by
  by_cases hz : z = 0
  · subst z
    change (componentSupport constructedModel (inclusion (upper, 0) (singleAxis i 0))).ncard = _
    rw [singleAxis_zero]
    simpa using carrierOrigin_componentSupport_ncard (upper, 0)
  · rw [axisPoint_support W upper i z hz, ite_eq_right hz,
      Set.ncard_image_of_injective _ (a2Triangle_injective_for_origin upper 0)]
    change ({i}ᶜ : Set (Fin 3)).ncard = 2
    rw [Set.ncard_compl]
    simp

theorem axisOrbit_zero
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) :
    axisOrbit W upper i 0 = constructedCentralOriginOrbit W upper := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  change inclusion _ (singleAxis i 0) = inclusion _ 0
  rw [singleAxis_zero]

theorem axisOrbit_eq_zero_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) (z : ℂ) :
    axisOrbit W upper i z = axisOrbit W upper i 0 ↔ z = 0 := by
  constructor
  · intro h
    have hc := centralOrbitRel_componentSupport_ncard_eq W _ _ (Quotient.exact h)
    rw [axisPoint_support_ncard, axisPoint_support_ncard] at hc
    by_contra hz
    simp [hz] at hc
  · rintro rfl; rfl

theorem axisOrbit_injective
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) : Function.Injective (axisOrbit W upper i) := by
  intro z w h
  by_cases hz : z = 0
  · subst z
    exact ((axisOrbit_eq_zero_iff W upper i w).mp h.symm).symm
  by_cases hw : w = 0
  · subst w
    exact (axisOrbit_eq_zero_iff W upper i z).mp h
  exact axisOrbit_injOn_nonzero W upper i hz hw h

theorem lower_upper_axisOrbit_eq_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel) (z w : ℂ) :
    axisOrbit W false 0 z = axisOrbit W true 2 w ↔ z ≠ 0 ∧ w = z⁻¹ := by
  constructor
  · intro h
    have hc := centralOrbitRel_componentSupport_ncard_eq W _ _ (Quotient.exact h)
    rw [axisPoint_support_ncard, axisPoint_support_ncard] at hc
    have hz : z ≠ 0 := by
      intro hz
      have hw : w = 0 := by
        by_contra hw
        simp [hz, hw] at hc
      subst z; subst w
      rw [axisOrbit_zero, axisOrbit_zero] at h
      exact constructedCentralOriginOrbit_ne W h
    have hw : w ≠ 0 := by intro hw; simp [hz, hw] at hc
    have hp : componentSupport constructedModel ((axisPoint W false 0 z).1.1 : Carrier) =
        ({e₁, e₂} : Set ToricLattice) := by
      ext v
      change inclusion (false, 0) (singleAxis 0 z) ∈ carrierCentralComponent v ↔ _
      rw [singleAxis_first]
      simpa using lowerAxisZero_component_iff z hz v
    have hq : componentSupport constructedModel ((axisPoint W true 2 w).1.1 : Carrier) =
        ({e₁, e₂} : Set ToricLattice) := by
      ext v
      change inclusion (true, 0) (singleAxis 2 w) ∈ carrierCentralComponent v ↔ _
      rw [singleAxis_last]
      simpa using upperAxisTwo_component_iff w hw v
    have he := centralOrbitRel_coe_eq_of_same_componentSupport W _
      (by simp) (by simp) _ _ hp hq (Quotient.exact h)
    change inclusion (false, 0) (singleAxis 0 z) = inclusion (true, 0) (singleAxis 2 w) at he
    rw [singleAxis_first, singleAxis_last] at he
    exact (inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 z w).mp he
  · rintro ⟨hz, rfl⟩
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    apply Subtype.ext
    change inclusion (false, 0) (singleAxis 0 z) = inclusion (true, 0) (singleAxis 2 z⁻¹)
    rw [singleAxis_first, singleAxis_last]
    exact inclusion_lowerAxisZero_eq_upperAxisTwo 0 z hz

private theorem toricPair_eq_translate_imp
    {a b c d k : ToricLattice} (hab : a ≠ b)
    (h : ({a, b} : Set ToricLattice) = (fun v ↦ v + k) '' ({c, d} : Set ToricLattice)) :
    (a = c + k ∧ b = d + k) ∨ (a = d + k ∧ b = c + k) := by
  have ha : a ∈ (fun v ↦ v + k) '' ({c, d} : Set ToricLattice) := by
    rw [← h]
    simp
  have hb : b ∈ (fun v ↦ v + k) '' ({c, d} : Set ToricLattice) := by
    rw [← h]
    simp
  obtain ⟨u, hu, hua⟩ := ha
  obtain ⟨v, hv, hvb⟩ := hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (hab (hua.symm.trans hvb)).elim
  · exact Or.inl ⟨hua.symm, hvb.symm⟩
  · exact Or.inr ⟨hua.symm, hvb.symm⟩
  · exact (hab (hua.symm.trans hvb)).elim

private theorem edgeSupportZero_ne_translate_one (k : ToricLattice) :
    ({e₁, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₂} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := e₁) (b := e₂) (c := 0) (d := e₂)
      (by simp [e₁, e₂]) h with hcase | hcase
  · have h00 := congrFun hcase.1 0
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h10
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h01 h10
    omega

private theorem edgeSupportZero_ne_translate_two (k : ToricLattice) :
    ({e₁, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₁} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := e₁) (b := e₂) (c := 0) (d := e₁)
      (by simp [e₁, e₂]) h with hcase | hcase
  · have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h01 h11
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h00 h01 h11
    omega

private theorem edgeSupportOne_ne_translate_two (k : ToricLattice) :
    ({0, e₂} : Set ToricLattice) ≠
      (fun v ↦ v + k) '' ({0, e₁} : Set ToricLattice) := by
  intro h
  rcases toricPair_eq_translate_imp (a := 0) (b := e₂) (c := 0) (d := e₁)
      (by
        intro heq
        have hcoord := congrFun heq 1
        simp [e₂] at hcoord) h with hcase | hcase
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h11 := congrFun hcase.2 1
    simp [e₁, e₂] at h00 h01 h11
    omega
  · have h00 := congrFun hcase.1 0
    have h01 := congrFun hcase.1 1
    have h10 := congrFun hcase.2 0
    simp [e₁, e₂] at h00 h01 h10
    omega


private def lowerSupport (i : Fin 3) : Set ToricLattice :=
  ![{e₁, e₂}, {0, e₂}, {0, e₁}] i

private theorem lowerSupport_translate_injective
    (i j : Fin 3) (k : ToricLattice)
    (h : lowerSupport i =
      (fun v ↦ v + k) '' lowerSupport j) : i = j := by
  have hr : lowerSupport j =
      (fun v ↦ v + -k) '' lowerSupport i := by
    rw [h, Set.image_image]
    simp
  fin_cases i <;> fin_cases j
  · rfl
  · exact (edgeSupportZero_ne_translate_one k h).elim
  · exact (edgeSupportZero_ne_translate_two k h).elim
  · exact (edgeSupportZero_ne_translate_one (-k) hr).elim
  · rfl
  · exact (edgeSupportOne_ne_translate_two k h).elim
  · exact (edgeSupportZero_ne_translate_two (-k) hr).elim
  · exact (edgeSupportOne_ne_translate_two (-k) hr).elim
  · rfl


private theorem axisPoint_lower_support
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) (hz : z ≠ 0) :
    componentSupport constructedModel ((axisPoint W false i z).1.1 : Carrier) =
      lowerSupport i := by
  rw [axisPoint_support W false i z hz]
  ext v
  fin_cases i <;>
    simp [lowerSupport, Set.mem_image, Fin.exists_fin_succ, a2Triangle, e₁, e₂, eq_comm]

theorem lower_axisOrbit_eq_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i j : Fin 3) (z w : ℂ) :
    axisOrbit W false i z = axisOrbit W false j w ↔
      (z = 0 ∧ w = 0) ∨ (i = j ∧ z = w) := by
  constructor
  · intro h
    have hc := centralOrbitRel_componentSupport_ncard_eq W _ _ (Quotient.exact h)
    rw [axisPoint_support_ncard, axisPoint_support_ncard] at hc
    by_cases hz : z = 0
    · left
      refine ⟨hz, ?_⟩
      by_contra hw
      simp [hz, hw] at hc
    have hw : w ≠ 0 := by intro hw; simp [hz, hw] at hc
    obtain ⟨lambda, hlambda⟩ :=
      centralOrbitRel_componentSupport_eq_translate W _ _ (Quotient.exact h)
    rw [axisPoint_lower_support W i z hz, axisPoint_lower_support W j w hw] at hlambda
    have hij := lowerSupport_translate_injective i j (shearVector lambda) hlambda
    subst j
    exact Or.inr ⟨rfl, axisOrbit_injective W false i h⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [axisOrbit_zero, axisOrbit_zero]
    · rfl


def upperChart (i : Fin 3) : ChartIndex := (true, ![0, -e₁, -e₂] i)
def upperAxis (i : Fin 3) : Fin 3 := ![2, 1, 0] i

def upperPoint (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) : actualLocalCuspCentralSubMulAction W := by
  have ht : carrierHeight (inclusion (upperChart i) (singleAxis (upperAxis i) z)) = 0 := by
    fin_cases i <;> simp [upperAxis, carrierHeight_inclusion, rawHeight, singleAxis]
  exact ⟨⟨inclusion (upperChart i) (singleAxis (upperAxis i) z), by
    change carrierHeight _ ∈ Metric.ball 0 W.localWitness.radius
    rw [ht, Metric.mem_ball, dist_self]
    exact W.localWitness.radius_pos⟩, ht⟩

def upperOrbit (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) : ActualLocalCuspCentralOrbitQuotient W :=
  Quotient.mk _ (upperPoint W i z)

theorem upperOrbit_zero (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) : upperOrbit W i 0 = constructedCentralOriginOrbit W true := by
  let _ := actualLocalCuspQuotientAction W
  apply Quotient.sound
  change MulAction.orbitRel (Multiplicative ParameterLattice)
    (actualLocalCuspCentralSubMulAction W) (upperPoint W i 0) (constructedCentralOriginPoint W true)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  obtain ⟨lambda, hlambda⟩ := shearVector_surjective (upperChart i).2
  refine ⟨Multiplicative.ofAdd lambda, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (((Multiplicative.ofAdd lambda) • constructedCentralOrigin W true :
    localCarrier constructedModel W.localWitness.radius) : constructedModel.Carrier) = _
  rw [constructedCentralOrigin_smul_coe]
  change inclusion (true, 0 + shearVector lambda) 0 =
    inclusion (upperChart i) (singleAxis (upperAxis i) 0)
  rw [singleAxis_zero, hlambda, zero_add]
  rfl

theorem lower_upper_carrier_eq_iff (i : Fin 3) (z w : ℂ) :
    inclusion (false, 0) (singleAxis i z) =
      inclusion (upperChart i) (singleAxis (upperAxis i) w) ↔ z ≠ 0 ∧ w = z⁻¹ := by
  fin_cases i
  · change inclusion (false, 0) (singleAxis 0 z) =
      inclusion (true, 0) (singleAxis 2 w) ↔ _
    rw [singleAxis_first, singleAxis_last]
    exact inclusion_lowerAxisZero_eq_upperAxisTwo_iff 0 z w
  · exact inclusion_middleAxis_left_iff z w
  · exact inclusion_lowerTwo_upperZero_down_iff z w

theorem upperOrbit_eq_lower_inv
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) (hz : z ≠ 0) :
    upperOrbit W i z = axisOrbit W false i z⁻¹ := by
  symm
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  apply Subtype.ext
  exact (lower_upper_carrier_eq_iff i z⁻¹ z).mpr ⟨inv_ne_zero hz, (inv_inv z).symm⟩

theorem lower_axisOrbit_ne_upper_pole
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) :
    axisOrbit W false i z ≠ constructedCentralOriginOrbit W true := by
  intro h
  by_cases hz : z = 0
  · subst z
    rw [axisOrbit_zero] at h
    exact constructedCentralOriginOrbit_ne W h
  have h' : axisOrbit W false i z = axisOrbit W true 0 0 :=
    h.trans (axisOrbit_zero W true 0).symm
  have hc := centralOrbitRel_componentSupport_ncard_eq W _ _ (Quotient.exact h')
  rw [axisPoint_support_ncard, axisPoint_support_ncard] at hc
  simp [hz] at hc

theorem lower_upperOrbit_eq_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i j : Fin 3) (z w : ℂ) :
    axisOrbit W false i z = upperOrbit W j w ↔ i = j ∧ z ≠ 0 ∧ w = z⁻¹ := by
  by_cases hw : w = 0
  · subst w
    rw [upperOrbit_zero]
    constructor
    · intro h; exact (lower_axisOrbit_ne_upper_pole W i z h).elim
    · rintro ⟨_, hz, h⟩
      exact (inv_ne_zero hz h.symm).elim
  rw [upperOrbit_eq_lower_inv W j w hw, lower_axisOrbit_eq_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨hij, hz⟩)
    · exact (inv_ne_zero hw h).elim
    · refine ⟨hij, ?_, ?_⟩
      · rw [hz]; exact inv_ne_zero hw
      · rw [hz, inv_inv]
  · rintro ⟨hij, hz, rfl⟩
    exact Or.inr ⟨hij, (inv_inv z).symm⟩

theorem upperOrbit_eq_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i j : Fin 3) (z w : ℂ) :
    upperOrbit W i z = upperOrbit W j w ↔
      (z = 0 ∧ w = 0) ∨ (i = j ∧ z = w) := by
  by_cases hz : z = 0
  · subst z
    rw [upperOrbit_zero]
    by_cases hw : w = 0
    · subst w; simp [upperOrbit_zero]
    rw [upperOrbit_eq_lower_inv W j w hw]
    simp only [true_and]
    constructor
    · intro h
      exact (lower_axisOrbit_ne_upper_pole W j w⁻¹ h.symm).elim
    · rintro (h | ⟨_, h⟩)
      · exact (hw h).elim
      · exact (hw h.symm).elim
  by_cases hw : w = 0
  · subst w
    rw [upperOrbit_zero, upperOrbit_eq_lower_inv W i z hz]
    constructor
    · intro h; exact (lower_axisOrbit_ne_upper_pole W i z⁻¹ h).elim
    · rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact (hz h).elim
  rw [upperOrbit_eq_lower_inv W i z hz, upperOrbit_eq_lower_inv W j w hw,
    lower_axisOrbit_eq_iff]
  simp [hz, hw, _root_.inv_inj]


theorem not_mem_singletonPhaseImage_iff
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (p : actualLocalCuspCentralSubMulAction W) :
    Quotient.mk _ p ∉ singletonPhaseImage W ↔
      (componentSupport constructedModel (p.1.1 : Carrier)).ncard ≠ 1 := by
  rw [singletonPhaseImage_eq_actualSingletonStratum]
  constructor
  · intro h hc
    exact h ⟨p, rfl, hc⟩
  · intro h ⟨q, hq, hc⟩
    have hn := centralOrbitRel_componentSupport_ncard_eq W _ _ (Quotient.exact hq)
    exact h (hn.symm.trans hc)

theorem axisOrbit_not_mem_singletonPhaseImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) (z : ℂ) :
    axisOrbit W upper i z ∉ singletonPhaseImage W := by
  apply (not_mem_singletonPhaseImage_iff W _).mpr
  rw [axisPoint_support_ncard]
  split <;> omega

theorem upperOrbit_not_mem_singletonPhaseImage
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) (z : ℂ) : upperOrbit W i z ∉ singletonPhaseImage W := by
  by_cases hz : z = 0
  · subst z
    rw [upperOrbit_zero, ← axisOrbit_zero W true 0]
    exact axisOrbit_not_mem_singletonPhaseImage W true 0 0
  rw [upperOrbit_eq_lower_inv W i z hz]
  exact axisOrbit_not_mem_singletonPhaseImage W false i z⁻¹

theorem not_mem_singletonPhaseImage_iff_exists_axis
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (x : ActualLocalCuspCentralOrbitQuotient W) :
    x ∉ singletonPhaseImage W ↔
      ∃ (i : Fin 3) (z : ℂ), x = axisOrbit W false i z ∨ x = upperOrbit W i z := by
  constructor
  · induction x using Quotient.inductionOn with
    | _ p =>
      intro hp
      have hne := (not_mem_singletonPhaseImage_iff W p).mp hp
      have hpos := Set.ncard_pos (componentSupport_finite constructedModel (p.1.1 : Carrier))
        |>.mpr (componentSupport_nonempty_of_t_eq_zero constructedModel p.property)
      have hge : 2 ≤ (componentSupport constructedModel (p.1.1 : Carrier)).ncard := by omega
      obtain ⟨a, z, ha⟩ := inclusion_jointly_surjective (p.1.1 : Carrier)
      have hz : 2 ≤ (componentSupport constructedModel (inclusion a z)).ncard := by
        simpa only [ha] using hge
      obtain ⟨j, hj⟩ := exists_singleAxis_of_componentSupport_ncard_ge_two a z hz
      have hrepr : (p.1.1 : Carrier) = inclusion a (singleAxis j (z j)) := by
        rw [← ha]
        exact congrArg (inclusion a) hj
      cases hb : a.1 with
      | false =>
        obtain ⟨q, w, hq, hw⟩ :=
          exists_actualCentral_deck_translate_singleAxis W p a j (z j) hrepr 0
        refine ⟨j, w, Or.inl ?_⟩
        rw [← hq]
        apply congrArg (Quotient.mk _)
        apply Subtype.ext
        apply Subtype.ext
        change (q.1.1 : Carrier) = inclusion (false, 0) (singleAxis j w)
        simpa only [hb] using hw
      | true =>
        obtain ⟨q, w, hq, hw⟩ := exists_actualCentral_deck_translate_singleAxis
          W p a j (z j) hrepr (upperChart (upperAxis j)).2
        refine ⟨upperAxis j, w, Or.inr ?_⟩
        rw [← hq]
        apply congrArg (Quotient.mk _)
        apply Subtype.ext
        apply Subtype.ext
        change (q.1.1 : Carrier) =
          inclusion (upperChart (upperAxis j)) (singleAxis (upperAxis (upperAxis j)) w)
        rw [hw, hb]
        fin_cases j <;> rfl
  · rintro ⟨i, z, rfl | rfl⟩
    · exact axisOrbit_not_mem_singletonPhaseImage W false i z
    · exact upperOrbit_not_mem_singletonPhaseImage W i z


theorem continuous_axisPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) : Continuous (axisPoint W upper i) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply (inclusion_isOpenEmbedding (upper, 0)).continuous.comp
  apply continuous_pi
  intro j
  by_cases hj : j = i
  · simp only [singleAxis, hj, ite_true]
    fun_prop
  · simp only [singleAxis, hj, ite_false]
    fun_prop

theorem continuous_axisOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (upper : Bool) (i : Fin 3) : Continuous (axisOrbit W upper i) :=
  continuous_quotient_mk'.comp (continuous_axisPoint W upper i)

theorem continuous_upperPoint
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) : Continuous (upperPoint W i) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply (inclusion_isOpenEmbedding (upperChart i)).continuous.comp
  apply continuous_pi
  intro j
  by_cases hj : j = upperAxis i
  · simp only [singleAxis, hj, ite_true]
    fun_prop
  · simp only [singleAxis, hj, ite_false]
    fun_prop

theorem continuous_upperOrbit
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (i : Fin 3) : Continuous (upperOrbit W i) :=
  continuous_quotient_mk'.comp (continuous_upperPoint W i)

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
