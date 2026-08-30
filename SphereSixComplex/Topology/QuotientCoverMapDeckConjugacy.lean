module

public import SphereSixComplex.Topology.EstablishedAffineVanKampen

/-!
# Conjugacy of deck maps induced by different lifts

Two equivariant lifts of the same map between quotient-cover bases differ by one target deck
transformation.  Their induced deck homomorphisms are therefore conjugate by that same element.
-/

@[expose] public section

noncomputable section

open Topology

namespace SphereSixComplex

variable {E E' X X' G H : Type*}
variable [TopologicalSpace E] [TopologicalSpace E'] [TopologicalSpace X] [TopologicalSpace X']
variable [Group G] [Group H] [MulAction G E] [MulAction H E']
variable {p : C(E, X)} {q : C(E', X')}

/-- Two lifts of the same base map which agree up to one deck transformation at a point agree
up to that deck transformation everywhere. -/
public theorem QuotientCoverMapData.lift_eq_smul_of_baseMap_eq
    [PathConnectedSpace E]
    (hq : IsQuotientCoveringMap q H)
    (D₁ D₂ : QuotientCoverMapData (G := G) (H := H) p q)
    (hbase : D₁.baseMap = D₂.baseMap) (e : E) (c : H)
    (he : D₂.lift e = c • D₁.lift e) :
    D₂.lift = ⟨fun z ↦ c • D₁.lift z,
      hq.continuous_const_smul c |>.comp D₁.lift.continuous⟩ := by
  have hcomp : q ∘ D₂.lift = q ∘ (fun z ↦ c • D₁.lift z) := by
    funext z
    change q (D₂.lift z) = q (c • D₁.lift z)
    rw [hq.map_smul, ← D₂.commutes, ← D₁.commutes, hbase]
  have hfun : (D₂.lift : E → E') = fun z ↦ c • D₁.lift z :=
    hq.isCoveringMap.eq_of_comp_eq D₂.lift.continuous
      (hq.continuous_const_smul c |>.comp D₁.lift.continuous)
      hcomp e he
  apply ContinuousMap.ext
  exact congrFun hfun

/-- Changing the selected lift conjugates the entire induced deck homomorphism by the deck
transformation relating the two selected lifts. -/
public theorem QuotientCoverMapData.deckMap_eq_conj_of_baseMap_eq
    [PathConnectedSpace E]
    (hq : IsQuotientCoveringMap q H)
    (D₁ D₂ : QuotientCoverMapData (G := G) (H := H) p q)
    (hbase : D₁.baseMap = D₂.baseMap) (e : E) (c : H)
    (he : D₂.lift e = c • D₁.lift e) (g : G) :
    D₂.deckMap g = c * D₁.deckMap g * c⁻¹ := by
  letI := hq.isCancelSMul
  have hlift := D₁.lift_eq_smul_of_baseMap_eq hq D₂ hbase e c he
  have hz := ContinuousMap.congr_fun hlift (g • e)
  change D₂.lift (g • e) = c • D₁.lift (g • e) at hz
  rw [D₂.equivariant, D₁.equivariant] at hz
  rw [he, smul_smul, smul_smul] at hz
  have hmul : D₂.deckMap g * c = c * D₁.deckMap g :=
    IsCancelSMul.right_cancel _ _ (D₁.lift e) hz
  exact (eq_mul_inv_iff_mul_eq).2 hmul

/-- In particular, the images of any ordered pair of source deck transformations differ by one
common conjugating element. -/
public theorem QuotientCoverMapData.deckPair_eq_conj_of_baseMap_eq
    [PathConnectedSpace E]
    (hq : IsQuotientCoveringMap q H)
    (D₁ D₂ : QuotientCoverMapData (G := G) (H := H) p q)
    (hbase : D₁.baseMap = D₂.baseMap) (e : E) (c : H)
    (he : D₂.lift e = c • D₁.lift e) (g₁ g₂ : G) :
    D₂.deckMap g₁ = c * D₁.deckMap g₁ * c⁻¹ ∧
      D₂.deckMap g₂ = c * D₁.deckMap g₂ * c⁻¹ :=
  ⟨D₁.deckMap_eq_conj_of_baseMap_eq hq D₂ hbase e c he g₁,
    D₁.deckMap_eq_conj_of_baseMap_eq hq D₂ hbase e c he g₂⟩

/-- Any two equivariant lifts of the same base map induce conjugate deck homomorphisms.  The
conjugating element is the unique target deck transformation carrying one selected lift of the
source basepoint to the other. -/
public theorem QuotientCoverMapData.exists_deckMap_eq_conj_of_baseMap_eq
    [PathConnectedSpace E]
    (hq : IsQuotientCoveringMap q H)
    (D₁ D₂ : QuotientCoverMapData (G := G) (H := H) p q)
    (hbase : D₁.baseMap = D₂.baseMap) (e : E) :
    ∃ c : H, ∀ g : G, D₂.deckMap g = c * D₁.deckMap g * c⁻¹ := by
  have hprojection : q (D₂.lift e) = q (D₁.lift e) := by
    rw [← D₂.commutes, ← D₁.commutes, hbase]
  obtain ⟨c, hc⟩ := hq.apply_eq_iff_mem_orbit.mp hprojection
  refine ⟨c, fun g ↦ D₁.deckMap_eq_conj_of_baseMap_eq hq D₂ hbase e c ?_ g⟩
  exact hc.symm

/-- The images of any two selected source deck transformations therefore differ by a single
common conjugating element. -/
public theorem QuotientCoverMapData.exists_deckPair_eq_conj_of_baseMap_eq
    [PathConnectedSpace E]
    (hq : IsQuotientCoveringMap q H)
    (D₁ D₂ : QuotientCoverMapData (G := G) (H := H) p q)
    (hbase : D₁.baseMap = D₂.baseMap) (e : E) (g₁ g₂ : G) :
    ∃ c : H,
      D₂.deckMap g₁ = c * D₁.deckMap g₁ * c⁻¹ ∧
      D₂.deckMap g₂ = c * D₁.deckMap g₂ * c⁻¹ := by
  obtain ⟨c, hc⟩ := D₁.exists_deckMap_eq_conj_of_baseMap_eq hq D₂ hbase e
  exact ⟨c, hc g₁, hc g₂⟩

end SphereSixComplex

end

end
