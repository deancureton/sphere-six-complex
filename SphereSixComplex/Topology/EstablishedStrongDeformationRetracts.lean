module

public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Established strong-deformation-retract principles

This file isolates two standard general-topology results not currently packaged in Mathlib: the
upgrade from a cofibrant homotopy-equivalent inclusion to a strong deformation retract, and the
equivariant lift of such a retraction through a regular covering.  Their hypotheses contain the
full homotopy-extension and quotient-covering data used below.
-/

@[expose] public section

noncomputable section

open Set Topology unitInterval
open scoped ContinuousMap

namespace SphereSixComplex

/-- The continuous inclusion of a subspace. -/
public def topologicalSubsetInclusionMap {X : Type*} [TopologicalSpace X] (A : Set X) : C(A, X) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

/-- The homotopy-extension property for the inclusion `A ⊆ X`. -/
public def HasHomotopyExtensionProperty {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type) (_ : TopologicalSpace Y) (f : C(X, Y)) (g : C(A, Y))
    (h : ContinuousMap.Homotopy (f.comp (topologicalSubsetInclusionMap A)) g),
    ∃ (f₁ : C(X, Y)) (H : ContinuousMap.Homotopy f f₁),
      ∀ s (a : A), H (s, (a : X)) = h (s, a)

/-- The inclusion `A ⊆ X` is a homotopy equivalence, with its inverse map recorded explicitly. -/
public def IsHomotopyEquivalenceInclusion {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ e : X ≃ₕ A, e.invFun = topologicalSubsetInclusionMap A

/-- A non-equivariant strong deformation retraction onto a subspace. -/
public structure StrongDeformationRetraction (X : Type*) [TopologicalSpace X] (A : Set X) where
  retract : C(X, X)
  homotopy : ContinuousMap.Homotopy (ContinuousMap.id X) retract
  retract_mem : ∀ x, retract x ∈ A
  retract_fixed : ∀ x, x ∈ A → retract x = x
  homotopy_fixed : ∀ s x, x ∈ A → homotopy (s, x) = x

/-- The track through `e` of a base homotopy, lifted through a covering. -/
public noncomputable def liftTrack {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) : C(I, E) :=
  cov.liftPath ⟨fun s => R.homotopy (s, p e), by fun_prop⟩ e (by simp)

public theorem liftTrack_lifts {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) (s : I) :
    p (liftTrack cov R e s) = R.homotopy (s, p e) :=
  congrFun (cov.liftPath_lifts ⟨fun s => R.homotopy (s, p e), by fun_prop⟩ e (by simp)) s

public theorem liftTrack_zero {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) : liftTrack cov R e 0 = e :=
  cov.liftPath_zero _ e (by simp)

/-- The lifted homotopy is jointly continuous.  Continuity in each variable separately is what
`liftPath` provides; `IsLocalHomeomorph.continuous_lift` upgrades it. -/
public theorem continuous_liftTrack {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) :
    Continuous (fun z : I × E => liftTrack cov R z.2 z.1) :=
  @IsLocalHomeomorph.continuous_lift E B E _ _ _ (⇑p) cov.isLocalHomeomorph cov.isSeparatedMap
    ⟨fun z : I × E => R.homotopy (z.1, p z.2), by fun_prop⟩
    (fun z => liftTrack cov R z.2 z.1)
    (by funext z; exact liftTrack_lifts cov R z.2 z.1)
    (by simpa only [liftTrack_zero] using continuous_id')
    (fun e => (liftTrack cov R e).continuous)

/-- A deck transformation does not change the image under the covering. -/
public theorem apply_smul_eq {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] {p : C(E, B)} (hp : IsQuotientCoveringMap p G) (g : G) (e : E) :
    p (g • e) = p e :=
  hp.apply_eq_iff_mem_orbit.mpr ⟨g, rfl⟩

/-- Uniqueness of lifts: anything continuous that lifts the same track and starts at `e` is the
lifted track. -/
public theorem liftTrack_eq {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) (e : E) (F : I → E)
    (hcont : Continuous F) (hlift : ∀ s, p (F s) = R.homotopy (s, p e)) (h0 : F 0 = e) :
    ∀ s, F s = liftTrack cov R e s := by
  have hg0 : (⟨fun s => R.homotopy (s, p e), by fun_prop⟩ : C(I, B)) 0 = p e := by simp
  have h := (cov.eq_liftPath_iff hg0 (Γ := F)).mpr ⟨hcont, funext hlift, h0⟩
  exact fun s => congrFun h s

/-- Over the base retract the track is constant, so its lift is too. -/
public theorem liftTrack_fixed {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (cov : IsCoveringMap p) {D : Set B}
    (R : StrongDeformationRetraction B D) {e : E} (he : p e ∈ D) (s : I) :
    liftTrack cov R e s = e :=
  (liftTrack_eq cov R e (fun _ => e) continuous_const
    (fun s => (R.homotopy_fixed s (p e) he).symm) rfl s).symm

/-- The lifted track is equivariant, again by uniqueness of lifts. -/
public theorem liftTrack_smul {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] {p : C(E, B)} (hp : IsQuotientCoveringMap p G) {D : Set B}
    (R : StrongDeformationRetraction B D) (g : G) (e : E) (s : I) :
    liftTrack hp.isCoveringMap R (g • e) s = g • liftTrack hp.isCoveringMap R e s := by
  let _ := hp.toContinuousConstSMul
  refine (liftTrack_eq hp.isCoveringMap R (g • e) (fun s => g • liftTrack hp.isCoveringMap R e s)
    ((continuous_const_smul g).comp (liftTrack hp.isCoveringMap R e).continuous) ?_ ?_ s).symm
  · intro s
    rw [apply_smul_eq hp, liftTrack_lifts, apply_smul_eq hp]
  · rw [liftTrack_zero]

namespace EstablishedGeneralTopology

/-- The inclusion of the base of a relative CW complex has the homotopy-extension property. -/
public axiom hasHomotopyExtensionProperty_of_relativeCWComplex
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hCW : RelCWComplex (Set.univ : Set X) A) :
    HasHomotopyExtensionProperty A

/-- If a regular covering and the full inverse image of a subspace are contractible, their
quotients are `K(G,1)` spaces. For a relative CW pair, the subspace inclusion is therefore a
homotopy equivalence. -/
public axiom isHomotopyEquivalenceInclusion_of_contractible_regularCover
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (hE : ContractibleSpace E) (hA : ContractibleSpace A)
    (hCW : RelCWComplex (Set.univ : Set B) D) :
    IsHomotopyEquivalenceInclusion D

/-- A cofibrant inclusion which is a homotopy equivalence is the inclusion of a strong
deformation retract. This is the standard homotopy-extension-property theorem. -/
public axiom strongDeformationRetraction_of_cofibration_homotopyEquivalence
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hHEP : HasHomotopyExtensionProperty A)
    (hEquiv : IsHomotopyEquivalenceInclusion A) :
    Nonempty (StrongDeformationRetraction X A)

/-- A strong deformation retraction lifts uniquely through a regular quotient covering. The
lift is equivariant under the deck group and retracts onto the full inverse image of the base
retract.

Proved from Mathlib's covering-space lifting API: each track is lifted by
`IsCoveringMap.liftPath`, joint continuity comes from `IsLocalHomeomorph.continuous_lift`, and both
the fixing on the preimage and the equivariance are uniqueness-of-lift arguments
(`IsCoveringMap.eq_liftPath_iff`). -/
public theorem equivariantStrongDeformationRetraction_lift
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (R : StrongDeformationRetraction B D) :
    Nonempty (EquivariantStrongDeformationRetraction G E A) := by
  let _ := hp.toContinuousConstSMul
  have hmemA : ∀ {x : E}, x ∈ A → p x ∈ D := fun {x} hx =>
    Set.mem_preimage.mp (by rw [hpreimage]; exact hx)
  exact ⟨{
    retract :=
      ⟨fun e => liftTrack hp.isCoveringMap R e 1,
        (continuous_liftTrack hp.isCoveringMap R).comp (continuous_const.prodMk continuous_id)⟩
    homotopy :=
      { toFun := fun z => liftTrack hp.isCoveringMap R z.2 z.1
        continuous_toFun := continuous_liftTrack hp.isCoveringMap R
        map_zero_left := fun e => liftTrack_zero hp.isCoveringMap R e
        map_one_left := fun _ => rfl }
    retract_mem := fun x => by
      have hD : p (liftTrack hp.isCoveringMap R x 1) ∈ D := by
        rw [liftTrack_lifts]; simpa using R.retract_mem (p x)
      rw [← hpreimage]; exact Set.mem_preimage.mpr hD
    retract_fixed := fun x hx => liftTrack_fixed hp.isCoveringMap R (hmemA hx) 1
    homotopy_fixed := fun s x hx => liftTrack_fixed hp.isCoveringMap R (hmemA hx) s
    retract_equivariant := fun g x => liftTrack_smul hp R g x 1
    homotopy_equivariant := fun g s x => liftTrack_smul hp R g x s }⟩

end EstablishedGeneralTopology

end SphereSixComplex
