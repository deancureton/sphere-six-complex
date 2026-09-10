module

public import Mathlib.Topology.Connected.LocallyConnected
import all Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Covering.Basic
import all Mathlib.Topology.Covering.Basic

@[expose] public section

/-!
# Homogeneous local homeomorphisms are coverings

A separated local homeomorphism need not be a covering: its sheets may escape over a limiting
base point.  The obstruction disappears when a family of fiber-preserving homeomorphisms acts
transitively on every fiber.  One local sheet can then be transported uniformly to every other
sheet.  Connectedness of a sufficiently small base neighbourhood and uniqueness of lifts make
two transported sheets either equal or disjoint.
-/

open Set

noncomputable section

namespace Topology

variable {E X ι : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- A surjective separated local homeomorphism over a locally connected base is a covering when
a family of fiber-preserving homeomorphisms acts transitively on each fiber.

No group laws on the indexing type are needed: the proof only uses the ability to move one point
of a fiber to another. -/
theorem isCoveringMap_of_deck_transitive [LocallyConnectedSpace X]
    (f : E → X) (hloc : IsLocalHomeomorph f) (hsep : IsSeparatedMap f)
    (hsurj : Function.Surjective f) (deck : ι → E ≃ₜ E)
    (hdeck : ∀ i e, f (deck i e) = f e)
    (htrans : ∀ e e', f e = f e' → ∃ i, deck i e = e') :
    IsCoveringMap f := by
  intro x
  obtain ⟨e₀, he₀⟩ := hsurj x
  obtain ⟨φ, he₀φ, hφ⟩ := hloc e₀
  have hxφ : x ∈ φ.target := by
    rw [← φ.image_source_eq_target]
    exact ⟨e₀, he₀φ, by simpa [← hφ] using he₀⟩
  obtain ⟨V, ⟨hVo, hxV, hVc⟩, hVφ⟩ :=
    (LocallyConnectedSpace.open_connected_basis x).mem_iff.mp
      (φ.open_target.mem_nhds hxφ)

  have hbase_section {y : X} (hy : y ∈ V) : f (φ.symm y) = y := by
    rw [hφ]
    exact φ.right_inv (hVφ hy)
  have hφsymm_x : φ.symm x = e₀ := by
    calc
      φ.symm x = φ.symm (φ e₀) := by rw [← hφ, he₀]
      _ = e₀ := φ.left_inv he₀φ

  let fiber := f ⁻¹' ({x} : Set X)
  have he₀fiber : e₀ ∈ fiber := by simpa [fiber] using he₀
  have hmove (e : fiber) : ∃ i, deck i e₀ = e := by
    apply htrans e₀ e
    exact he₀.trans (Set.mem_singleton_iff.mp e.2).symm
  let label (e : fiber) : ι := Classical.choose (hmove e)
  have hlabel (e : fiber) : deck (label e) e₀ = e :=
    Classical.choose_spec (hmove e)

  let liftSection (e : fiber) (y : X) : E := deck (label e) (φ.symm y)
  let sheet (e : fiber) : Set E := liftSection e '' V

  have hφsymm_cont : ContinuousOn (φ.symm : X → E) V :=
    φ.symm.continuousOn.mono hVφ
  have hsection_cont (e : fiber) : ContinuousOn (liftSection e) V := by
    simpa only [liftSection, Function.comp_def] using
      (deck (label e)).continuous.comp_continuousOn hφsymm_cont
  have hsection_base (e : fiber) {y : X} (hy : y ∈ V) :
      f (liftSection e y) = y := by
    change f (deck (label e) (φ.symm y)) = y
    rw [hdeck]
    exact hbase_section hy
  have hsection_x (e : fiber) : liftSection e x = e := by
    change deck (label e) (φ.symm x) = e
    rw [hφsymm_x]
    exact hlabel e

  have hsection_unique (e e' : fiber) {y : X} (hy : y ∈ V)
      (hee' : liftSection e y = liftSection e' y) :
      EqOn (liftSection e) (liftSection e') V := by
    apply hsep.eqOn_of_comp_eqOn hloc.isLocallyInjective hVc.isPreconnected
      (hsection_cont e) (hsection_cont e')
    · intro z hz
      simp only [Function.comp_apply, hsection_base e hz, hsection_base e' hz]
    · exact hy
    · exact hee'

  have hdisjoint : Pairwise (Function.onFun Disjoint sheet) := by
    intro e e' hne
    change Disjoint (sheet e) (sheet e')
    rw [Set.disjoint_left]
    intro q hqe hqe'
    obtain ⟨y, hy, rfl⟩ := hqe
    obtain ⟨y', hy', heq⟩ := hqe'
    have hyy' : y = y' := by
      calc
        y = f (liftSection e y) := (hsection_base e hy).symm
        _ = f (liftSection e' y') := congrArg f heq.symm
        _ = y' := hsection_base e' hy'
    subst y'
    have hall := hsection_unique e e' hy heq.symm
    apply hne
    apply Subtype.ext
    simpa only [hsection_x] using hall hxV

  have hinj (e : fiber) : InjOn f (sheet e) := by
    intro q hq q' hq' hqq'
    obtain ⟨y, hy, rfl⟩ := hq
    obtain ⟨y', hy', rfl⟩ := hq'
    have : y = y' := by
      simpa only [hsection_base e hy, hsection_base e hy'] using hqq'
    subst y'
    rfl

  have honto (e : fiber) : SurjOn f (sheet e) V := by
    intro y hy
    exact ⟨liftSection e y, ⟨y, hy, rfl⟩, hsection_base e hy⟩

  have hexhaustive : f ⁻¹' V ⊆ ⋃ e : fiber, sheet e := by
    intro q hq
    have hbaseq : f (φ.symm (f q)) = f q := hbase_section hq
    obtain ⟨i, hi⟩ := htrans (φ.symm (f q)) q hbaseq
    let e : fiber := ⟨deck i e₀, by
      change f (deck i e₀) ∈ ({x} : Set X)
      rw [hdeck, he₀]
      exact Set.mem_singleton x⟩
    have hraw_x : deck i (φ.symm x) = liftSection e x := by
      rw [hφsymm_x, hsection_x]
    have hraw_cont : ContinuousOn (fun y ↦ deck i (φ.symm y)) V := by
      simpa only [Function.comp_def] using
        (deck i).continuous.comp_continuousOn hφsymm_cont
    have hraw_base : EqOn (f ∘ fun y ↦ deck i (φ.symm y)) id V := by
      intro y hy
      simp only [Function.comp_apply, hdeck, hbase_section hy, id_eq]
    have hsraw : EqOn (liftSection e) (fun y ↦ deck i (φ.symm y)) V := by
      apply hsep.eqOn_of_comp_eqOn hloc.isLocallyInjective hVc.isPreconnected
        (hsection_cont e) hraw_cont
      · intro y hy
        simpa only [Function.comp_apply, hsection_base e hy, id_eq] using (hraw_base hy).symm
      · exact hxV
      · exact hraw_x.symm
    apply Set.mem_iUnion.2
    refine ⟨e, ⟨f q, hq, ?_⟩⟩
    exact (hsraw hq).trans hi

  have hopen_iff (e : fiber) {W : Set X} (hWV : W ⊆ V) :
      IsOpen W ↔ IsOpen (f ⁻¹' W ∩ sheet e) := by
    have heq : f ⁻¹' W ∩ sheet e = liftSection e '' W := by
      ext q
      constructor
      · rintro ⟨hqW, y, hyV, rfl⟩
        refine ⟨y, ?_, rfl⟩
        change f (liftSection e y) ∈ W at hqW
        rwa [hsection_base e hyV] at hqW
      · rintro ⟨y, hyW, rfl⟩
        have hyV := hWV hyW
        refine ⟨?_, ⟨y, hyV, rfl⟩⟩
        change f (liftSection e y) ∈ W
        rwa [hsection_base e hyV]
    rw [heq]
    have himage : liftSection e '' W = deck (label e) '' (φ.symm '' W) := by
      change (fun y ↦ deck (label e) (φ.symm y)) '' W = _
      rw [Set.image_image]
    rw [himage, (deck (label e)).isOpen_image]
    exact (φ.isOpen_symm_image_iff_of_subset_target (hWV.trans hVφ)).symm

  letI : Nonempty E := ⟨e₀⟩
  letI : Nonempty fiber := ⟨⟨e₀, he₀fiber⟩⟩
  letI : DiscreteTopology fiber :=
    (IsDiscrete.of_openPartialHomeomorph f subset_rfl fun e _ ↦ by
      obtain ⟨ψ, heψ, hψ⟩ := hloc e
      exact ⟨ψ, heψ, hψ.symm⟩).1
  let t := hVo.trivializationDiscrete (f := f) sheet V hopen_iff hinj honto
    hdisjoint hexhaustive
  exact IsEvenlyCovered.of_trivialization (f := f) (t := t) hxV


end Topology
