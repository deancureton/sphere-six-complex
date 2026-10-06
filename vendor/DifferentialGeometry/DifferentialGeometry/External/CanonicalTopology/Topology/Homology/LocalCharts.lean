module

public import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeHomeomorphism
public import Mathlib.Geometry.Manifold.ChartedSpace

@[expose] public section

/-! # Actual local homology through the same open chart -/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [T1Space X] [T1Space Y]

/-- Restriction to the SAME open source, its original chart homeomorphism,
and inclusion of its SAME open target identify the original local homology. -/
def integralLocalHomologyOpenPartialHomeomorphIso (n : ℕ) (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) : integralLocalHomology n x ≅ integralLocalHomology n (e x) :=
  (integralLocalHomologyNeighborhoodIso n x e.source e.open_source hx).symm ≪≫
    integralLocalHomologyHomeomorphIso n e.toHomeomorphSourceTarget ⟨x, hx⟩ ≪≫
      integralLocalHomologyNeighborhoodIso n (e x) e.target e.open_target (e.map_source hx)

/-- The original manifold chart identifies local singular homology at
the SAME point with local singular homology at its actual chart coordinate. -/
def integralLocalHomologyChartIso [ChartedSpace Y X] (n : ℕ) (x : X) :
    integralLocalHomology n x ≅ integralLocalHomology n (chartAt Y x x) :=
  integralLocalHomologyOpenPartialHomeomorphIso n (chartAt Y x) x (mem_chart_source Y x)

theorem integralLocalHomologyOpenPartialHomeomorphIso_natural (n : ℕ)
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) :
    (integralLocalHomologyNeighborhoodIso n x e.source e.open_source hx).hom ≫
        (integralLocalHomologyOpenPartialHomeomorphIso n e x hx).hom =
      (integralLocalHomologyHomeomorphIso n e.toHomeomorphSourceTarget
        (⟨x, hx⟩ : e.source)).hom ≫
          (integralLocalHomologyNeighborhoodIso n (e x) e.target
            e.open_target (e.map_source hx)).hom := by
  simp [integralLocalHomologyOpenPartialHomeomorphIso]
  rfl

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

theorem integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [T1Space X] [T1Space Y]
    (n : ℕ) (e : OpenPartialHomeomorph X Y) (a : X)
    (U : Set X) (hU : IsOpen U) (haU : a ∈ U) (hUs : U ⊆ e.source) :
    (integralLocalHomologyOpenPartialHomeomorphIso n e a (hUs haU)).hom.hom.comp
        (integralLocalHomologyNeighborhoodIso n a U hU haU).hom.hom =
      integralRelativeHomologyMap n
        (⟨fun x : U => e x, (e.continuousOn.mono hUs).domRestrict⟩ : C(U, Y))
        (show MapsTo (fun x : U => e x)
          ({(⟨a, haU⟩ : U)}ᶜ : Set U) ({e a}ᶜ : Set Y)
          from fun x hx h => hx (Subtype.ext (e.injOn (hUs x.property) (hUs haU) h))) := by
  have ha : a ∈ e.source := hUs haU
  let I := integralLocalHomologyOpenPartialHomeomorphIso n e a ha
  let Js := integralLocalHomologyNeighborhoodIso n a e.source e.open_source ha
  let Jt := integralLocalHomologyNeighborhoodIso n (e a) e.target e.open_target (e.map_source ha)
  let Ju := integralLocalHomologyNeighborhoodIso n a U hU haU
  let q := singularPairRestriction (ContinuousMap.id X) hUs
  have hq : MapsTo q ({(⟨a, haU⟩ : U)}ᶜ : Set U)
      ({(⟨a, ha⟩ : e.source)}ᶜ : Set e.source) := by
    intro x hx h
    change q x = (⟨a, ha⟩ : e.source) at h
    have hval : (x : X) = a := congrArg (fun z : e.source => (z : X)) h
    exact hx (Subtype.ext hval)
  let g : C(e.source, Y) := ⟨fun x => e x, e.continuousOn.domRestrict⟩
  have hg : MapsTo g ({(⟨a, ha⟩ : e.source)}ᶜ : Set e.source) ({e a}ᶜ : Set Y) :=
    fun x hx h => hx (Subtype.ext (e.injOn x.property ha h))
  have hepair : MapsTo e.toHomeomorphSourceTarget
      ({(⟨a, ha⟩ : e.source)}ᶜ : Set e.source)
      ({(⟨e a, e.map_source ha⟩ : e.target)}ᶜ : Set e.target) := by
    intro x hx h
    apply hx
    apply e.toHomeomorphSourceTarget.injective
    exact h
  have hsource : I.hom.hom.comp Js.hom.hom = integralRelativeHomologyMap n g hg := by
    have hnat := congrArg (fun f => f.hom)
      (integralLocalHomologyOpenPartialHomeomorphIso_natural n e a ha)
    change I.hom.hom.comp Js.hom.hom = Jt.hom.hom.comp
      (integralLocalHomologyHomeomorphIso n e.toHomeomorphSourceTarget
        (⟨a, ha⟩ : e.source)).hom.hom at hnat
    rw [hnat]
    change (integralRelativeHomologyMap n (singularSubspaceInclusion e.target)
        (neighborhoodPointComplement_mapsTo (e a) e.target (e.map_source ha))).comp
      (integralRelativeHomologyMap n
        ⟨e.toHomeomorphSourceTarget, e.toHomeomorphSourceTarget.continuous⟩
        hepair) =
      integralRelativeHomologyMap n g hg
    rw [← integralRelativeHomologyMap_comp]
    rfl
  have hnested : Js.hom.hom.comp (integralRelativeHomologyMap n q hq) = Ju.hom.hom :=
    integralLocalHomologyNeighborhoodIso_comp n a U e.source hU e.open_source hUs haU
  change I.hom.hom.comp Ju.hom.hom = _
  rw [← hnested, ← LinearMap.comp_assoc, hsource, ← integralRelativeHomologyMap_comp]
  rfl

theorem integralLocalHomologyOpenPartialHomeomorphIso_trans
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T1Space X] [T1Space Y] [T1Space Z]
    (n : ℕ) (e : OpenPartialHomeomorph X Y) (f : OpenPartialHomeomorph Y Z)
    (a : X) (ha : a ∈ e.source) (hb : e a ∈ f.source) :
    integralLocalHomologyOpenPartialHomeomorphIso n (e.trans f) a ⟨ha, hb⟩ =
      integralLocalHomologyOpenPartialHomeomorphIso n e a ha ≪≫
        integralLocalHomologyOpenPartialHomeomorphIso n f (e a) hb := by
  let U := (e.trans f).source
  have hUa : a ∈ U := ⟨ha, hb⟩
  have hUe : U ⊆ e.source := fun _ hx => hx.1
  let Ju := integralLocalHomologyNeighborhoodIso n a U (e.trans f).open_source hUa
  let Jv := integralLocalHomologyNeighborhoodIso n (e a) f.source f.open_source hb
  let g : C(U, f.source) :=
    ⟨fun x => ⟨e x, x.property.2⟩,
      ((e.continuousOn.mono hUe).domRestrict).subtype_mk _⟩
  have hg : MapsTo g ({(⟨a, hUa⟩ : U)}ᶜ : Set U)
      ({(⟨e a, hb⟩ : f.source)}ᶜ : Set f.source) := by
    intro x hx h
    apply hx
    apply Subtype.ext
    apply e.injOn (hUe x.property) ha
    exact congrArg (fun z : f.source => (z : Y)) h
  have heU :
      (integralLocalHomologyOpenPartialHomeomorphIso n e a ha).hom.hom.comp Ju.hom.hom =
        Jv.hom.hom.comp (integralRelativeHomologyMap n g hg) := by
    rw [integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
      n e a U (e.trans f).open_source hUa hUe]
    change integralRelativeHomologyMap n _ _ =
      (integralRelativeHomologyMap n _ _).comp (integralRelativeHomologyMap n _ _)
    rw [← integralRelativeHomologyMap_comp]
    rfl
  have hcomp :
      (integralLocalHomologyOpenPartialHomeomorphIso n f (e a) hb).hom.hom.comp
          ((integralLocalHomologyOpenPartialHomeomorphIso n e a ha).hom.hom.comp Ju.hom.hom) =
        (integralLocalHomologyOpenPartialHomeomorphIso n (e.trans f) a ⟨ha, hb⟩).hom.hom.comp
          Ju.hom.hom := by
    rw [heU, ← LinearMap.comp_assoc,
      integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
        n f (e a) f.source f.open_source hb Subset.rfl,
      integralLocalHomologyOpenPartialHomeomorphIso_comp_neighborhood
        n (e.trans f) a U (e.trans f).open_source hUa Subset.rfl,
      ← integralRelativeHomologyMap_comp]
    rfl
  apply CategoryTheory.Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hz : Ju.hom.hom (Ju.inv.hom z) = z :=
    congrArg (fun k => k.hom z) Ju.inv_hom_id
  have h := LinearMap.congr_fun hcomp (Ju.inv.hom z)
  change (integralLocalHomologyOpenPartialHomeomorphIso n f (e a) hb).hom.hom
      ((integralLocalHomologyOpenPartialHomeomorphIso n e a ha).hom.hom
        (Ju.hom.hom (Ju.inv.hom z))) =
    (integralLocalHomologyOpenPartialHomeomorphIso n (e.trans f) a ⟨ha, hb⟩).hom.hom
      (Ju.hom.hom (Ju.inv.hom z)) at h
  rw [hz] at h
  change (integralLocalHomologyOpenPartialHomeomorphIso n (e.trans f) a ⟨ha, hb⟩).hom.hom z =
    (integralLocalHomologyOpenPartialHomeomorphIso n f (e a) hb).hom.hom
      ((integralLocalHomologyOpenPartialHomeomorphIso n e a ha).hom.hom z)
  exact h.symm

end DifferentialGeometry.Topology
