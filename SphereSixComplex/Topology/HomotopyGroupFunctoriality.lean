module

public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Functoriality of cube-based higher homotopy groups

Mathlib defines higher homotopy groups using generalized cube loops, but currently provides no
induced-map API above the special comparison with the fundamental group.  This file constructs
postcomposition on generalized loops, proves that it respects relative homotopy and concatenation,
and descends it to a functorial homomorphism on higher homotopy groups.
-/

@[expose] public section

noncomputable section

open ContinuousMap Topology
open Topology.Homotopy
open scoped Topology Topology.Homotopy unitInterval

namespace SphereSixComplex

universe u v w

/-- A continuous map equipped with an equality at the chosen basepoints. -/
public structure BasedContinuousMap
    (X : Type u) (x : X) (Y : Type v) (y : Y)
    [TopologicalSpace X] [TopologicalSpace Y] where
  toContinuousMap : C(X, Y)
  map_base : toContinuousMap x = y

namespace BasedContinuousMap

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y} {z : Z}

@[ext] public theorem ext {f g : BasedContinuousMap X x Y y}
    (h : f.toContinuousMap = g.toContinuousMap) : f = g := by
  cases f
  cases g
  simp_all

/-- Identity based map. -/
public def id (X : Type u) [TopologicalSpace X] (x : X) :
    BasedContinuousMap X x X x where
  toContinuousMap := ContinuousMap.id X
  map_base := rfl

/-- Composition of based maps. -/
public def comp (g : BasedContinuousMap Y y Z z) (f : BasedContinuousMap X x Y y) :
    BasedContinuousMap X x Z z where
  toContinuousMap := g.toContinuousMap.comp f.toContinuousMap
  map_base := by rw [ContinuousMap.comp_apply, f.map_base, g.map_base]

@[simp] public theorem id_toContinuousMap :
    (id X x).toContinuousMap = ContinuousMap.id X :=
  rfl

@[simp] public theorem comp_toContinuousMap
    (g : BasedContinuousMap Y y Z z) (f : BasedContinuousMap X x Y y) :
    (g.comp f).toContinuousMap = g.toContinuousMap.comp f.toContinuousMap :=
  rfl

/-- Postcomposition sends generalized loops to generalized loops. -/
public def mapGenLoop {N : Type*} (f : BasedContinuousMap X x Y y) :
    Ω^ N X x → Ω^ N Y y :=
  fun p ↦ ⟨f.toContinuousMap.comp p.1, by
    intro a ha
    rw [ContinuousMap.comp_apply, p.property a ha, f.map_base]⟩

@[simp] public theorem mapGenLoop_apply {N : Type*}
    (f : BasedContinuousMap X x Y y) (p : Ω^ N X x) (a : I^N) :
    f.mapGenLoop p a = f.toContinuousMap (p a) :=
  rfl

@[simp] public theorem mapGenLoop_const {N : Type*}
    (f : BasedContinuousMap X x Y y) :
    f.mapGenLoop (GenLoop.const : Ω^ N X x) = GenLoop.const := by
  ext a
  exact f.map_base

@[simp] public theorem id_mapGenLoop {N : Type*} (p : Ω^ N X x) :
    (id X x).mapGenLoop p = p := by
  ext a
  rfl

@[simp] public theorem comp_mapGenLoop {N : Type*}
    (g : BasedContinuousMap Y y Z z) (f : BasedContinuousMap X x Y y)
    (p : Ω^ N X x) :
    (g.comp f).mapGenLoop p = g.mapGenLoop (f.mapGenLoop p) := by
  ext a
  rfl

/-- Postcomposition respects homotopy relative to the cube boundary. -/
public theorem mapGenLoop_homotopic {N : Type*}
    (f : BasedContinuousMap X x Y y) {p q : Ω^ N X x}
    (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (f.mapGenLoop p) (f.mapGenLoop q) :=
  h.comp_continuousMap f.toContinuousMap

/-- The induced map on arbitrary-index homotopy groups. -/
public def mapHomotopyGroup {N : Type*} (f : BasedContinuousMap X x Y y) :
    HomotopyGroup N X x → HomotopyGroup N Y y :=
  Quotient.map' f.mapGenLoop (fun _ _ h ↦ f.mapGenLoop_homotopic h)

@[simp] public theorem mapHomotopyGroup_mk {N : Type*}
    (f : BasedContinuousMap X x Y y) (p : Ω^ N X x) :
    f.mapHomotopyGroup (⟦p⟧ : HomotopyGroup N X x) =
      (⟦f.mapGenLoop p⟧ : HomotopyGroup N Y y) :=
  rfl

@[simp] public theorem id_mapHomotopyGroup {N : Type*} :
    (id X x).mapHomotopyGroup (N := N) = _root_.id := by
  funext a
  refine Quotient.inductionOn a ?_
  intro p
  change (⟦(id X x).mapGenLoop p⟧ : HomotopyGroup N X x) = ⟦p⟧
  exact congrArg Quotient.mk' (id_mapGenLoop p)

@[simp] public theorem comp_mapHomotopyGroup {N : Type*}
    (g : BasedContinuousMap Y y Z z) (f : BasedContinuousMap X x Y y) :
    (g.comp f).mapHomotopyGroup (N := N) =
      g.mapHomotopyGroup ∘ f.mapHomotopyGroup := by
  funext a
  refine Quotient.inductionOn a ?_
  intro p
  change (⟦(g.comp f).mapGenLoop p⟧ : HomotopyGroup N Z z) =
    ⟦g.mapGenLoop (f.mapGenLoop p)⟧
  exact congrArg Quotient.mk' (comp_mapGenLoop g f p)

/-- Postcomposition commutes with generalized-loop concatenation. -/
public theorem mapGenLoop_transAt {N : Type*} [DecidableEq N]
    (f : BasedContinuousMap X x Y y) (i : N) (p q : Ω^ N X x) :
    f.mapGenLoop (GenLoop.transAt i p q) =
      GenLoop.transAt i (f.mapGenLoop p) (f.mapGenLoop q) := by
  ext a
  simp only [mapGenLoop_apply, GenLoop.transAt, GenLoop.coe_copy]
  split_ifs <;> rfl

/-- For a nonempty index type, the induced map is a group homomorphism. -/
public def mapHomotopyGroupMonoidHom {N : Type*} [DecidableEq N] [Nonempty N]
    (f : BasedContinuousMap X x Y y) :
    HomotopyGroup N X x →* HomotopyGroup N Y y where
  toFun := f.mapHomotopyGroup
  map_one' := by
    rw [HomotopyGroup.one_def, mapHomotopyGroup_mk, mapGenLoop_const,
      HomotopyGroup.one_def]
  map_mul' a b := by
    let mulX : HomotopyGroup N X x → HomotopyGroup N X x → HomotopyGroup N X x :=
      (· * ·)
    let mulY : HomotopyGroup N Y y → HomotopyGroup N Y y → HomotopyGroup N Y y :=
      (· * ·)
    change f.mapHomotopyGroup (mulX a b) =
      mulY (f.mapHomotopyGroup a) (f.mapHomotopyGroup b)
    refine Quotient.inductionOn₂ a b ?_
    intro p q
    let i := Classical.arbitrary N
    have hmulX : mulX (⟦p⟧ : HomotopyGroup N X x) ⟦q⟧ =
        (⟦GenLoop.transAt i q p⟧ : HomotopyGroup N X x) :=
      HomotopyGroup.mul_spec (i := i)
    have hmulY : mulY
        (⟦f.mapGenLoop p⟧ : HomotopyGroup N Y y) ⟦f.mapGenLoop q⟧ =
        (⟦GenLoop.transAt i (f.mapGenLoop q) (f.mapGenLoop p)⟧ :
          HomotopyGroup N Y y) :=
      HomotopyGroup.mul_spec (i := i)
    rw [hmulX]
    change (⟦f.mapGenLoop (GenLoop.transAt i q p)⟧ : HomotopyGroup N Y y) =
      mulY (⟦f.mapGenLoop p⟧ : HomotopyGroup N Y y) ⟦f.mapGenLoop q⟧
    rw [f.mapGenLoop_transAt i q p]
    exact hmulY.symm

@[simp] public theorem mapHomotopyGroupMonoidHom_apply
    {N : Type*} [DecidableEq N] [Nonempty N]
    (f : BasedContinuousMap X x Y y) (a : HomotopyGroup N X x) :
    f.mapHomotopyGroupMonoidHom a = f.mapHomotopyGroup a :=
  rfl

/-- Identity functoriality at the group-homomorphism level. -/
@[simp] public theorem id_mapHomotopyGroupMonoidHom
    {N : Type*} [DecidableEq N] [Nonempty N] :
    (id X x).mapHomotopyGroupMonoidHom (N := N) = MonoidHom.id _ := by
  ext a
  exact congrFun (id_mapHomotopyGroup (X := X) (x := x) (N := N)) a

/-- Composition functoriality at the group-homomorphism level. -/
@[simp] public theorem comp_mapHomotopyGroupMonoidHom
    {N : Type*} [DecidableEq N] [Nonempty N]
    (g : BasedContinuousMap Y y Z z) (f : BasedContinuousMap X x Y y) :
    (g.comp f).mapHomotopyGroupMonoidHom (N := N) =
      g.mapHomotopyGroupMonoidHom.comp f.mapHomotopyGroupMonoidHom := by
  ext a
  exact congrFun (comp_mapHomotopyGroup (N := N) g f) a

/-- The induced homomorphism on `π₅`. -/
public abbrev mapPiFive (f : BasedContinuousMap X x Y y) :
    π_ 5 X x →* π_ 5 Y y :=
  f.mapHomotopyGroupMonoidHom

end BasedContinuousMap

end SphereSixComplex
