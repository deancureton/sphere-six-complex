module

public import SphereSixComplex.Geometry.Quotient
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Fundamental-group classes from deck paths

For a path-connected space with a group action, a path from a point to one of its deck translates
projects to a based loop in the orbit quotient.  This elementary construction is shared by the
outer triangle-group quotient and the two finite affine elliptic filling quotients.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry

variable {M G : Type*} [TopologicalSpace M] [Group G] [MulAction G M]

/-- Concatenate a continuously chosen path from each point to its image under `f`.  The result
records the lifted path through `n` successive iterates of `f`. -/
public def iteratedForwardPath {X : Type*} [TopologicalSpace X]
    (f : X → X) (step : ∀ x, Path x (f x)) :
    ∀ (n : ℕ) (x : X), Path x (f^[n] x)
  | 0, x => Path.refl x
  | n + 1, x =>
      ((step x).trans (iteratedForwardPath f step n (f x))).cast rfl
        (Function.iterate_succ_apply f n x)

/-- Concatenate one path with its successive images under a continuous self-map.  Unlike
`iteratedForwardPath`, every later segment is the corresponding iterate of the first segment;
this is the lift that represents a power of the projected one-step loop. -/
public def iteratedMappedPath {X : Type*} [TopologicalSpace X]
    (f : X → X) (hf : Continuous f) {x : X}
    (P : Path x (f x)) : ∀ n : ℕ, Path x (f^[n] x)
  | 0 => Path.refl x
  | n + 1 =>
      (iteratedMappedPath f hf P n).trans
        ((P.map (hf.iterate n)).cast rfl (Function.iterate_succ_apply f n x))

/-- A map invariant under one application of `f` is invariant under every iterate of `f`. -/
public theorem map_iterate_eq_of_map_comp_eq {X Y : Type*}
    (f : X → X) (q : X → Y) (hq : ∀ z, q (f z) = q z) (n : ℕ) (z : X) :
    q (f^[n] z) = q z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (f z)).trans (hq z)

/-- Project a path from `x` to `f x` along an `f`-invariant map, obtaining a loop. -/
public def projectedForwardLoop {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (q : X → Y) (hq : ∀ z, q (f z) = q z)
    {x : X} (P : Path x (f x)) (hqcont : Continuous q) : Path (q x) (q x) :=
  (P.map hqcont).cast rfl (hq x).symm

/-- Project the successive images of a path to the invariant target and cast its final endpoint
back to the initial basepoint. -/
public def projectedIteratedMappedLoop {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) : Path (q x) (q x) :=
  ((iteratedMappedPath f hf P n).map hqcont).cast rfl
    (map_iterate_eq_of_map_comp_eq f q hq n x).symm

/-- A literal `n`-fold concatenation of one based loop. -/
public def repeatedLoop {Y : Type*} [TopologicalSpace Y] {y : Y}
    (L : Path y y) : ℕ → Path y y
  | 0 => Path.refl y
  | n + 1 => (repeatedLoop L n).trans L

/-- Regard a based path as its fundamental-group class. -/
public def pathLoopClass {Y : Type*} [TopologicalSpace Y] {y : Y}
    (L : Path y y) : FundamentalGroup Y y :=
  Path.Homotopic.Quotient.mk L

/-- Casting both endpoints of a loop along a point equality is the same as applying the
fundamental-group homomorphism induced by the identity map with that target basepoint. -/
public theorem pathLoopClass_cast_eq_mapOfEq_id
    {X : Type*} [TopologicalSpace X] {x y : X}
    (L : Path x x) (h : x = y) :
    pathLoopClass (L.cast h.symm h.symm) =
      FundamentalGroup.mapOfEq (ContinuousMap.id X) h (pathLoopClass L) := by
  have hm := FundamentalGroup.mapOfEq_apply (ContinuousMap.id X)
    (show (ContinuousMap.id X) x = y from h) (pathLoopClass L)
  rw [hm]
  rfl

/-- Transporting a local loop back along a path is represented by whiskering the loop with that
path and its reverse. -/
public def whiskeredLoopClass {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) : FundamentalGroup X x :=
  pathLoopClass (W.trans (L.trans W.symm))

/-- If the far endpoint of a whisker is identified with its starting point, Mathlib's reversed
path-composition convention writes geometric whiskering as inverse conjugation.  This is the
conversion needed when a paper presentation uses the usual left-to-right loop convention. -/
public theorem whiskeredLoopClass_eq_conjugate_cast
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) (h : y = x) :
    whiskeredLoopClass W L =
      (pathLoopClass (W.cast rfl h.symm))⁻¹ *
        pathLoopClass (L.cast h.symm h.symm) *
        pathLoopClass (W.cast rfl h.symm) := by
  subst h
  simp only [whiskeredLoopClass, pathLoopClass,
    Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rfl

public theorem fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (L : Path y y) :
    (FundamentalGroup.fundamentalGroupMulEquivOfPath W).symm (pathLoopClass L) =
      whiskeredLoopClass W L := by
  rfl

/-- Basepoint transport preserves a conjugation identity. -/
public theorem whiskeredLoopClass_conjugation
    {X : Type*} [TopologicalSpace X] {x y : X}
    (W : Path x y) (D T T' : Path y y)
    (h : (pathLoopClass D)⁻¹ * pathLoopClass T * pathLoopClass D =
      pathLoopClass T') :
    (whiskeredLoopClass W D)⁻¹ * whiskeredLoopClass W T *
        whiskeredLoopClass W D = whiskeredLoopClass W T' := by
  let e := FundamentalGroup.fundamentalGroupMulEquivOfPath W
  have hm := congrArg e.symm h
  rw [← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W D,
    ← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W T,
    ← fundamentalGroupMulEquivOfPath_symm_apply_eq_whiskeredLoopClass W T']
  simpa only [map_mul, map_inv] using hm

/-- Literal repeated concatenation represents the corresponding group power.  The proof records
the reversal built into Mathlib's categorical convention for fundamental-group multiplication. -/
public theorem pathLoopClass_repeatedLoop {Y : Type*} [TopologicalSpace Y]
    {y : Y} (L : Path y y) (n : ℕ) :
    pathLoopClass (repeatedLoop L n) = pathLoopClass L ^ n := by
  induction n with
  | zero =>
      rw [repeatedLoop.eq_def, pow_zero]
      exact Path.Homotopic.Quotient.mk_refl y
  | succ n ih =>
      rw [repeatedLoop.eq_def, pathLoopClass, Path.Homotopic.Quotient.mk_trans,
        ← pathLoopClass, ih, pow_succ']
      rfl

/-- After projection along an invariant map, the concatenation of the successive images of a
path is literally the repeated projected loop. -/
public theorem projectedIteratedMappedLoop_eq_repeatedLoop
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) :
    projectedIteratedMappedLoop f hf q hq P hqcont n =
      repeatedLoop (projectedForwardLoop f q hq P hqcont) n := by
  induction n with
  | zero =>
      apply Path.ext
      funext t
      rfl
  | succ n ih =>
      apply Path.ext
      funext t
      change q (((iteratedMappedPath f hf P n).trans
          ((P.map (hf.iterate n)).cast rfl
            (Function.iterate_succ_apply f n x))) t) =
        ((repeatedLoop (projectedForwardLoop f q hq P hqcont) n).trans
          (projectedForwardLoop f q hq P hqcont)) t
      rw [Path.trans_apply]
      rw [Path.trans_apply]
      split_ifs with ht
      · exact congrArg
          (fun Q : Path (q x) (q x) =>
            Q ⟨2 * (t : ℝ), by constructor <;> linarith [t.2.1, t.2.2]⟩) ih
      · change q ((f^[n])
            (P ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2]⟩)) =
          q (P ⟨2 * (t : ℝ) - 1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
        rw [map_iterate_eq_of_map_comp_eq f q hq]

/-- The projected successive-image path represents the `n`th power of its projected one-step
loop in the fundamental group. -/
public theorem pathLoopClass_projectedIteratedMappedLoop_eq_pow
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → X) (hf : Continuous f)
    (q : X → Y) (hq : ∀ z, q (f z) = q z) {x : X}
    (P : Path x (f x)) (hqcont : Continuous q) (n : ℕ) :
    pathLoopClass (projectedIteratedMappedLoop f hf q hq P hqcont n) =
      pathLoopClass (projectedForwardLoop f q hq P hqcont) ^ n := by
  rw [projectedIteratedMappedLoop_eq_repeatedLoop]
  exact pathLoopClass_repeatedLoop _ _

/-- A chosen path from a point to one of its translates in a path-connected action space. -/
public def orbitDeckPath [PathConnectedSpace M] (x : M) (g : G) : Path x (g • x) :=
  PathConnectedSpace.somePath _ _

/-- The canonical continuous projection to an orbit quotient. -/
public def orbitQuotientMap : C(M, OrbitQuotient (M := M) (G := G)) :=
  ⟨quotientProjection, continuous_quot_mk⟩

/-- A point and any of its translates have the same orbit-quotient image. -/
public theorem orbitQuotientMap_smul (x : M) (g : G) :
    orbitQuotientMap (G := G) (g • x) = orbitQuotientMap (G := G) x := by
  apply Quotient.sound
  change MulAction.orbitRel G M (g • x) x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨g, rfl⟩

/-- Compose paths carrying `x` to its `g`- and `h`-translates.  The second path is first
translated by `g`, so the endpoint records the product `g * h` rather than merely forgetting the
deck labels after quotienting. -/
public def composedOrbitDeckPath (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    Path x ((g * h) • x) :=
  (Pg.trans (Ph.map hg)).cast rfl (mul_smul g h x)

/-- Project a specified path to a deck translate, rather than using the arbitrary path selected
by `orbitDeckPath`. -/
public def projectedOrbitDeckPath (x : M) (g : G) (Pg : Path x (g • x)) :
    Path (orbitQuotientMap (G := G) x) (orbitQuotientMap (G := G) x) :=
  (Pg.map (orbitQuotientMap (G := G)).continuous).cast rfl
    (orbitQuotientMap_smul x g).symm

/-- Projecting a composed deck path gives the literal concatenation of the two projected loops.
The second upstairs segment was translated by `g`, but orbit projection removes that translate. -/
public theorem projectedOrbitDeckPath_mul_eq
    (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    projectedOrbitDeckPath x (g * h)
        (composedOrbitDeckPath x g h Pg Ph hg) =
      (projectedOrbitDeckPath x g Pg).trans
        (projectedOrbitDeckPath x h Ph) := by
  apply Path.ext
  funext t
  unfold composedOrbitDeckPath projectedOrbitDeckPath
  change orbitQuotientMap (G := G) ((Pg.trans (Ph.map hg)) t) =
    ((projectedOrbitDeckPath x g Pg).trans
      (projectedOrbitDeckPath x h Ph)) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · rfl
  · exact orbitQuotientMap_smul _ _

/-- Deck-path composition is contravariant in the fundamental group.  This theorem records the
precise order reversal: a path labelled `g * h` projects to the class labelled `h` times the class
labelled `g` in Mathlib's fundamental-group multiplication. -/
public theorem projectedOrbitDeckPath_mul
    (x : M) (g h : G)
    (Pg : Path x (g • x)) (Ph : Path x (h • x))
    (hg : Continuous (fun y : M ↦ g • y)) :
    pathLoopClass (projectedOrbitDeckPath x (g * h)
      (composedOrbitDeckPath x g h Pg Ph hg)) =
      pathLoopClass (projectedOrbitDeckPath x h Ph) *
        pathLoopClass (projectedOrbitDeckPath x g Pg) := by
  rw [projectedOrbitDeckPath_mul_eq]
  rfl

/-- Rebase a deck path at `y` along `Q : x → y`.  The return path must be translated by `g`
upstairs; after orbit projection it becomes the ordinary reverse whisker. -/
public def rebasedOrbitDeckPath {x y : M} (g : G)
    (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) : Path x (g • x) :=
  Q.trans (D.trans (Q.symm.map hg))

/-- Projecting the genuinely rebased deck path is literally the usual whiskered loop: the
translated return path has the same orbit projection as the original reverse whisker. -/
public theorem projectedRebasedOrbitDeckPath_eq
    {x y : M} (g : G) (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) :
    projectedOrbitDeckPath x g (rebasedOrbitDeckPath g Q D hg) =
      (Q.map (orbitQuotientMap (G := G)).continuous).trans
        ((projectedOrbitDeckPath y g D).trans
          (Q.map (orbitQuotientMap (G := G)).continuous).symm) := by
  apply Path.ext
  funext t
  unfold projectedOrbitDeckPath rebasedOrbitDeckPath
  change orbitQuotientMap (G := G)
      ((Q.trans (D.trans (Q.symm.map hg))) t) =
    ((Q.map (orbitQuotientMap (G := G)).continuous).trans
      ((projectedOrbitDeckPath y g D).trans
        (Q.map (orbitQuotientMap (G := G)).continuous).symm)) t
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with ht
  · rfl
  · rw [Path.trans_apply, Path.trans_apply]
    split_ifs with hu
    · rfl
    · change orbitQuotientMap (G := G)
          (g • Q.symm ⟨2 * (2 * (t : ℝ) - 1) - 1,
            by constructor <;> linarith [t.2.1, t.2.2]⟩) =
        orbitQuotientMap (G := G)
          (Q.symm ⟨2 * (2 * (t : ℝ) - 1) - 1,
            by constructor <;> linarith [t.2.1, t.2.2]⟩)
      exact orbitQuotientMap_smul _ _

/-- The path equality above, expressed as the corresponding fundamental-group class. -/
public theorem projectedRebasedOrbitDeckPath_class
    {x y : M} (g : G) (Q : Path x y) (D : Path y (g • y))
    (hg : Continuous (fun z : M ↦ g • z)) :
    pathLoopClass (projectedOrbitDeckPath x g
      (rebasedOrbitDeckPath g Q D hg)) =
      whiskeredLoopClass
        (Q.map (orbitQuotientMap (G := G)).continuous)
        (projectedOrbitDeckPath y g D) :=
  congrArg pathLoopClass (projectedRebasedOrbitDeckPath_eq g Q D hg)

/-- Projecting a path to a deck translate gives a based loop in the orbit quotient. -/
public def orbitDeckLoop [PathConnectedSpace M] (x : M) (g : G) :
    Path (orbitQuotientMap (G := G) x) (orbitQuotientMap (G := G) x) :=
  ((orbitDeckPath x g).map (orbitQuotientMap (G := G)).continuous).cast rfl
    (orbitQuotientMap_smul x g).symm

/-- The fundamental-group class represented by a projected deck path. -/
public def orbitDeckClass [PathConnectedSpace M] (x : M) (g : G) :
    FundamentalGroup (OrbitQuotient (M := M) (G := G))
      (orbitQuotientMap (G := G) x) :=
  Path.Homotopic.Quotient.mk (orbitDeckLoop x g)

/-! ## Surjectivity through quotient coverings -/

/-- The full preimage of a subset is invariant under the deck action. -/
@[instance_reducible]
public def quotientCoveringPreimageMulAction {X : Type*} [TopologicalSpace X]
    {f : M → X} (hf : IsQuotientCoveringMap f G) (S : Set X) :
    MulAction G (f ⁻¹' S) :=
  SubMulAction.mulAction
    ⟨f ⁻¹' S, fun g _ h ↦ by simpa only [Set.mem_preimage, hf.map_smul g] using h⟩

/-- A quotient covering restricts over the full preimage of any subset. -/
public theorem IsQuotientCoveringMap.restrictPreimage {X : Type*} [TopologicalSpace X]
    {f : M → X} (hf : IsQuotientCoveringMap f G) (S : Set X) :
    letI := quotientCoveringPreimageMulAction hf S
    IsQuotientCoveringMap (S.restrictPreimage f) G := by
  let _ := quotientCoveringPreimageMulAction hf S
  let _ := hf.toContinuousConstSMul
  have hcoe_smul (g : G) (a : f ⁻¹' S) : ((g • a : f ⁻¹' S) : M) = g • (a : M) := rfl
  have hcont : Continuous (S.restrictPreimage f) :=
    (hf.continuous.comp continuous_subtype_val).subtype_mk _
  have hsurj : Function.Surjective (S.restrictPreimage f) := by
    intro b
    obtain ⟨e, he⟩ := hf.surjective (b : X)
    exact ⟨⟨e, by rw [Set.mem_preimage, he]; exact b.2⟩, Subtype.ext he⟩
  have hopen : IsOpenMap (S.restrictPreimage f) := by
    intro U hU
    rw [isOpen_induced_iff] at hU
    obtain ⟨V, hV, rfl⟩ := hU
    rw [isOpen_induced_iff]
    refine ⟨f '' V, hf.isCoveringMap.isLocalHomeomorph.isOpenMap V hV, ?_⟩
    ext b
    constructor
    · rintro ⟨v, hv, hpv⟩
      exact ⟨⟨v, by rw [Set.mem_preimage, hpv]; exact b.2⟩, hv, Subtype.ext hpv⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(a : M), ha, rfl⟩
  refine
    { toIsQuotientMap := hopen.isQuotientMap hcont hsurj
      continuous_const_smul := fun g ↦
        (((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _)
      apply_eq_iff_mem_orbit := ?_
      disjoint := ?_ }
  · intro a₁ a₂
    constructor
    · intro h
      obtain ⟨g, hg⟩ := hf.apply_eq_iff_mem_orbit.mp (congrArg Subtype.val h)
      exact ⟨g, Subtype.ext hg⟩
    · rintro ⟨g, rfl⟩
      apply Subtype.ext
      exact hf.map_smul g
  · intro a
    obtain ⟨U, hU, hU'⟩ := hf.disjoint (a : M)
    refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, ?_⟩
    rintro g ⟨b, ⟨c, hc, rfl⟩, hb⟩
    exact hU' g ⟨((g • c : f ⁻¹' S) : M), ⟨(c : M), hc, (hcoe_smul g c).symm⟩, hb⟩

/-- Project a chosen path to a deck translate through an arbitrary quotient covering. -/
public def projectedQuotientDeckPath {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (x : M) (g : G) (P : Path x (g • x)) :
    Path (f x) (f x) :=
  (P.map hf.continuous).cast rfl (hf.map_smul g).symm

/-- A projected deck path has the prescribed monodromy label. -/
public theorem fundamentalGroupToMulOpposite_projectedQuotientDeckPath
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) (x : M) (g : G) (P : Path x (g • x)) :
    hf.fundamentalGroupToMulOpposite (⟨x, rfl⟩ : f ⁻¹' {f x})
        (pathLoopClass (projectedQuotientDeckPath hf x g P)) = MulOpposite.op g := by
  rw [hf.fundamentalGroupToMulOpposite_apply_eq_Iff]
  let e : f ⁻¹' {f x} := ⟨x, rfl⟩
  let e' : f ⁻¹' {f x} := ⟨g • x, hf.map_smul g⟩
  have hm : hf.isCoveringMap.monodromy
        (pathLoopClass (projectedQuotientDeckPath hf x g P)) e = e' :=
    hf.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk P) (by rfl)
  exact congrArg Subtype.val hm.symm

/-- Replacing the target base point by a propositionally equal point preserves surjectivity. -/
public theorem fundamentalGroup_map_surjective_of_mapOfEq_surjective
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (hsurj : Function.Surjective (FundamentalGroup.mapOfEq f h)) :
    Function.Surjective (FundamentalGroup.map f x) := by
  intro q
  let q' : FundamentalGroup Y y := Path.Homotopic.Quotient.cast q h.symm h.symm
  obtain ⟨a, ha⟩ := hsurj q'
  refine ⟨a, ?_⟩
  have ha' := congrArg
    (fun z : FundamentalGroup Y y ↦ Path.Homotopic.Quotient.cast z h h) ha
  rw [FundamentalGroup.mapOfEq_apply] at ha'
  simpa [q', Path.Homotopic.Quotient.cast_cast] using ha'

/-- An equivariant map between path-connected quotient coverings inherits surjectivity on
fundamental groups from the map between their covering spaces. -/
public theorem quotientCovering_equivariant_map_fundamentalGroup_surjective
    {MW MV XW XV : Type*} {G : Type*}
    [TopologicalSpace MW] [TopologicalSpace MV] [TopologicalSpace XW] [TopologicalSpace XV]
    [Group G] [MulAction G MW] [MulAction G MV]
    [PathConnectedSpace MW] [PathConnectedSpace MV]
    {fW : MW → XW} {fV : MV → XV}
    (hfW : IsQuotientCoveringMap fW G) (hfV : IsQuotientCoveringMap fV G)
    (sourceMap : C(MW, MV)) (targetMap : C(XW, XV))
    (hcomm : ∀ y, targetMap (fW y) = fV (sourceMap y))
    (hequiv : ∀ (g : G) y, sourceMap (g • y) = g • sourceMap y)
    (x : MW) (hsource : Function.Surjective (FundamentalGroup.map sourceMap x)) :
    Function.Surjective (FundamentalGroup.mapOfEq targetMap (hcomm x)) := by
  let xV : MV := sourceMap x
  let bW : XW := fW x
  let bV : XV := fV xV
  let sourceHom := FundamentalGroup.map sourceMap x
  let targetHom := FundamentalGroup.mapOfEq targetMap (hcomm x)
  let coverHomW := FundamentalGroup.mapOfEq
    (⟨fW, hfW.continuous⟩ : C(MW, XW)) (x := x) (y := bW) rfl
  let coverHomV := FundamentalGroup.mapOfEq
    (⟨fV, hfV.continuous⟩ : C(MV, XV)) (x := xV) (y := bV) rfl
  let deckPathW (g : G) : Path x (g • x) := PathConnectedSpace.somePath x (g • x)
  let deckPathV (g : G) : Path xV (g • xV) :=
    ((deckPathW g).map sourceMap.continuous).cast rfl (hequiv g x).symm
  let deckClassW (g : G) : FundamentalGroup XW bW :=
    pathLoopClass (projectedQuotientDeckPath hfW x g (deckPathW g))
  let deckClassV (g : G) : FundamentalGroup XV bV :=
    pathLoopClass (projectedQuotientDeckPath hfV xV g (deckPathV g))
  have hdeckMap (g : G) : targetHom (deckClassW g) = deckClassV g := by
    dsimp only [targetHom, deckClassW, deckClassV]
    rw [FundamentalGroup.mapOfEq_apply]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    funext t
    exact hcomm (deckPathW g t)
  have hcoverComm (a : FundamentalGroup MW x) :
      targetHom (coverHomW a) = coverHomV (sourceHom a) := by
    induction a using Quotient.ind with
    | _ P =>
        change targetHom (coverHomW (Path.Homotopic.Quotient.mk P)) =
          coverHomV (sourceHom (Path.Homotopic.Quotient.mk P))
        dsimp only [targetHom, coverHomW, coverHomV, sourceHom]
        rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply,
          FundamentalGroup.mapOfEq_apply]
        apply congrArg Path.Homotopic.Quotient.mk
        apply Path.ext
        funext t
        exact hcomm (P t)
  intro q
  let eV : fV ⁻¹' {bV} := ⟨xV, rfl⟩
  let monV := hfV.fundamentalGroupToMulOpposite eV
  let g : G := (monV q).unop
  have hmon : monV (deckClassV g) = monV q := by
    have h := fundamentalGroupToMulOpposite_projectedQuotientDeckPath
      hfV xV g (deckPathV g)
    simpa only [monV, deckClassV, g, MulOpposite.op_unop] using h
  have hk : q * (deckClassV g)⁻¹ ∈ monV.ker := by
    change monV (q * (deckClassV g)⁻¹) = 1
    rw [map_mul, map_inv, hmon, mul_inv_cancel]
  have hker : monV.ker = coverHomV.range := by
    dsimp only [monV, coverHomV, eV]
    rw [hfV.ker_fundamentalGroupToMulOpposite ⟨xV, rfl⟩,
      hfV.ker_monodromyPerm ⟨xV, rfl⟩]
  have hrange : q * (deckClassV g)⁻¹ ∈ coverHomV.range := by
    rw [← hker]
    exact hk
  obtain ⟨aV, haV⟩ := hrange
  obtain ⟨aW, haW⟩ := hsource aV
  refine ⟨coverHomW aW * deckClassW g, ?_⟩
  rw [map_mul, hcoverComm, haW, haV, hdeckMap]
  change q * (deckClassV g)⁻¹ * deckClassV g = q
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Surjectivity on fundamental groups passes from an inclusion of covering spaces to the
corresponding inclusion of quotient-covering targets. -/
public theorem quotientCovering_restrict_inclusion_fundamentalGroup_surjective
    {X : Type*} [TopologicalSpace X] {f : M → X}
    (hf : IsQuotientCoveringMap f G) {W V : Set X} (hWV : W ⊆ V)
    (x : M) (hxW : f x ∈ W) [PathConnectedSpace (f ⁻¹' W)]
    [PathConnectedSpace (f ⁻¹' V)]
    (hsource : Function.Surjective
      (FundamentalGroup.map
        (⟨fun z : f ⁻¹' W ↦ ⟨z.1, hWV z.2⟩,
          Continuous.subtype_mk continuous_subtype_val _⟩ : C(f ⁻¹' W, f ⁻¹' V))
        (⟨x, hxW⟩ : f ⁻¹' W))) :
    Function.Surjective
      (FundamentalGroup.map
        (⟨fun z : W ↦ ⟨z.1, hWV z.2⟩,
          Continuous.subtype_mk continuous_subtype_val _⟩ : C(W, V))
        (⟨f x, hxW⟩ : W)) := by
  let _ := quotientCoveringPreimageMulAction hf W
  let _ := quotientCoveringPreimageMulAction hf V
  let fW : f ⁻¹' W → W := W.restrictPreimage f
  let fV : f ⁻¹' V → V := V.restrictPreimage f
  let sourceMap : C(f ⁻¹' W, f ⁻¹' V) :=
    ⟨fun z ↦ ⟨z.1, hWV z.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩
  let targetMap : C(W, V) :=
    ⟨fun z ↦ ⟨z.1, hWV z.2⟩, Continuous.subtype_mk continuous_subtype_val _⟩
  let xW : f ⁻¹' W := ⟨x, hxW⟩
  have hcomm (z : f ⁻¹' W) : targetMap (fW z) = fV (sourceMap z) := rfl
  have hequiv (g : G) (z : f ⁻¹' W) : sourceMap (g • z) = g • sourceMap z := rfl
  have hmapOfEq := quotientCovering_equivariant_map_fundamentalGroup_surjective
    (SphereSixComplex.Geometry.IsQuotientCoveringMap.restrictPreimage hf W)
    (SphereSixComplex.Geometry.IsQuotientCoveringMap.restrictPreimage hf V)
    sourceMap targetMap hcomm hequiv xW
    (by simpa only [sourceMap, xW] using hsource)
  exact fundamentalGroup_map_surjective_of_mapOfEq_surjective
    targetMap (fW xW) (fV (sourceMap xW)) (hcomm xW) hmapOfEq

end SphereSixComplex.Geometry
