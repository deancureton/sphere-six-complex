module

public import SphereSixComplex.Geometry.Gluing

/-!
# Four-piece star gluings

The completed family is obtained by gluing three pairwise disjoint collars of the regular piece
to collars in the cusp and two elliptic fillings.  This file turns exactly that data into
`TopCat.GlueData`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace SphereSixComplex

/-- A paired collar map has closed ambient range when radial annuli are compact and the central
space separates every point from the collapsing end. -/
public theorem isClosed_range_prod_of_compact_radial_annuli
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space X] [T2Space Y]
    (toCentral : Z → X) (toFilling : Z → Y)
    (sourceRadius : Z → ℝ) (fillingRadius : Y → ℝ) (r : ℝ)
    (hfillingRadius : Continuous fillingRadius)
    (hfillingRadius_nonneg : ∀ y, 0 ≤ fillingRadius y)
    (hfillingRadius_lt : ∀ y, fillingRadius y < r)
    (hradius : ∀ z, fillingRadius (toFilling z) = sourceRadius z)
    (hcompact : ∀ {s t : ℝ}, 0 < s → t < r →
      IsCompact ((fun z => (toCentral z, toFilling z)) ''
        {z | s ≤ sourceRadius z ∧ sourceRadius z ≤ t}))
    (hend : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ s : ℝ, 0 < s ∧ ∀ z, sourceRadius z < s → toCentral z ∉ V) :
    IsClosed (Set.range fun z => (toCentral z, toFilling z)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  have hpnot : p ∉ Set.range (fun z => (toCentral z, toFilling z)) := hp
  rcases (hfillingRadius_nonneg p.2).eq_or_lt with hzero | hpos
  · obtain ⟨V, hVopen, hpV, s, hs, hsV⟩ := hend p.1
    let N : Set Y := {y | fillingRadius y < s}
    have hNopen : IsOpen N := isOpen_lt hfillingRadius continuous_const
    have hpN : p.2 ∈ N := by
      change fillingRadius p.2 < s
      rw [← hzero]
      exact hs
    refine ⟨V ×ˢ N, ?_, hVopen.prod hNopen, ⟨hpV, hpN⟩⟩
    intro w hw
    change w ∉ Set.range (fun z => (toCentral z, toFilling z))
    rintro ⟨z, rfl⟩
    apply hsV z
    · have hzN := hw.2
      change fillingRadius (toFilling z) < s at hzN
      rwa [hradius] at hzN
    · exact hw.1
  · let s := fillingRadius p.2 / 2
    let t := (fillingRadius p.2 + r) / 2
    have hs : 0 < s := by
      dsimp [s]
      linarith
    have hsρ : s < fillingRadius p.2 := by
      dsimp [s]
      linarith
    have hρt : fillingRadius p.2 < t := by
      dsimp [t]
      linarith [hfillingRadius_lt p.2]
    have htr : t < r := by
      dsimp [t]
      linarith [hfillingRadius_lt p.2]
    let N : Set Y := {y | s < fillingRadius y ∧ fillingRadius y < t}
    have hNopen : IsOpen N :=
      (isOpen_lt continuous_const hfillingRadius).inter
        (isOpen_lt hfillingRadius continuous_const)
    have hpN : p.2 ∈ N := ⟨hsρ, hρt⟩
    let K : Set (X × Y) := (fun z => (toCentral z, toFilling z)) ''
      {z | s ≤ sourceRadius z ∧ sourceRadius z ≤ t}
    have hKcompact : IsCompact K := hcompact hs htr
    have hKclosed : IsClosed K := hKcompact.isClosed
    have hpK : p ∉ K := by
      intro h
      obtain ⟨z, _, hz⟩ := h
      exact hpnot ⟨z, hz⟩
    refine ⟨(Set.univ ×ˢ N) ∩ Kᶜ, ?_,
      (isOpen_univ.prod hNopen).inter hKclosed.isOpen_compl,
      ⟨⟨Set.mem_univ _, hpN⟩, hpK⟩⟩
    intro w hw
    change w ∉ Set.range (fun z => (toCentral z, toFilling z))
    rintro ⟨z, rfl⟩
    apply hw.2
    refine ⟨z, ?_, rfl⟩
    have hzN := hw.1.2
    change s < fillingRadius (toFilling z) ∧
      fillingRadius (toFilling z) < t at hzN
    rw [hradius] at hzN
    exact ⟨hzN.1.le, hzN.2.le⟩

/-- A paired collar map has closed ambient range when its filling-side map is an open
embedding, its image is exactly the positive-radius locus, and the central space separates
every point from the collapsing end.  This version handles positive radius by pulling back a
Hausdorff separation through the open embedding, so it needs no compactness of radial
annuli. -/
public theorem isClosed_range_prod_of_openEmbedding_radial_end
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space X]
    (toCentral : Z → X) (toFilling : Z → Y)
    (sourceRadius : Z → ℝ) (fillingRadius : Y → ℝ)
    (hcentral : Continuous toCentral)
    (hfilling : Topology.IsOpenEmbedding toFilling)
    (hfillingRadius : Continuous fillingRadius)
    (hfillingRadius_nonneg : ∀ y, 0 ≤ fillingRadius y)
    (hrange : Set.range toFilling = {y | 0 < fillingRadius y})
    (hradius : ∀ z, fillingRadius (toFilling z) = sourceRadius z)
    (hend : ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∃ s : ℝ, 0 < s ∧ ∀ z, sourceRadius z < s → toCentral z ∉ V) :
    IsClosed (Set.range fun z ↦ (toCentral z, toFilling z)) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  have hpnot : p ∉ Set.range (fun z ↦ (toCentral z, toFilling z)) := hp
  rcases (hfillingRadius_nonneg p.2).eq_or_lt with hzero | hpos
  · obtain ⟨V, hVopen, hpV, s, hs, hsV⟩ := hend p.1
    let N : Set Y := {y | fillingRadius y < s}
    have hNopen : IsOpen N := isOpen_lt hfillingRadius continuous_const
    have hpN : p.2 ∈ N := by
      change fillingRadius p.2 < s
      rw [← hzero]
      exact hs
    refine ⟨V ×ˢ N, ?_, hVopen.prod hNopen, ⟨hpV, hpN⟩⟩
    intro w hw
    change w ∉ Set.range (fun z ↦ (toCentral z, toFilling z))
    rintro ⟨z, rfl⟩
    apply hsV z
    · have hzN := hw.2
      change fillingRadius (toFilling z) < s at hzN
      rwa [hradius] at hzN
    · exact hw.1
  · have hpRange : p.2 ∈ Set.range toFilling := by
      rw [hrange]
      exact hpos
    let R : Opens Y := ⟨Set.range toFilling, hfilling.isOpen_range⟩
    let e : Z ≃ₜ R := hfilling.isEmbedding.toHomeomorph
    let yp : R := ⟨p.2, hpRange⟩
    let z₀ : Z := e.symm yp
    have hfillz₀ : toFilling z₀ = p.2 := by
      calc
        toFilling z₀ = (e z₀).1 := by
          change toFilling z₀ =
            ↑(hfilling.isEmbedding.toHomeomorph z₀)
          exact (Topology.IsEmbedding.toHomeomorph_apply_coe hfilling.isEmbedding z₀).symm
        _ = p.2 := congrArg Subtype.val (e.apply_symm_apply yp)
    have hne : p.1 ≠ toCentral z₀ := by
      intro h
      apply hpnot
      exact ⟨z₀, Prod.ext h.symm hfillz₀⟩
    obtain ⟨U, V, hUopen, hVopen, hpU, hzV, hUV⟩ := t2_separation hne
    let S : Set R := (toCentral ∘ e.symm) ⁻¹' V
    have hSopen : IsOpen S := hVopen.preimage (hcentral.comp e.symm.continuous)
    have hypS : yp ∈ S := hzV
    let N : Set Y := Subtype.val '' S
    have hNopen : IsOpen N := R.isOpen.isOpenMap_subtype_val S hSopen
    have hpN : p.2 ∈ N := ⟨yp, hypS, rfl⟩
    refine ⟨U ×ˢ N, ?_, hUopen.prod hNopen, ⟨hpU, hpN⟩⟩
    intro w hw
    change w ∉ Set.range (fun z ↦ (toCentral z, toFilling z))
    rintro ⟨z, rfl⟩
    obtain ⟨q, hqS, hq⟩ := hw.2
    have hqeq : q = e z := by
      apply Subtype.ext
      exact hq.trans (Topology.IsEmbedding.toHomeomorph_apply_coe hfilling.isEmbedding z).symm
    apply Set.disjoint_left.1 hUV hw.1
    change toCentral (e.symm q) ∈ V at hqS
    simpa [hqeq] using hqS

/-- Three fillings attached along pairwise disjoint open collars of one central piece. -/
public structure FourPieceStarGluingData where
  central : TopCat
  filling : Fin 3 → TopCat
  centralCollar : Fin 3 → Opens central
  fillingCollar : ∀ i, Opens (filling i)
  collarEquiv : ∀ i, centralCollar i ≃ₜ fillingCollar i
  centralCollar_disjoint : Pairwise fun i j ↦ Disjoint (centralCollar i) (centralCollar j)

namespace FourPieceStarGluingData

variable (A : FourPieceStarGluingData)

/-- The central piece is indexed by `none`; the three fillings are indexed by `some i`. -/
public def piece : Option (Fin 3) → TopCat
  | none => A.central
  | some i => A.filling i

/-- Pairwise overlaps in the star diagram.  Distinct fillings do not overlap directly. -/
public def overlap : ∀ i, Option (Fin 3) → Opens (A.piece i)
  | none, none => ⊤
  | none, some j => A.centralCollar j
  | some i, none => A.fillingCollar i
  | some i, some j => if i = j then ⊤ else ⊥

public noncomputable def transition : ∀ i j,
    (Opens.toTopCat _).obj (A.overlap i j) ⟶
      (Opens.toTopCat _).obj (A.overlap j i)
  | none, none => 𝟙 _
  | none, some j => TopCat.ofHom ⟨A.collarEquiv j, (A.collarEquiv j).continuous⟩
  | some i, none => TopCat.ofHom ⟨(A.collarEquiv i).symm,
      (A.collarEquiv i).symm.continuous⟩
  | some i, some j => by
      by_cases h : i = j
      · subst j
        exact 𝟙 _
      · haveI : IsEmpty (A.overlap (some i) (some j)) := by
          constructor
          intro x
          simpa [overlap, h] using x.2
        haveI : IsEmpty (A.overlap (some j) (some i)) := by
          constructor
          intro x
          simpa [overlap, Ne.symm h] using x.2
        exact TopCat.ofHom ⟨Homeomorph.empty, Homeomorph.empty.continuous⟩

@[simp]
public theorem transition_none_none_apply (x : A.overlap none none) :
    A.transition none none x = x :=
  rfl

@[simp]
public theorem transition_none_some_apply (j : Fin 3) (x : A.overlap none (some j)) :
    A.transition none (some j) x = A.collarEquiv j x :=
  rfl

@[simp]
public theorem transition_some_none_apply (i : Fin 3) (x : A.overlap (some i) none) :
    A.transition (some i) none x = (A.collarEquiv i).symm x :=
  rfl

@[simp]
public theorem transition_some_self_apply (i : Fin 3) (x : A.overlap (some i) (some i)) :
    A.transition (some i) (some i) x = x := by
  simp [transition, Function.id_def]
  rfl

@[simp]
public theorem transition_none_none_val (x : A.overlap none none) :
    (A.transition none none x).1 = x.1 :=
  congrArg Subtype.val (A.transition_none_none_apply x)

@[simp]
public theorem transition_none_some_val (j : Fin 3) (x : A.overlap none (some j)) :
    (A.transition none (some j) x).1 = (A.collarEquiv j x).1 :=
  congrArg Subtype.val (A.transition_none_some_apply j x)

@[simp]
public theorem transition_some_none_val (i : Fin 3) (x : A.overlap (some i) none) :
    (A.transition (some i) none x).1 = ((A.collarEquiv i).symm x).1 :=
  congrArg Subtype.val (A.transition_some_none_apply i x)

@[simp]
public theorem transition_some_self_val (i : Fin 3)
    (x : A.overlap (some i) (some i)) :
    (A.transition (some i) (some i) x).1 = x.1 :=
  congrArg Subtype.val (A.transition_some_self_apply i x)

public theorem overlap_id (i : Option (Fin 3)) : A.overlap i i = ⊤ := by
  cases i with
  | none => rfl
  | some i => simp [overlap]

public theorem transition_id (i : Option (Fin 3)) : ⇑(A.transition i i) = id := by
  cases i with
  | none => rfl
  | some i => simp [transition]

public theorem transition_inter
    {i j : Option (Fin 3)} (k : Option (Fin 3)) (x : A.overlap i j) (hx : ↑x ∈ A.overlap i k) :
    (((↑) : (A.overlap j i) → (A.piece j))
      (A.transition i j x)) ∈ A.overlap j k := by
  cases i with
  | none =>
      cases j with
      | none =>
          rw [transition_none_none_val]
          exact hx
      | some j =>
          cases k with
          | none =>
              change (A.transition none (some j) x).1 ∈ A.fillingCollar j
              rw [transition_none_some_val]
              exact (A.collarEquiv j x).2
          | some k =>
              by_cases hjk : j = k
              · subst k
                simp [overlap]
              · exfalso
                have hmem : x.1 ∈ A.centralCollar j ⊓ A.centralCollar k := ⟨x.2, hx⟩
                rw [(A.centralCollar_disjoint hjk).eq_bot] at hmem
                change False at hmem
                exact hmem
  | some i =>
      cases j with
      | none =>
          cases k with
          | none =>
              simp [overlap]
          | some k =>
              by_cases hik : i = k
              · subst k
                change (A.transition (some i) none x).1 ∈ A.centralCollar i
                rw [transition_some_none_val]
                exact ((A.collarEquiv i).symm x).2
              · exfalso
                simp [overlap, hik] at hx
      | some j =>
          by_cases hij : i = j
          · subst j
            cases k with
            | none =>
                change (A.transition (some i) (some i) x).1 ∈ A.fillingCollar i
                rw [transition_some_self_val]
                exact hx
            | some k =>
                change (A.transition (some i) (some i) x).1 ∈
                  (if i = k then ⊤ else ⊥)
                rw [transition_some_self_val]
                exact hx
          · exfalso
            simpa [overlap, hij] using x.2

public theorem transition_cocycle
    (i j k : Option (Fin 3)) (x : A.overlap i j) (hx : ↑x ∈ A.overlap i k) :
    (((↑) : (A.overlap k j) → (A.piece k))
        (A.transition j k ⟨_, A.transition_inter k x hx⟩)) =
      ((↑) : (A.overlap k i) → (A.piece k))
        (A.transition i k ⟨x, hx⟩) := by
  cases i <;> cases j <;> cases k <;> simp_all [overlap, transition] <;>
    try rfl
  case none.some.none j =>
    change ((A.collarEquiv j).symm (A.collarEquiv j x)).1 = x.1
    exact congrArg Subtype.val ((A.collarEquiv j).symm_apply_apply x)
  case none.some.some j k =>
    by_cases h : j = k
    · subst k
      simp
      rfl
    · exfalso
      have hmem : x.1 ∈ A.centralCollar j ⊓ A.centralCollar k := ⟨x.2, hx⟩
      rw [(A.centralCollar_disjoint h).eq_bot] at hmem
      change False at hmem
      exact hmem
  case some.none.some i k =>
    by_cases h : i = k
    · subst k
      simp
      change (A.collarEquiv i ((A.collarEquiv i).symm x)).1 = x.1
      exact congrArg Subtype.val ((A.collarEquiv i).apply_symm_apply x)
    · exfalso
      simp [overlap, h] at hx
  case some.some.none i j =>
    by_cases h : i = j
    · subst j
      simp
      rfl
    · exfalso
      simpa [overlap, h] using x.2
  case some.some.some i j k =>
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp
        rfl
      · exfalso
        simp [overlap, hik] at hx
    · exfalso
      simpa [overlap, hij] using x.2

/-- The canonical four-piece topological gluing diagram associated to a star of collars. -/
public noncomputable def glueData : TopCat.GlueData :=
  TopCat.GlueData.mk' {
    J := Option (Fin 3)
    U := A.piece
    V := A.overlap
    t := transition A
    V_id := overlap_id A
    t_id := transition_id A
    t_inter := fun _ _ k x hx ↦ transition_inter A k x hx
    cocycle := transition_cocycle A }

/-- The graph of the `i`th collar identification in the two ambient pieces. -/
public def collarPairRange (i : Fin 3) : Set (A.central × A.filling i) :=
  Set.range fun x : A.centralCollar i ↦ (x.1, (A.collarEquiv i x).1)

/-- Equality in the gluing between the central piece and a filling is exactly membership in the
corresponding ambient collar graph. -/
public theorem ι_none_eq_ι_some_iff_mem_collarPairRange
    (i : Fin 3) (x : A.central) (y : A.filling i) :
    A.glueData.toGlueData.ι none x = A.glueData.toGlueData.ι (some i) y ↔
      (x, y) ∈ A.collarPairRange i := by
  let D := A.glueData
  let ni : D.J := none
  let si : D.J := some i
  let x' : D.U ni := x
  let y' : D.U si := y
  have hrel := D.ι_eq_iff_rel ni si x' y'
  change D.toGlueData.ι ni x' = D.toGlueData.ι si y' ↔ _
  apply hrel.trans
  change (∃ z : A.centralCollar i,
      z.1 = x ∧ (A.collarEquiv i z).1 = y) ↔ _
  simp only [collarPairRange.eq_def, Set.mem_range, Prod.mk.injEq]

/-- A central representative is also represented in the `i`th filling exactly when it lies in
the `i`th central collar. -/
public theorem exists_ι_none_eq_ι_some_iff_mem_centralCollar
    (i : Fin 3) (x : A.central) :
    (∃ y : A.filling i,
      A.glueData.toGlueData.ι none x =
        A.glueData.toGlueData.ι (some i) y) ↔
      x ∈ A.centralCollar i := by
  constructor
  · rintro ⟨y, hxy⟩
    obtain ⟨z, hz⟩ :=
      (A.ι_none_eq_ι_some_iff_mem_collarPairRange i x y).mp hxy
    have hzfst : z.1 = x := congrArg Prod.fst hz
    rw [← hzfst]
    exact z.2
  · intro hx
    let z : A.centralCollar i := ⟨x, hx⟩
    exact ⟨(A.collarEquiv i z).1,
      (A.ι_none_eq_ι_some_iff_mem_collarPairRange i x
        (A.collarEquiv i z).1).mpr ⟨z, rfl⟩⟩

/-- Distinct filling pieces have no equal representatives in a four-piece star gluing. -/
public theorem ι_some_ne_ι_some_of_ne
    {i j : Fin 3} (hij : i ≠ j) (x : A.filling i) (y : A.filling j) :
    A.glueData.toGlueData.ι (some i) x ≠ A.glueData.toGlueData.ι (some j) y := by
  intro h
  let D := A.glueData
  let si : D.J := some i
  let sj : D.J := some j
  let x' : D.U si := x
  let y' : D.U sj := y
  have h' : D.toGlueData.ι si x' = D.toGlueData.ι sj y' := h
  obtain ⟨z, _⟩ := (D.ι_eq_iff_rel si sj x' y').mp h'
  have hz : z.1 ∈ A.overlap (some i) (some j) := z.2
  simp [overlap, hij] at hz

/-- The intersection of the central-piece image with a filling-piece image is exactly the
image of the corresponding central collar. -/
public theorem range_ι_none_inter_range_ι_some (i : Fin 3) :
    Set.range (A.glueData.toGlueData.ι none) ∩
        Set.range (A.glueData.toGlueData.ι (some i)) =
      Set.range (fun x : A.centralCollar i ↦
        A.glueData.toGlueData.ι none x.1) := by
  ext p
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    have hxy : A.glueData.toGlueData.ι none x =
        A.glueData.toGlueData.ι (some i) y := hx.trans hy.symm
    obtain ⟨z, hz⟩ :=
      (A.ι_none_eq_ι_some_iff_mem_collarPairRange i x y).mp hxy
    have hzfst : z.1 = x := by
      exact congrArg Prod.fst hz
    refine ⟨z, ?_⟩
    exact (congrArg (A.glueData.toGlueData.ι none) hzfst).trans hx
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z.1, rfl⟩, (A.collarEquiv i z).1, ?_⟩
    exact ((A.ι_none_eq_ι_some_iff_mem_collarPairRange i z.1
      (A.collarEquiv i z).1).mpr ⟨z, rfl⟩).symm

/-- The images of two distinct filling pieces in the glued carrier are disjoint. -/
public theorem disjoint_range_ι_some_of_ne
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (Set.range (A.glueData.toGlueData.ι (some i)))
      (Set.range (A.glueData.toGlueData.ι (some j))) := by
  rw [Set.disjoint_left]
  rintro p ⟨x, hx⟩ ⟨y, hy⟩
  exact A.ι_some_ne_ι_some_of_ne hij x y (hx.trans hy.symm)

/-- For a star of Hausdorff pieces, closedness of its three ambient collar graphs is sufficient
for Hausdorffness of the glued carrier. -/
public theorem gluedT2_of_isClosed_collarPairRange
    [T2Space A.central] [∀ i, T2Space (A.filling i)]
    (hgraph : ∀ i, IsClosed (A.collarPairRange i)) :
    T2Space (GluedSpace A.glueData) := by
  apply (t2Space_gluedSpace_iff_pieceKernelsClosed A.glueData).2
  change ∀ i j : Option (Fin 3), IsClosed
    {p : A.piece i × A.piece j |
      A.glueData.toGlueData.ι i p.1 = A.glueData.toGlueData.ι j p.2}
  intro i j
  cases i with
  | none =>
      cases j with
      | none =>
          change IsClosed {p : A.central × A.central |
            A.glueData.toGlueData.ι none p.1 = A.glueData.toGlueData.ι none p.2}
          have heq : {p : A.central × A.central |
              A.glueData.toGlueData.ι none p.1 = A.glueData.toGlueData.ι none p.2} =
              Set.diagonal A.central := by
            ext p
            simp only [Set.mem_ofPred_eq, Set.mem_diagonal_iff]
            constructor
            · intro hp
              apply A.glueData.ι_injective none
              exact hp
            · exact fun hp ↦ congrArg (A.glueData.toGlueData.ι none) hp
          rw [heq]
          exact isClosed_diagonal
      | some j =>
          change IsClosed {p : A.central × A.filling j |
            A.glueData.toGlueData.ι none p.1 = A.glueData.toGlueData.ι (some j) p.2}
          rw [show {p : A.central × A.filling j |
              A.glueData.toGlueData.ι none p.1 = A.glueData.toGlueData.ι (some j) p.2} =
              A.collarPairRange j by
            ext p
            exact A.ι_none_eq_ι_some_iff_mem_collarPairRange j p.1 p.2]
          exact hgraph j
  | some i =>
      cases j with
      | none =>
          change IsClosed {p : A.filling i × A.central |
            A.glueData.toGlueData.ι (some i) p.1 = A.glueData.toGlueData.ι none p.2}
          rw [show {p : A.filling i × A.central |
              A.glueData.toGlueData.ι (some i) p.1 = A.glueData.toGlueData.ι none p.2} =
              Prod.swap ⁻¹' A.collarPairRange i by
            ext p
            constructor
            · intro hp
              exact (A.ι_none_eq_ι_some_iff_mem_collarPairRange i p.2 p.1).mp hp.symm
            · intro hp
              exact (A.ι_none_eq_ι_some_iff_mem_collarPairRange i p.2 p.1).mpr hp |>.symm]
          exact (hgraph i).preimage continuous_swap
      | some j =>
          by_cases hij : i = j
          · subst j
            change IsClosed {p : A.filling i × A.filling i |
              A.glueData.toGlueData.ι (some i) p.1 =
                A.glueData.toGlueData.ι (some i) p.2}
            have heq : {p : A.filling i × A.filling i |
                A.glueData.toGlueData.ι (some i) p.1 =
                  A.glueData.toGlueData.ι (some i) p.2} =
                Set.diagonal (A.filling i) := by
              ext p
              simp only [Set.mem_ofPred_eq, Set.mem_diagonal_iff]
              constructor
              · intro hp
                apply A.glueData.ι_injective (some i)
                exact hp
              · exact fun hp ↦ congrArg (A.glueData.toGlueData.ι (some i)) hp
            rw [heq]
            exact isClosed_diagonal
          · change IsClosed {p : A.filling i × A.filling j |
              A.glueData.toGlueData.ι (some i) p.1 =
                A.glueData.toGlueData.ι (some j) p.2}
            rw [show {p : A.filling i × A.filling j |
                A.glueData.toGlueData.ι (some i) p.1 =
                  A.glueData.toGlueData.ι (some j) p.2} = ∅ by
              ext p
              simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
              exact A.ι_some_ne_ι_some_of_ne hij p.1 p.2]
            exact isClosed_empty

/-- A four-piece star gluing is compact if the central piece and each filling contain compact
subsets whose canonical images cover the glued carrier.  This is the compact-core form used by
the paper construction, whose four open pieces are themselves noncompact. -/
public theorem gluedCompact_of_compact_core_cover
    (centralCore : Set A.central)
    (fillingCore : ∀ i, Set (A.filling i))
    (hcentral : IsCompact centralCore)
    (hfilling : ∀ i, IsCompact (fillingCore i))
    (hcover : ∀ x : GluedSpace A.glueData,
      (∃ y ∈ centralCore, A.glueData.toGlueData.ι none y = x) ∨
        ∃ i y, y ∈ fillingCore i ∧
          A.glueData.toGlueData.ι (some i) y = x) :
    CompactSpace (GluedSpace A.glueData) := by
  let _ : Finite A.glueData.J := by
    change Finite (Option (Fin 3))
    infer_instance
  let K : ∀ i, Set (A.glueData.U i)
    | none => centralCore
    | some i => fillingCore i
  apply compactSpace_gluedSpace_of_compact_piece_cover A.glueData K
  · intro i
    cases i with
    | none => exact hcentral
    | some i => exact hfilling i
  · intro x
    rcases hcover x with hcentralCover | hfillCover
    · obtain ⟨y, hy, hxy⟩ := hcentralCover
      exact ⟨none, y, hy, hxy⟩
    · obtain ⟨i, y, hy, hxy⟩ := hfillCover
      exact ⟨some i, y, hy, hxy⟩

/-- Compact cores in the four pieces give a compact star gluing when points outside a core can
be moved across a collar to a core on the other side. -/
public theorem gluedCompact_of_compact_cores
    (centralCore : Set A.central)
    (fillingCore : ∀ i, Set (A.filling i))
    (hcentralCompact : IsCompact centralCore)
    (hfillingCompact : ∀ i, IsCompact (fillingCore i))
    (hcentralCover : ∀ x : A.central,
      x ∈ centralCore ∨ ∃ i y, y ∈ fillingCore i ∧
        A.glueData.toGlueData.ι none x =
          A.glueData.toGlueData.ι (some i) y)
    (hfillingCover : ∀ i (y : A.filling i),
      y ∈ fillingCore i ∨ ∃ x : A.central,
        A.glueData.toGlueData.ι (some i) y =
          A.glueData.toGlueData.ι none x) :
    CompactSpace (GluedSpace A.glueData) := by
  apply A.gluedCompact_of_compact_core_cover centralCore fillingCore
    hcentralCompact hfillingCompact
  intro q
  obtain ⟨j, z, rfl⟩ := A.glueData.ι_jointly_surjective q
  cases j with
  | none =>
      rcases hcentralCover z with hz | hz
      · exact Or.inl ⟨z, hz, rfl⟩
      · obtain ⟨i, y, hy, hzy⟩ := hz
        exact Or.inr ⟨i, y, hy, hzy.symm⟩
  | some i =>
      rcases hfillingCover i z with hz | hz
      · exact Or.inr ⟨i, z, hz, rfl⟩
      · obtain ⟨x, hzx⟩ := hz
        rcases hcentralCover x with hx | hx
        · exact Or.inl ⟨x, hx, hzx.symm⟩
        · obtain ⟨j, y, hy, hxy⟩ := hx
          exact Or.inr ⟨j, y, hy, hxy.symm.trans hzx.symm⟩

/-- The central piece and the `i`th filling overlap whenever their collar is nonempty. -/
public theorem centralFillingOverlap_nonempty (i : Fin 3)
    (h : Nonempty (A.centralCollar i)) :
    (Set.range (A.glueData.toGlueData.ι none) ∩
      Set.range (A.glueData.toGlueData.ι (some i))).Nonempty := by
  let D := A.glueData
  let ni : D.J := none
  let si : D.J := some i
  have hni : Nonempty (D.toGlueData.V (ni, si)) := by
    change Nonempty (A.centralCollar i)
    exact h
  rw [show Set.range (D.toGlueData.ι ni) ∩ Set.range (D.toGlueData.ι si) =
      Set.range (D.toGlueData.f ni si ≫ D.toGlueData.ι ni) from
    D.image_inter ni si]
  let _ : Nonempty (D.toGlueData.V (ni, si)) := hni
  exact Set.range_nonempty _

/-- Nonempty collars connect the intersection graph of the four-piece star through its central
vertex. -/
public theorem intersectionGraphConnected
    (h : ∀ i, Nonempty (A.centralCollar i)) :
    GluingIntersectionGraphConnected A.glueData := by
  intro i j
  change Relation.ReflTransGen
    (fun i j : Option (Fin 3) =>
      (Set.range (A.glueData.toGlueData.ι i) ∩
        Set.range (A.glueData.toGlueData.ι j)).Nonempty) i j
  cases i with
  | none =>
      cases j with
      | none => exact Relation.ReflTransGen.refl
      | some j =>
          exact Relation.ReflTransGen.single (A.centralFillingOverlap_nonempty j (h j))
  | some i =>
      have hi : (Set.range (A.glueData.toGlueData.ι (some i)) ∩
          Set.range (A.glueData.toGlueData.ι none)).Nonempty := by
        simpa [Set.inter_comm] using A.centralFillingOverlap_nonempty i (h i)
      cases j with
      | none => exact Relation.ReflTransGen.single hi
      | some j =>
          exact (Relation.ReflTransGen.single hi).tail
            (A.centralFillingOverlap_nonempty j (h j))

/-- Nonempty attaching collars make all four pieces nonempty. -/
public theorem nonemptyPieceOfCollars
    (h : ∀ i, Nonempty (A.centralCollar i)) :
    ∀ i, Nonempty (A.glueData.U i) := by
  change ∀ i : Option (Fin 3), Nonempty (A.piece i)
  intro i
  cases i with
  | none => exact ⟨(h 0).some.1⟩
  | some i => exact ⟨(A.collarEquiv i (h i).some).1⟩

end FourPieceStarGluingData

end SphereSixComplex
