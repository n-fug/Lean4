/-
Copyright (c) 2026 Hang Lu Su, Valerio Proietti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Valerio Proietti
-/
module

public import Mathlib.GroupTheory.FinitelyPresentedGroup

/-!
# Group presentations as data

`Group.Presentation` packages a chosen presentation of a given group `G`:
a generating family together with relators (words `r`, each read as `r = 1`) whose
generated normal subgroup is exactly the kernel of `FreeGroup.lift val : FreeGroup α →* G`.
This the complementary to `PresentedGroup rels`, which constructs the group presented by a set of
generators and relations.

## Main definitions

* `Group.Generators G α`: a family `val : α → G`, indexed by `α`, with `FreeGroup.lift val`
  surjective.
* `Group.Presentation G α ρ`: a presentation `⟨α | rel⟩` of `G`, extending `Group.Generators G α`

## Main results

* `Group.Generators.fg` and `Group.fg_iff_nonempty_finite_generators`: a finite generating family
  witnesses `Group.FG`, and conversely.
* `Group.Presentation.isFinitelyPresented` and
  `Group.isFinitelyPresented_iff_nonempty_finite_presentation`: a finite presentation witnesses
  `Group.IsFinitelyPresented`, and conversely.

## Design notes

* Finiteness is expressed by instance arguments rather than bundled fields: a generating family is
  finite when `[Finite α]`, a presentation when `[Finite α] [Finite ρ]`.
* This file is multiplicative only: `PresentedGroup` has no additive counterpart and there is no
`to_additive`-generated `AddGroup.Presentation` so far.

## References

* [D. F. Holt, S. Rees, C. E. Röver, *Groups, Languages and Automata*][HoltReesRover2017], §1

## Tags

group presentation, generators and relations
-/

@[expose] public section

variable {G α ρ : Type*} [Group G]

/-- The generators of a group are given by a generating family indexed by `α` such that the induced
homomorphism `FreeGroup.lift val : FreeGroup α →* G` is surjective. -/
structure Group.Generators (G : Type*) [Group G] (α : Type*) where
  /-- The generating family itself: the element of `G` named by each index. -/
  val : α → G
  /-- The generators generate: the induced map `FreeGroup.lift val` is onto `G`. -/
  lift_surjective : Function.Surjective (FreeGroup.lift val)

namespace Group.Generators

variable (P : Group.Generators G α)

/-- A generating family generates `G`: the subgroup closure of its image is everything. This is the
elementary form of the defining condition; `Group.Generators.ofClosureEqTop` is the converse. -/
theorem closure_range_val_eq_top : Subgroup.closure (Set.range P.val) = ⊤ := by
  rw [← FreeGroup.range_lift_eq_closure, MonoidHom.range_eq_top]
  exact P.lift_surjective

/-- Build a generating family from the elementary condition that the image of `val` generates `G`
(`Subgroup.closure (Set.range val) = ⊤`), instead of from surjectivity of `FreeGroup.lift val`. -/
def ofClosureEqTop (val : α → G) (h : Subgroup.closure (Set.range val) = ⊤) :
    Group.Generators G α where
  val := val
  lift_surjective := by rw [← MonoidHom.range_eq_top, FreeGroup.range_lift_eq_closure]; exact h

/-- The underlying family of the generating family built by `ofClosureEqTop` is the map it was
built from. -/
@[simp]
theorem val_ofClosureEqTop (val : α → G) (h : Subgroup.closure (Set.range val) = ⊤) :
    (ofClosureEqTop val h).val = val := rfl

/-- The tautological generating family of `G`, indexed by `G` itself via the identity. -/
def self (G : Type*) [Group G] : Group.Generators G G :=
  ofClosureEqTop id (by rw [Set.range_id]; exact Subgroup.closure_univ)

/-- The underlying family of the tautological generating family `self` is the identity map. -/
@[simp]
theorem val_self : (self G).val = id := rfl

/-- A finite generating family (finitely many generators, `[Finite α]`) witnesses that `G` is
finitely generated: the induced surjection `FreeGroup α →* G` has finitely generated domain. -/
theorem fg [Finite α] (P : Group.Generators G α) : Group.FG G :=
  Group.fg_of_surjective P.lift_surjective

end Group.Generators

/-- A group is finitely generated if and only if it admits a bundled `Group.Generators` with a
finite index type. This is the bridge between the predicate `Group.FG` and the data-carrying
`Group.Generators`. -/
theorem Group.fg_iff_nonempty_finite_generators :
    Group.FG G ↔ ∃ (α : Type) (_ : Finite α), Nonempty (Group.Generators G α) := by
  rw [Group.fg_iff_exists_freeGroup_hom_surjective_finite]
  constructor
  · rintro ⟨α, hα, φ, hφ⟩
    obtain ⟨v, rfl⟩ := FreeGroup.lift.surjective φ
    exact ⟨α, hα, ⟨v, hφ⟩⟩
  · rintro ⟨α, hα, ⟨P⟩⟩
    exact ⟨α, hα, FreeGroup.lift P.val, P.lift_surjective⟩

/-- A presentation `⟨α | rel⟩` of a group `G`: a generating family `val : α → G` together with a
family of relators `rel : ρ → FreeGroup α`, words, each read as a defining relation `r = 1`
whose generated normal subgroup is exactly the kernel of the induced map `FreeGroup.lift val`.
Equivalently (see `Group.Presentation.presentedGroupEquiv`), `G` is isomorphic to the group
presented by these generators and relators. -/
structure Group.Presentation (G : Type*) [Group G] (α ρ : Type*)
    extends Group.Generators G α where
  /-- The family of relators, as words in the free group; each `rel r` is read as `rel r = 1`. -/
  rel : ρ → FreeGroup α
  /-- The relators are exactly the defining relations: the normal subgroup they generate is the
  full kernel of `FreeGroup.lift val`, so no relation holds in `G` beyond their consequences. -/
  ker_eq_normalClosure :
    (FreeGroup.lift val).ker = Subgroup.normalClosure (Set.range rel)

namespace Group.Presentation

variable (P : Group.Presentation G α ρ)

/-- The canonical surjection `FreeGroup α →* G` induced by the generators of the presentation. -/
def lift : FreeGroup α →* G := FreeGroup.lift P.val

/-- The set of relators of the presentation, as words in the free group (each read as `= 1`). This
is the datum fed to `PresentedGroup`. -/
def relSet : Set (FreeGroup α) := Set.range P.rel

/-- The canonical map `lift : FreeGroup α →* G` induced by the presentation is surjective; the
`lift`-level restatement of the generating family's `lift_surjective` field. -/
theorem lift_surjective' : Function.Surjective P.lift := P.lift_surjective

/-- The induced map `lift` sends the free-group generator `FreeGroup.of a` to the corresponding
generator `val a` of `G`. -/
@[simp]
theorem lift_of (a : α) : P.lift (FreeGroup.of a) = P.val a := FreeGroup.lift_apply_of

/-- The range of `lift : FreeGroup α →* G` is all of `G` — the subgroup-range form of its
surjectivity. -/
@[simp]
theorem range_lift_eq_top : P.lift.range = ⊤ :=
  MonoidHom.range_eq_top.mpr P.lift_surjective'

/-- Each relator `rel r` belongs to the relator set `relSet = Set.range rel`. -/
theorem rel_mem_relSet (r : ρ) : P.rel r ∈ P.relSet := ⟨r, rfl⟩

/-- The relator set of a presentation with finitely many relators is finite. -/
theorem relSet_finite [Finite ρ] : P.relSet.Finite := Set.finite_range P.rel

/-- Instance form of `relSet_finite`: typeclass search cannot unfold `relSet` to `Set.range rel`,
so the `Finite ↥(Set.range _)` instance does not apply to `↥relSet` on its own. -/
instance [Finite ρ] : Finite P.relSet := P.relSet_finite.to_subtype

/-- The kernel of `lift` is the normal closure of the relator set `relSet`: the presentation's
defining condition `ker_eq_normalClosure`, restated in terms of `lift` and `relSet`. -/
theorem ker_lift : P.lift.ker = Subgroup.normalClosure P.relSet := P.ker_eq_normalClosure

/-- A relator `r ∈ relSet` is respected by `lift`: it maps to the identity of `G`. This is the
universal-property side condition satisfied by the generators. -/
theorem lift_eq_one_of_mem_relSet {r : FreeGroup α} (hr : r ∈ P.relSet) : P.lift r = 1 :=
  MonoidHom.mem_ker.mp (by rw [P.ker_lift]; exact Subgroup.subset_normalClosure hr)

/-- Every relator `rel r` of the presentation maps to the identity under `lift`. -/
theorem lift_rel (r : ρ) : P.lift (P.rel r) = 1 :=
  P.lift_eq_one_of_mem_relSet (P.rel_mem_relSet r)

/-- A presentation of `G` exhibits `G` as the group presented by its generators and relators. -/
noncomputable def presentedGroupEquiv : PresentedGroup P.relSet ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq P.ker_eq_normalClosure.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective P.lift P.lift_surjective')

@[simp]
theorem presentedGroupEquiv_of (a : α) :
    P.presentedGroupEquiv (PresentedGroup.of a) = P.val a := P.lift_of a

/-- A finite presentation — finitely many generators (`[Finite α]`) together with finitely many
relators (`[Finite ρ]`) — witnesses that `G` is finitely presented (`Group.IsFinitelyPresented`).
This is the presentation-level analogue of `Group.Generators.fg`. -/
theorem isFinitelyPresented [Finite α] [Finite ρ] (P : Group.Presentation G α ρ) :
    Group.IsFinitelyPresented G := IsFinitelyPresented.equiv P.presentedGroupEquiv

end Group.Presentation

/-- A group is finitely presented (`Group.IsFinitelyPresented`) if and only if it admits a
`Group.Presentation` with finitely many generators and finitely many relators. This is the bridge
between the predicate `Group.IsFinitelyPresented` and the data-carrying `Group.Presentation`,
mirroring `Group.fg_iff_nonempty_finite_generators` for finite generation. -/
theorem Group.isFinitelyPresented_iff_nonempty_finite_presentation :
    Group.IsFinitelyPresented G ↔
      ∃ (α ρ : Type) (_ : Finite α) (_ : Finite ρ), Nonempty (Group.Presentation G α ρ) := by
  refine ⟨fun h => ?_, fun ⟨_, _, _, _, ⟨P⟩⟩ => P.isFinitelyPresented⟩
  obtain ⟨n, φ, hφ, s, hs, hsφ⟩ := h.out
  obtain ⟨v, rfl⟩ := FreeGroup.lift.surjective φ
  exact ⟨Fin n, s, inferInstance, hs.to_subtype,
    ⟨{ val := v
       lift_surjective := hφ
       rel := Subtype.val
       ker_eq_normalClosure := by rw [Subtype.range_val]; exact hsφ.symm }⟩⟩
