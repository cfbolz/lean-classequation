import tactic
import data.fintype.basic
import group_theory.subgroup
import group_theory.coset
import group_theory.group_action
import group_theory.order_of_element

open_locale classical
open_locale big_operators
noncomputable theory

section finset

-- goes to data/finset/basic.lean

/-- Two sets are disjoint iff they are disjoint as finsets. -/
lemma disjoint_finset_iff_disjoint {α : Type*} [fintype α] {s t : set α} :
  disjoint s t ↔ disjoint s.to_finset t.to_finset :=
begin
  rw [disjoint, disjoint, le_bot_iff, le_bot_iff],
  change _ ∩ _ = ∅ ↔ _ ∩ _ = ∅,
  rw ←set.to_finset_inter,
  split,
  { intro h, simp_rw h, ext, simp },
  { intro h, ext, rw ←set.mem_to_finset, rw h, simp }
end

lemma Union_to_finset_eq_bind {ι α : Type*} [fintype ι] [fintype α] (f : ι → set α) :
  (⋃ i : ι, f i).to_finset = (finset.univ : finset ι).bind(λ i, (f i).to_finset) := by ext; simp


end finset


section group_action

-- into group_theory/group_action.lean


variables {α β : Type*} [group α] [mul_action α β]

/-- Class equation for a group action. f is an indexed set of representatives
of all the orbits. -/
theorem card_set_eq_sum_card_orbits [fintype β] {ι : Type*} (f : ι → β) [fintype ι]
    (hcover : (⋃ i : ι, (mul_action.orbit α (f i))) = set.univ)
    (hdisjoint : ∀ i j : ι, i ≠ j → disjoint (mul_action.orbit α (f i)) (mul_action.orbit α (f j))) :
  fintype.card β = ∑ i : ι, fintype.card(mul_action.orbit α (f i)) :=
begin
  simp_rw ←set.to_finset_card,
  have hcover' : (finset.univ : finset ι).bind(λ s, (mul_action.orbit α (f s)).to_finset) = finset.univ,
  { rw [←Union_to_finset_eq_bind, ←set.to_finset_univ], simp_rw hcover, congr },
  change finset.univ.card = _,
  rw [←hcover', finset.card_bind],
  exact λ i _ j _ hxyne, disjoint_finset_iff_disjoint.mp (hdisjoint i j hxyne),
end

end group_action


section group

variables {α β : Type*} [group α] [mul_action α β]

def index_subgroup [fintype α] (b : subgroup α) : ℕ :=
  fintype.card(quotient_group.quotient b)

/-- finite version of Lagrange's theorem: the cardinality of a group is
the product of the index of a subgroup times the cardinality of the subgroup.
Follows directly from `group_equiv_quotient_times_subgroup` -/
def card_group_eq_index_subgroup_mul_card_subgroup [fintype α] (b : subgroup α) :
  fintype.card α = index_subgroup b * fintype.card b := card_eq_card_quotient_mul_card_subgroup _

def one_le_card_group [fintype α] :
  1 ≤ fintype.card α := by rw ←finset.card_singleton (1 : α); apply finset.card_le_of_subset; simp

def index_subgroup_eq_div [fintype α] (b : subgroup α) :
  index_subgroup b = fintype.card α / fintype.card b :=
  (nat.div_eq_of_eq_mul_left one_le_card_group (card_group_eq_index_subgroup_mul_card_subgroup b)).symm


def conj_action (α : Type*) [group α] : mul_action α α := {
  smul := λ a b, a * b * a⁻¹,
  one_smul := by simp,
  mul_smul := λ a b c, by group,
}

/-- Equivalence class of g under conjugation. -/
def conj_class (g : α) : set α := {a : α | is_conj g a}

lemma mem_conj_class_iff (g₁ g₂ : α) : g₁ ∈ conj_class g₂ ↔ is_conj g₂ g₁ := by rw conj_class; simp

lemma mem_self_conj_class (g : α) : g ∈ conj_class g := is_conj_refl g

local attribute [instance] conj_action

/-- The conjugation class of an element is the same as the orbit of that
element of the group acting on itself under conjugation.-/
lemma conj_class_eq_orbit_conj_action (g : α) :
  conj_class g = mul_action.orbit α g :=
begin
  ext,
  split;
  { rw [mem_conj_class_iff, mul_action.mem_orbit_iff],
    intros ha,
    rcases ha with ⟨m, hm⟩,
    use m, rw ←hm,
    refl},
end

/-- The centralizer of a set of group elements. -/
def centralizer (s : set α) : subgroup α := {
  carrier := {x : α | ∀ a ∈ s, x * a = a * x},
  one_mem' := by simp,
  mul_mem' := λ x y hx hy a ha, by rw [mul_assoc, hy a ha, ←mul_assoc, hx a ha, mul_assoc],
  inv_mem' := λ x hx a ha, by rw [←mul_right_inj x, ←mul_assoc, mul_inv_self, one_mul, ←mul_assoc, hx a ha, mul_inv_cancel_right],
}

/-- As a shortcut, the centralizer of a single group element. -/
def centralizer_element (s : α) : subgroup α :=
  centralizer {s}

/-- The stabilizer of an element of the group acting on itself under
conjugation is the same as the centralizer of that element. -/
lemma conj_stabilizer_eq_centralizer (g : α) :
  (mul_action.stabilizer α g) = (centralizer_element g) :=
begin
  ext,
  simp only [mul_action.stabilizer, centralizer_element, centralizer, set.mem_singleton_iff, forall_eq],
  change (x * g * x⁻¹ = g) ↔ x * g = g * x,
  split,
  { intro hx, apply mul_right_cancel, rw hx, exact eq_mul_inv_of_mul_eq rfl },
  { intro hx, rw hx, exact mul_inv_eq_of_eq_mul rfl }
end

lemma card_conj_class_eq_index_centralizer [fintype α] (s : α) :
  fintype.card(conj_class s) = index_subgroup(centralizer_element s) :=
begin
  apply fintype.card_congr,
  simp_rw [conj_class_eq_orbit_conj_action, ←conj_stabilizer_eq_centralizer],
  apply mul_action.orbit_equiv_quotient_stabilizer,
end

/-- Class equation for finite groups: f is an index set of representatives of
the non-trivial conjugation classes (the trivial ones are all size one, and
contain each an element of the center of the group). -/
theorem card_eq_card_center_add_sum_card_centralizers' [fintype α] {ι : Type*} [fintype ι] (f : ι → α)
    (hcover : (⋃ s : ι, (conj_class (f s))) = (set.univ \ (subgroup.center α)))
    (hdisjoint : ∀ i j : ι, i ≠ j → disjoint (conj_class (f i)) (conj_class (f j))) :
  fintype.card α = fintype.card(subgroup.center α) + ∑ s : ι, index_subgroup(centralizer_element (f s)) :=
begin
  simp_rw [←card_conj_class_eq_index_centralizer, ←set.to_finset_card],
  change finset.univ.card = fintype.card ↥((subgroup.center α).carrier) + _,
  have hcover' : (finset.univ : finset ι).bind(λ s, (conj_class (f s)).to_finset) = finset.univ \ (subgroup.center α).carrier.to_finset,
  { rw [←Union_to_finset_eq_bind, ←set.to_finset_univ],
    simp_rw hcover, tidy },
  rw [←finset.sdiff_union_of_subset (subgroup.center α).carrier.to_finset.subset_univ,
      finset.card_disjoint_union (finset.sdiff_disjoint), add_comm, ←hcover', finset.card_bind],
  { rw [add_left_inj, set.to_finset_card] },
  exact λ i _ j _ hxyne, disjoint_finset_iff_disjoint.mp (hdisjoint i j hxyne),
end

end group