import tactic
import data.fintype.basic
import group_theory.subgroup
import group_theory.coset
import group_theory.group_action
import deprecated.subgroup

open_locale classical
open_locale big_operators
noncomputable theory

section finset

/-- If two sets are disjoint, converting them to finsets also leaves them disjoint. -/
lemma disjoint_finset_of_disjoint {α : Type*} [fintype α] {s t : set α} (h : disjoint s t) :
  disjoint s.to_finset t.to_finset :=
begin
  rw disjoint,
  rw disjoint at h,
  rw le_bot_iff at h,
  change _ ∩ _ = ∅ at h,
  rw le_bot_iff,
  change _ ∩ _ = ∅,
  rw ←set.to_finset_inter,
  conv_lhs begin congr, rw h, end,
  ext; simp,
end

lemma sdiff_to_finset {α : Type*} [fintype α] (a b : set α) :
  (a \ b).to_finset = a.to_finset \ b.to_finset := by ext; simp

lemma Union_to_finset_eq_to_finset_bind {ι α : Type*} [fintype ι] [fintype α] (f : ι → set α) :
  (⋃ i : ι, f i).to_finset = (finset.univ : finset ι).bind(λ i, (f i).to_finset) := by ext; simp


end finset

variables {α β : Type*} [group α] [mul_action α β]

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

instance fintype_quotient (s : set α) [fintype α] (h : is_subgroup s) :
  fintype(quotient_group.quotient s) := quotient.fintype $ _

-- FIXME: make nicer after the is_subgroup refactoring
def index_subgroup [fintype α] (b : subgroup α) : ℕ :=
  fintype.card(@quotient_group.quotient _ _ b.carrier (subgroup.is_subgroup b))

/-- finite version of Lagrange's theorem: the cardinality of a group is
the product of the index of a subgroup times the cardinality of the subgroup. -/
def card_group_eq_index_subgroup_mul_card_subgroup [fintype α] (b : subgroup α) :
  fintype.card α = index_subgroup b * fintype.card b :=
begin
  rw [index_subgroup, ←fintype.card_prod],
  exact fintype.card_congr (is_subgroup.group_equiv_quotient_times_subgroup (subgroup.is_subgroup b)),
end

def one_le_card_group [fintype α] :
  1 ≤ fintype.card α := by rw ←finset.card_singleton (1 : α); apply finset.card_le_of_subset; simp

def index_subgroup_eq_div [fintype α] (b : subgroup α) :
  index_subgroup b = fintype.card α / fintype.card b := (nat.div_eq_of_eq_mul_left (one_le_card_group) (card_group_eq_index_subgroup_mul_card_subgroup b)).symm


def conj_action (α : Type*) [group α] : mul_action α α := {
  smul := λ a b, a * b * a⁻¹,
  one_smul := by simp,
  mul_smul := λ a b c, by group,
}

/-- Equivalence class of g under conjugation. -/
def conj_class (g : α) : set α := {a : α | is_conj g a}

lemma mem_self_conj_class (g : α) : g ∈ conj_class g := is_conj_refl g

local attribute [instance] conj_action

/-- The conjugation class of an element is the same as the orbit of that
element of the group acting on itself under conjugation.-/
lemma conj_class_eq_orbit_conj_action (g : α) :
  conj_class g = mul_action.orbit α g :=
begin
  rw [conj_class, mul_action.orbit],
  ext, split; intros ha; rcases ha with ⟨m, hm⟩; use m; rw ←hm; refl,
end

/-- The stabilizer of an element of the group acting on itself under
conjugation is the same as the centralizer of that element. -/
lemma conj_stabilizer_eq_centralizer (g : α) :
  (mul_action.stabilizer α g) = (centralizer_element g).carrier :=
begin
  ext,
  simp only [mul_action.stabilizer, centralizer_element, centralizer, set.mem_singleton_iff, forall_eq, set.mem_set_of_eq],
  change (x * g * x⁻¹ = g) ↔ _,
  split,
  { intro hx, apply mul_right_cancel, rw hx, exact eq_mul_inv_of_mul_eq rfl },
  { intro hx, rw hx, exact mul_inv_eq_of_eq_mul rfl }
end

lemma card_conj_class_eq_index_centralizer [fintype α] (s : α) :
  fintype.card(conj_class s) = index_subgroup(centralizer_element s) :=
begin
  rw index_subgroup,
  apply fintype.card_congr,
  rw conj_class_eq_orbit_conj_action,
  conv_rhs begin congr, rw ←conj_stabilizer_eq_centralizer, end,
  apply mul_action.orbit_equiv_quotient_stabilizer,
end

/-- Class equation for a group action. r is a finset of representatives of the orbits. -/
theorem card_set_eq_sum_card_orbits [fintype β] (r : finset β)
    (hcover : r.bind(λ s, (mul_action.orbit α s).to_finset) = finset.univ)
    (hdisjoint : ∀ x y ∈ r, x ≠ y → disjoint (mul_action.orbit α x) (mul_action.orbit α y)) :
  fintype.card β = ∑ s in r, fintype.card(mul_action.orbit α s) :=
begin
  change finset.univ.card = _,
  conv_rhs begin congr, skip, funext, rw ←set.to_finset_card, end,
  rw [←hcover, finset.card_bind],
  exact λ x hx y hy hxyne, disjoint_finset_of_disjoint (hdisjoint x y hx hy hxyne),
end

/-- Class equation for finite groups: r is a finset of representatives of the
non-trivial conjugation classes (the trivial ones are all size one, and
generated by elements in the center of the group). -/
theorem card_eq_card_center_add_sum_card_centralizers [fintype α] (r : finset α)
    (hcover : r.bind(λ s, (conj_class s).to_finset) = finset.univ \ (subgroup.center α).carrier.to_finset)
    (hdisjoint : ∀ x y ∈ r, x ≠ y → disjoint (conj_class x) (conj_class y)) :
  fintype.card α = fintype.card(subgroup.center α) + ∑ s in r, index_subgroup(centralizer_element s) :=
begin
  conv_rhs begin congr, skip, congr, skip, funext, rw ←card_conj_class_eq_index_centralizer, rw ←set.to_finset_card end,
  change finset.univ.card = fintype.card ↥((subgroup.center α).carrier) + _,
  rw [←finset.sdiff_union_of_subset (subgroup.center α).carrier.to_finset.subset_univ,
      finset.card_disjoint_union (finset.sdiff_disjoint), add_comm, ←hcover, finset.card_bind],
  { rw [add_left_inj, set.to_finset_card] },
  exact λ x hx y hy hxyne, disjoint_finset_of_disjoint (hdisjoint x y hx hy hxyne),
end



lemma hcover_to_finset {ι : Type*} [fintype α] (f : ι → α) [fintype ι]
    (hcover : (⋃ s : ι, (conj_class (f s))) = (set.univ \ (subgroup.center α).carrier)) :
  (finset.univ : finset ι).bind(λ s, (conj_class (f s)).to_finset) = finset.univ \ (subgroup.center α).carrier.to_finset :=
begin
  rw ←Union_to_finset_eq_to_finset_bind, rw ←set.to_finset_univ,
  -- this part is a mess, but if I do more straightforward things I run into fintype issues.
  -- I'd like to either to
  -- rw hcover, -- motive is not type correct
  -- or
  -- rw ←sdiff_to_finset, -- did not find instance of the pattern in the target expression
  -- and delete the remaining mess
  ext,
  cases set.ext_iff.mp hcover a with h1 h2,
  simp only [true_and, set.mem_Union, set.mem_univ, set.mem_diff, exists_imp_distrib] at h1 h2,
  split; simp only [true_and, set.mem_Union, finset.mem_univ, set.mem_to_finset, set.to_finset_univ, finset.mem_sdiff, exists_imp_distrib],
  exact h1, exact h2,
end


theorem card_eq_card_center_add_sum_card_centralizers' {ι : Type*} [fintype α] (f : ι → α) [fintype ι]
    (hcover : (⋃ s : ι, (conj_class (f s))) = (set.univ \ (subgroup.center α).carrier))
    (hdisjoint : ∀ i j : ι, i ≠ j → disjoint (conj_class (f i)) (conj_class (f j))) :
  fintype.card α = fintype.card(subgroup.center α) + ∑ s : ι, index_subgroup(centralizer_element (f s)) :=
begin
  conv_rhs begin congr, skip, congr, skip, funext, rw ←card_conj_class_eq_index_centralizer, rw ←set.to_finset_card end,
  change finset.univ.card = fintype.card ↥((subgroup.center α).carrier) + _,
  have hcover' := hcover_to_finset f hcover,
  rw [←finset.sdiff_union_of_subset (subgroup.center α).carrier.to_finset.subset_univ,
      finset.card_disjoint_union (finset.sdiff_disjoint), add_comm, ←hcover', finset.card_bind],
  { rw [add_left_inj, set.to_finset_card] },
  exact λ i _ j _ hxyne, disjoint_finset_of_disjoint (hdisjoint i j hxyne),
end
