import tactic
import group_theory.subgroup data.fintype.basic group_theory.coset
import group_theory.group_action
import data.fintype.basic
import deprecated.subgroup

open_locale classical
open_locale big_operators
noncomputable theory

variables {α β : Type*} [group α] {s : set α} [is_subgroup s] [mul_action α β]

def centralizer (s : set α) : subgroup α := {
  carrier := {x : α | ∀ a ∈ s, x * a = a * x},
  one_mem' := by simp,
  mul_mem' := λ x y hx hy a ha, by rw [mul_assoc, hy a ha, ←mul_assoc, hx a ha, mul_assoc],
  inv_mem' := λ x hx a ha, by rw [←mul_right_inj x, ←mul_assoc, mul_inv_self, one_mul, ←mul_assoc, hx a ha, mul_inv_cancel_right],
}

def centralizer_element (s : α) : subgroup α :=
  centralizer {s}

instance fintype_quotient (s : set α) [fintype α] (h : is_subgroup s) :
  fintype(quotient_group.quotient s) := quotient.fintype $ _

def index_subgroup [fintype α] (b : subgroup α) : ℕ :=
  fintype.card(@quotient_group.quotient _ _ b.carrier (subgroup.is_subgroup b))

def conj_action (α : Type*) [group α] : mul_action α α := {
  smul := λ a b, a * b * a⁻¹,
  one_smul := by simp,
  mul_smul := λ a b c, by group,
}

def conj_class (g : α) : set α := {a : α | is_conj g a}

lemma conj_class_eq_orbit_conj_action (g : α) :
  conj_class g = @mul_action.orbit _ _ _ (conj_action α) g :=
begin
  rw [conj_class, mul_action.orbit],
  ext, split; intros ha; rcases ha with ⟨m, hm⟩; use m; rw ←hm; refl,
end

lemma conj_stabilizer_eq_centralizer (g : α) :
  (@mul_action.stabilizer _ _ _ (conj_action α) g) = (centralizer_element g).carrier :=
begin
  ext,
  simp only [mul_action.stabilizer, centralizer_element, centralizer, set.mem_singleton_iff, forall_eq, set.mem_set_of_eq],
  change (x * g * x⁻¹ = g) ↔ _,
  split,
  { intro hx, apply mul_right_cancel, rw hx, exact eq_mul_inv_of_mul_eq rfl },
  { intro hx, rw hx, exact mul_inv_eq_of_eq_mul rfl }
end

lemma disjoint_finset_of_disjoint {α : Type*} [fintype α] {s t : set α} (h : disjoint s t) :
  disjoint s.to_finset t.to_finset := 
begin
  intros a hinter,
  have hset : a ∈ ∅, 
  { rw [←set.bot_eq_empty, ←le_bot_iff.mp h],
    apply (set.mem_inter_iff a s t).mpr,
    split, 
      exact set.mem_to_finset.mp (finset.mem_of_mem_inter_left hinter),
      exact set.mem_to_finset.mp (finset.mem_of_mem_inter_right hinter) },
  exfalso, exact set.not_mem_empty a hset
end

lemma card_conj_class_eq_card_quotient_stabilizer [fintype α] (s : α) :
  fintype.card(conj_class s) = index_subgroup(centralizer_element s) :=
begin
  rw index_subgroup,
  apply fintype.card_congr,
  rw conj_class_eq_orbit_conj_action,
  conv_rhs begin congr, rw ←conj_stabilizer_eq_centralizer, end,
  apply mul_action.orbit_equiv_quotient_stabilizer,
end

-- class equation for a group action
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

-- class equation for groups
theorem card_eq_card_center_add_sum_card_centralizers [fintype α] (r : finset α)
    (hcover : r.bind(λ s, (conj_class s).to_finset) = finset.univ \ (subgroup.center α).carrier.to_finset)
    (hdisjoint : ∀ x y ∈ r, x ≠ y → disjoint (conj_class x) (conj_class y)) :
  fintype.card α = fintype.card(subgroup.center α) + ∑ s in r, index_subgroup(centralizer_element s) :=
begin
  conv_rhs begin congr, skip, congr, skip, funext, rw ←card_conj_class_eq_card_quotient_stabilizer, rw ←set.to_finset_card end,
  change finset.univ.card = fintype.card ↥((subgroup.center α).carrier) + _,
  rw [←finset.sdiff_union_of_subset (subgroup.center α).carrier.to_finset.subset_univ,
      finset.card_disjoint_union (finset.sdiff_disjoint), add_comm, ←hcover, finset.card_bind],
  { rw [add_left_inj, set.to_finset_card] },
  exact λ x hx y hy hxyne, disjoint_finset_of_disjoint (hdisjoint x y hx hy hxyne),
end