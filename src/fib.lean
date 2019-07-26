import data.list.basic
-- import .deps
-- import .dlb

@[reducible]
def fibonacci : ℕ → ℕ
| 0 := 0
| 1 := 1
| (n+2) := fibonacci n + fibonacci (n+1)

open nat list
---
@[reducible]
def fib_sum (n : ℕ) : ℕ :=
((range n).map fibonacci).sum

@[reducible]
def fib_odd_sum (n : ℕ) : ℕ :=
((range n).map (λ m, fibonacci (2*m + 1))).sum

@[reducible]
def fib_even_sum (n : ℕ) : ℕ :=
((range n).map (λ m, fibonacci (2*m))).sum
---
theorem fib_odd_sum_eq : ∀ (n : ℕ),
  fib_odd_sum n = fibonacci (2*n)
| 0 := rfl
| (n+1) := by rw [fib_odd_sum,
  sum_range_succ,
  ←fib_odd_sum,
  fib_odd_sum_eq,
  mul_add,
  mul_one,
  fibonacci]

-- #print fib_odd_sum_eq
---
theorem fib_even_sum_eq : ∀ {n : ℕ} (h : n > 0),
  fib_even_sum n + 1 = fibonacci (2*n - 1)
| 0 h := (gt_irrefl 0 h).elim
| 1 _ := rfl
| (n+2) _ :=
have H : fib_even_sum (n+1) + 1 = fibonacci (2*(n+1) - 1) :=
  fib_even_sum_eq (succ_pos n),
begin
  rw [fib_even_sum,
    sum_range_succ,
    ←fib_even_sum,
    add_right_comm,
    H,
    mul_add,
    mul_one,
    mul_add],
  change fibonacci (2*n + 1) + fibonacci (2*n + 1 + 1) =
    fibonacci (2*n + 1 + 2),
  rw [←fibonacci],
end
---
theorem fib_sum_eq : ∀ (n : ℕ),
  fib_sum n + 1 = fibonacci (n+1)
| 0 := rfl
| (n+1) :=
begin
  rw [fibonacci,
    ←fib_sum_eq n],
  simp [range_concat, fib_sum],
--   simp only [range_concat,
--  fib_sum,
--  list.sum_cons,
--  add_zero,
--  list.sum_nil,
--  list.map_append,
--  add_comm,
--  list.sum_append,
--  add_right_inj,
--  add_left_comm,
--  list.map]
end

inductive bee : Type
| queen : bee
| worker : bee
| drone : bee

open bee list

instance : has_repr bee :=
⟨λ s, match s with
| queen := "Q"
| worker := "W"
| drone := "D"
end⟩
---
namespace bee

def parents : bee → list bee
| queen := [queen, drone]
| worker := [queen, drone]
| drone := [queen]

def ancestors (b : bee) : ℕ → list bee
| 0 := [b]
| (n+1) := ((ancestors n).map parents).join
---
def tree_json : bee → ℕ → string
| b 0 := "{\"name\":\"" ++ repr b ++ "\"}"
| b (n+1) := "{\"name\":\"" ++ repr b ++ "\",\"children\":[" ++
  string.intercalate "," (b.parents.map (λ p, p.tree_json n)) ++ "]}"
---
lemma drone_ancestors_concat : ∀ (n : ℕ),
  drone.ancestors (n+2) = drone.ancestors (n+1) ++ drone.ancestors n
| 0 := rfl
| (n+1) := begin
  change ((ancestors _ (n+2)).map _).join = _,
  conv { to_lhs,
    rw [drone_ancestors_concat n,
      map_append,
      join_append], },
  refl,
end
---
theorem drone_ancestors_length_eq_fib_succ : ∀ (n : ℕ),
  (drone.ancestors n).length = fibonacci (n+1)
| 0 := rfl
| 1 := rfl
| (n+2) := begin
  rw [drone_ancestors_concat,
    length_append,
    drone_ancestors_length_eq_fib_succ n,
    drone_ancestors_length_eq_fib_succ (n+1),
    add_comm],
  refl,
end

end bee

inductive car : Type
| rabbit : car
| cadillac : car

open car list nat

instance : has_repr car :=
⟨λ s, match s with
| rabbit := "R"
| cadillac := "C"
end⟩
---
namespace car

@[reducible]
def size : car → ℕ
| rabbit := 1
| cadillac := 2

@[reducible]
def sum_size (cs : list car) : ℕ :=
(cs.map size).sum

lemma sum_size_cons (c : car) (cs : list car) :
  sum_size (c :: cs) = sum_size cs + c.size :=
by simp only [sum_size, sum_cons, map, add_comm]
---
@[reducible]
def packings : ℕ → list (list car)
| 0 := [[]]
| 1 := [[rabbit]]
| (n+2) := (packings (n+1)).map (cons rabbit) ++
  (packings n).map (cons cadillac)
---
theorem num_packings_eq_fib : ∀ (n : ℕ),
  (packings n).length = fibonacci (n+1)
| 0 := rfl
| 1 := rfl
| (n+2) :=
begin
  simp [packings, fibonacci],
  rw [num_packings_eq_fib n,
    num_packings_eq_fib (n+1),
    add_left_comm,
    add_left_inj,
    fibonacci],
end

---
theorem packings_size : ∀ {n : ℕ} {cs : list car} (h : cs ∈ packings n),
  sum_size cs = n
| 0 cs h :=
begin
  rw mem_singleton.1 h,
  refl,
end
| 1 cs h :=
begin
  rw mem_singleton.1 h,
  refl,
end
| (n+2) cs h :=
begin
  simp [packings] at h,
  rcases h with ⟨cs', h₁, h₂⟩ | ⟨cs', h₁, h₂⟩,
  all_goals { rw [←h₂,
    sum_size_cons,
    size,
    packings_size h₁], },
end
---
lemma car_size_ne_zero (c : car) : size c ≠ 0 :=
by cases c; contradiction

lemma sum_size_zero : ∀ {cs : list car} (h : sum_size cs = 0),
  cs = []
| [] _ := rfl
| (c::cs) h :=
begin
  exfalso,
  rw [sum_size_cons,
      add_eq_zero_iff] at h,
  exact car_size_ne_zero c h.2,
end
---
lemma sum_size_one : ∀ {cs : list car} (h : sum_size cs = 1),
  cs = [rabbit]
| [] h := by contradiction
| (rabbit::cs) h :=
begin
  rw [sum_size_cons] at h,
  simp,
  exact sum_size_zero (succ_inj h),
end
| (cadillac::cs) h :=
begin
  rw [sum_size_cons] at h,
  have : sum_size cs + 1 = 0 := succ_inj h,
  contradiction,
end
---

-- set_option trace.simp_lemmas true
theorem all_packings : ∀ {n : ℕ} {cs : list car} (h : sum_size cs = n),
  cs ∈ packings n
| 0 cs h := by simp [packings, sum_size_zero h]
| 1 cs h := by simp [packings, sum_size_one h]
| (n+2) [] h := by contradiction
| (n+2) (rabbit::cs) h :=
begin
  rw [sum_size_cons,
    add_right_inj 1] at h,
  simp [packings, all_packings, h],
--   simp only [packings,
--  all_packings,
--  h,
--  list.mem_append,
--  true_and,
--  list.mem_map,
--  exists_false,
--  or_false,
--  exists_eq_right,
--  and_false,
--  list.map,
--  false_and]
end
| (n+2) (cadillac::cs) h :=
begin
  rw [sum_size_cons,
    add_right_inj 2] at h,
  simp [packings, all_packings, h],
--   simp only [packings,
--  all_packings,
--  h,
--  list.mem_append,
--  true_and,
--  list.mem_map,
--  false_or,
--  exists_false,
--  exists_eq_right,
--  and_false,
--  list.map,
--  false_and]
end

end car

-- #eval print_content
/-
fib.lean:258:0: information trace output
- Name: bee
  Line: 80
  Type: inductive
  Size: 4
- Name: car.sum_size_cons
  Line: 160
  Type: theorem
  Statement uses: [car.size, nat.has_add, has_add.add, list.cons, car.sum_size, nat, eq, list, car]
  Size: 151
  Proof uses lemmas: [add_comm, eq.refl, list.sum_cons, list.map.equations._eqn_2, car.sum_size.equations._eqn_1, eq.trans, congr_arg, congr]
  and uses: [nat.add_comm_semigroup, add_comm_semigroup.to_add_semigroup, has_zero, has_add, add_monoid.to_has_zero, nat.add_monoid, add_monoid.to_add_semigroup, add_semigroup.to_has_add, id, list.map, nat.has_zero, list.sum, car.size, nat.has_add, has_add.add, list.cons, car.sum_size, nat, eq, eq.mpr, list, car]
  Proof size: 3985
- Name: car.packings_size
  Line: 186
  Type: theorem
  Statement uses: [car.sum_size, eq, car.packings, list.has_mem, has_mem.mem, car, list, nat]
  Size: 185
  Proof uses lemmas: [car.size.equations._eqn_2, car.size.equations._eqn_1, car.sum_size_cons, eq.symm, Exists.dcases_on, or.dcases_on, list.mem_map, list.mem_append, propext, car.packings.equations._eqn_3, congr_arg, congr, eq.trans, list.mem_singleton, iff.mp, eq.refl]
  and uses: [pprod.snd, pprod, punit, nat.rec, nat.add, pprod.fst, car.size, and.dcases_on, has_mem, list.has_append, has_append.append, list.map, eq.mp, bit0, nat.has_add, has_add.add, car.cadillac, and, Exists, or, car.rabbit, nat.has_one, has_one.one, nat.succ, list.cons, eq.rec, id, list.nil, eq.mpr, nat.has_zero, has_zero.zero, id_rhs, nat.zero, nat.cases_on, nat.below, car.sum_size, eq, nat.brec_on, car.packings, list.has_mem, has_mem.mem, car, list, nat]
  Proof size: 41470
- Name: fib_even_sum_eq
  Line: 38
  Type: theorem
  Statement uses: [bit0, nat.has_mul, has_mul.mul, nat.has_sub, has_sub.sub, fibonacci, nat.has_one, has_one.one, fib_even_sum, nat.has_add, has_add.add, eq, nat.has_zero, has_zero.zero, nat.has_lt, gt, nat]
  Size: 355
  Proof uses lemmas: [nat.succ_pos, fibonacci.equations._eqn_3, mul_one, mul_add, add_right_comm, eq.symm, list.sum_range_succ, fib_even_sum.equations._eqn_1, eq.refl, rfl, gt_irrefl]
  and uses: [pprod, punit, nat.rec, nat.add, pprod.fst, monoid.to_has_one, nat.monoid, monoid.to_semigroup, semigroup.to_has_mul, distrib.to_has_mul, nat.distrib, distrib.to_has_add, nat.add_comm_semigroup, add_comm_semigroup.to_add_semigroup, add_monoid.to_has_zero, nat.add_monoid, add_monoid.to_add_semigroup, add_semigroup.to_has_add, eq.rec, id, list.range, list.map, list.sum, eq.mpr, nat.succ, nat.ordered_semiring, ordered_semiring.to_ordered_cancel_comm_monoid, ordered_cancel_comm_monoid.to_ordered_comm_monoid, ordered_comm_monoid.to_partial_order, partial_order.to_preorder, false.elim, id_rhs, nat.zero, nat.cases_on, nat.below, bit0, nat.has_mul, has_mul.mul, nat.has_sub, has_sub.sub, fibonacci, nat.has_one, has_one.one, fib_even_sum, nat.has_add, has_add.add, eq, nat.brec_on, nat.has_zero, has_zero.zero, nat.has_lt, gt, nat]
  Proof size: 70504
- Name: car.rabbit.inj
  Line: 137
  Type: definition
  Uses: [true, car.rabbit, car, eq]
  Size: 54
- Name: car.rabbit.inj_arrow
  Line: 137
  Type: definition
  Uses: [true, car.rabbit, car, eq]
  Size: 103
- Name: car.size
  Line: 152
  Type: definition
  Uses: [nat, car]
  Size: 14
- Name: bee.rec_on
  Line: 80
  Type: definition
  Uses: [bee.drone, bee.worker, bee.queen, bee]
  Size: 127
- Name: bee.no_confusion_type
  Line: 80
  Type: definition
  Uses: [bee]
  Size: 296
- Name: bee.sizeof
  Line: 80
  Type: definition
  Uses: [nat, bee]
  Size: 134
- Name: bee.worker.inj_eq
  Line: 80
  Type: definition
  Uses: [true, bee.worker, bee, eq]
  Size: 211
- Name: car.cadillac.inj_eq
  Line: 137
  Type: definition
  Uses: [true, car.cadillac, car, eq]
  Size: 227
- Name: bee.worker.inj
  Line: 80
  Type: definition
  Uses: [true, bee.worker, bee, eq]
  Size: 54
- Name: car.sum_size
  Line: 157
  Type: definition
  Uses: [nat, car, list]
  Size: 105
- Name: bee.drone.inj_arrow
  Line: 80
  Type: definition
  Uses: [true, bee.drone, bee, eq]
  Size: 100
- Name: car.cadillac.inj
  Line: 137
  Type: definition
  Uses: [true, car.cadillac, car, eq]
  Size: 58
- Name: bee.queen.inj_eq
  Line: 80
  Type: definition
  Uses: [true, bee.queen, bee, eq]
  Size: 203
- Name: bee.queen.sizeof_spec
  Line: 80
  Type: definition
  Uses: [nat.has_one, has_one.one, bee.queen, bee.sizeof, nat, eq]
  Size: 38
- Name: car.cadillac.inj_arrow
  Line: 137
  Type: definition
  Uses: [true, car.cadillac, car, eq]
  Size: 109
- Name: bee.drone.inj
  Line: 80
  Type: definition
  Uses: [true, bee.drone, bee, eq]
  Size: 52
- Name: car.cadillac.sizeof_spec
  Line: 137
  Type: definition
  Uses: [nat.has_one, has_one.one, car.cadillac, car.sizeof, nat, eq]
  Size: 41
- Name: car.sum_size_zero
  Line: 211
  Type: theorem
  Statement uses: [list.nil, nat.has_zero, has_zero.zero, car.sum_size, nat, eq, car, list]
  Size: 141
  Proof uses lemmas: [car.sum_size_cons, add_eq_zero_iff, propext, eq.refl, and.right, car.car_size_ne_zero, rfl]
  and uses: [add_monoid.to_add_semigroup, add_semigroup.to_has_add, eq.rec, and, nat.has_add, has_add.add, eq.mp, car.size, nat.canonically_ordered_comm_semiring, canonically_ordered_comm_semiring.to_canonically_ordered_monoid, canonically_ordered_monoid.to_ordered_comm_monoid, ordered_comm_monoid.to_add_comm_monoid, add_comm_monoid.to_add_monoid, add_monoid.to_has_zero, false.rec, list.cons, id_rhs, list.nil, list.cases_on, nat.has_zero, has_zero.zero, car.sum_size, nat, eq, car, list]
  Proof size: 6508
- Name: bee.drone.inj_eq
  Line: 80
  Type: definition
  Uses: [true, bee.drone, bee, eq]
  Size: 203
- Name: car.has_repr
  Line: 143
  Type: instance
  Target: has_repr.{0}
  Uses: [car, has_repr]
  Size: 62
- Name: car.all_packings
  Line: 238
  Type: theorem
  Statement uses: [car.packings, list.has_mem, has_mem.mem, car.sum_size, eq, car, list, nat]
  Size: 185
  Proof uses lemmas: [false_or, or_false, exists_false, iff_false_intro, and_false, false_and, eq_false_intro, true.intro, car.sum_size_cons, add_right_inj, iff.refl, iff.mpr, iff_true_intro, exists_eq_right, true_and, funext, list.mem_map, list.mem_append, car.packings.equations._eqn_3, eq.refl, and_self, list.cons.inj_eq, car.packings.equations._eqn_2, car.sum_size_one, trivial, eq_self_iff_true, list.mem_singleton, propext, car.packings.equations._eqn_1, car.sum_size_zero, congr_arg, congr, eq.trans]
  and uses: [pprod.snd, car.no_confusion, nat.ordered_semiring, ordered_semiring.to_ordered_cancel_comm_monoid, ordered_cancel_comm_monoid.to_add_right_cancel_semigroup, add_right_cancel_semigroup.to_add_semigroup, add_semigroup.to_has_add, car.size, eq.mp, iff, eq.rec, pprod, punit, nat.rec, nat.add, pprod.fst, Exists, list.has_append, has_append.append, car.cadillac, list.map, false, or, car.cases_on, nat.no_confusion, bit0, nat.has_add, has_add.add, nat.no_confusion_type, list.cases_on, car.rabbit, and, nat.has_one, has_one.one, nat.succ, has_mem, list.cons, list.nil, id, true, eq.mpr, nat.has_zero, has_zero.zero, id_rhs, nat.zero, nat.cases_on, nat.below, car.packings, list.has_mem, has_mem.mem, nat.brec_on, car.sum_size, eq, car, list, nat]
  Proof size: 59126
- Name: bee.tree_json
  Line: 105
  Type: definition
  Uses: [string, nat, bee]
  Size: 19
- Name: bee.queen.inj_arrow
  Line: 80
  Type: definition
  Uses: [true, bee.queen, bee, eq]
  Size: 100
- Name: fibonacci
  Line: 6
  Type: definition
  Uses: [nat]
  Size: 15
- Name: fib_even_sum
  Line: 22
  Type: definition
  Uses: [nat]
  Size: 224
- Name: bee.drone_ancestors_concat
  Line: 110
  Type: theorem
  Statement uses: [list.has_append, has_append.append, nat.has_one, has_one.one, bit0, nat.has_add, has_add.add, bee.drone, bee.ancestors, bee, list, eq, nat]
  Size: 349
  Proof uses lemmas: [list.join_append, list.map_append, eq.refl, eq.trans, congr_arg, congr, rfl]
  and uses: [pprod, punit, nat.rec, nat.add, pprod.fst, eq.rec, bee.parents, list.map, list.join, eq.mpr, id, nat.succ, nat.has_zero, has_zero.zero, id_rhs, nat.zero, nat.cases_on, nat.below, list.has_append, has_append.append, nat.has_one, has_one.one, bit0, nat.has_add, has_add.add, bee.drone, bee.ancestors, bee, list, eq, nat.brec_on, nat]
  Proof size: 19760
- Name: car.rabbit.sizeof_spec
  Line: 137
  Type: definition
  Uses: [nat.has_one, has_one.one, car.rabbit, car.sizeof, nat, eq]
  Size: 39
- Name: bee.worker.sizeof_spec
  Line: 80
  Type: definition
  Uses: [nat.has_one, has_one.one, bee.worker, bee.sizeof, nat, eq]
  Size: 39
- Name: fib_odd_sum_eq
  Line: 25
  Type: theorem
  Statement uses: [nat.has_one, has_one.one, nat.has_add, bit0, nat.has_mul, has_mul.mul, fibonacci, fib_odd_sum, eq, nat]
  Size: 151
  Proof uses lemmas: [fibonacci.equations._eqn_3, mul_one, mul_add, eq.symm, list.sum_range_succ, fib_odd_sum.equations._eqn_1, eq.refl, rfl]
  and uses: [monoid.to_has_one, nat.monoid, monoid.to_semigroup, semigroup.to_has_mul, distrib.to_has_mul, nat.distrib, distrib.to_has_add, pprod, punit, nat.rec, nat.add, pprod.fst, add_monoid.to_has_zero, nat.add_monoid, add_monoid.to_add_semigroup, add_semigroup.to_has_add, eq.rec, id, list.range, list.map, list.sum, eq.mpr, has_add.add, nat.succ, nat.has_zero, has_zero.zero, id_rhs, nat.zero, nat.cases_on, nat.below, nat.has_one, has_one.one, nat.has_add, bit0, nat.has_mul, has_mul.mul, fibonacci, fib_odd_sum, eq, nat.brec_on, nat]
  Proof size: 37244
- Name: car.cases_on
  Line: 137
  Type: definition
  Uses: [car.cadillac, car.rabbit, car]
  Size: 106
- Name: bee.ancestors
  Line: 101
  Type: definition
  Uses: [list, nat, bee]
  Size: 38
- Name: bee.queen.inj
  Line: 80
  Type: definition
  Uses: [true, bee.queen, bee, eq]
  Size: 52
- Name: fib_sum_eq
  Line: 59
  Type: theorem
  Statement uses: [fibonacci, nat.has_one, has_one.one, fib_sum, nat.has_add, has_add.add, eq, nat]
  Size: 188
  Proof uses lemmas: [trivial, eq_self_iff_true, add_right_inj, propext, add_left_comm, add_comm, add_zero, list.sum_nil, list.sum_cons, list.sum_append, list.map.equations._eqn_1, list.map.equations._eqn_2, list.map_append, list.range_concat, fib_sum.equations._eqn_1, congr_arg, congr, eq.trans, eq.symm, fibonacci.equations._eqn_3, eq.refl, rfl]
  and uses: [nat.ordered_semiring, ordered_semiring.to_ordered_cancel_comm_monoid, ordered_cancel_comm_monoid.to_add_right_cancel_semigroup, add_right_cancel_semigroup.to_add_semigroup, has_append, has_zero, list.has_append, list, has_append.append, list.nil, list.cons, add_monoid.to_has_zero, nat.add_monoid, add_monoid.to_add_semigroup, has_add, nat.add_comm_semigroup, add_comm_semigroup.to_add_semigroup, add_semigroup.to_has_add, list.range, list.map, list.sum, true, pprod, punit, nat.rec, nat.add, pprod.fst, bit0, eq.rec, id, eq.mpr, nat.succ, nat.has_zero, has_zero.zero, id_rhs, nat.zero, nat.cases_on, nat.below, fibonacci, nat.has_one, has_one.one, fib_sum, nat.has_add, has_add.add, eq, nat.brec_on, nat]
  Proof size: 25798
- Name: bee.has_repr
  Line: 87
  Type: instance
  Target: has_repr.{0}
  Uses: [bee, has_repr]
  Size: 62
- Name: car.num_packings_eq_fib
  Line: 171
  Type: theorem
  Statement uses: [nat.has_one, has_one.one, nat.has_add, has_add.add, fibonacci, car.packings, car, list, list.length, eq, nat]
  Size: 158
  Proof uses lemmas: [add_left_inj, propext, eq.refl, fibonacci.equations._eqn_3, add_zero, add_left_comm, add_comm, list.length_map, list.length_append, car.packings.equations._eqn_3, eq.trans, congr_arg, congr, rfl]
  and uses: [nat.ordered_semiring, ordered_semiring.to_ordered_cancel_comm_monoid, ordered_cancel_comm_monoid.to_add_left_cancel_semigroup, add_left_cancel_semigroup.to_add_semigroup, pprod.snd, pprod, punit, nat.rec, nat.add, pprod.fst, eq.rec, nat.add_monoid, bit1, has_add, list.has_append, has_append.append, car.cadillac, car.rabbit, list.cons, list.map, nat.add_comm_semigroup, add_comm_semigroup.to_add_semigroup, add_semigroup.to_has_add, id, eq.mpr, bit0, nat.succ, nat.has_zero, has_zero.zero, id_rhs, nat.zero, nat.cases_on, nat.below, nat.has_one, has_one.one, nat.has_add, has_add.add, fibonacci, car.packings, car, list, list.length, eq, nat.brec_on, nat]
  Proof size: 40164
- Name: car.no_confusion_type
  Line: 137
  Type: definition
  Uses: [car]
  Size: 225
- Name: bee.worker.inj_arrow
  Line: 80
  Type: definition
  Uses: [true, bee.worker, bee, eq]
  Size: 103
- Name: fib_sum
  Line: 14
  Type: definition
  Uses: [nat]
  Size: 108
- Name: car.rabbit.inj_eq
  Line: 137
  Type: definition
  Uses: [true, car.rabbit, car, eq]
  Size: 211
- Name: bee.cases_on
  Line: 80
  Type: definition
  Uses: [bee.drone, bee.worker, bee.queen, bee]
  Size: 127
- Name: bee.drone_ancestors_length_eq_fib_succ
  Line: 122
  Type: theorem
  Statement uses: [nat.has_one, has_one.one, nat.has_add, has_add.add, fibonacci, bee.drone, bee.ancestors, bee, list.length, eq, nat]
  Size: 158
  Proof uses lemmas: [add_comm, list.length_append, bee.drone_ancestors_concat, eq.refl, rfl]
  and uses: [nat.add_comm_semigroup, add_comm_semigroup.to_add_semigroup, add_semigroup.to_has_add, pprod.snd, pprod, punit, nat.rec, nat.add, pprod.fst, eq.rec, id, list.has_append, list, has_append.append, eq.mpr, bit0, nat.succ, nat.has_zero, has_zero.zero, id_rhs, nat.zero, nat.cases_on, nat.below, nat.has_one, has_one.one, nat.has_add, has_add.add, fibonacci, bee.drone, bee.ancestors, bee, list.length, eq, nat.brec_on, nat]
  Proof size: 23833
- Name: fib_odd_sum
  Line: 18
  Type: definition
  Uses: [nat]
  Size: 292
- Name: bee.parents
  Line: 96
  Type: definition
  Uses: [list, bee]
  Size: 17
- Name: car.rec_on
  Line: 137
  Type: definition
  Uses: [car.cadillac, car.rabbit, car]
  Size: 106
- Name: bee.has_sizeof_inst
  Line: 80
  Type: instance
  Target: has_sizeof.{1}
  Uses: [bee, has_sizeof]
  Size: 32
- Name: car.no_confusion
  Line: 137
  Type: definition
  Uses: [car.no_confusion_type, eq, car]
  Size: 316
- Name: car.car_size_ne_zero
  Line: 208
  Type: theorem
  Statement uses: [nat.has_zero, has_zero.zero, car.size, nat, ne, car]
  Size: 76
  Proof uses lemmas: []
  and uses: [car.cadillac, false, nat.no_confusion, eq, car.rabbit, id, nat.has_zero, has_zero.zero, car.size, nat, ne, car.cases_on, car]
  Proof size: 629
- Name: bee.drone.sizeof_spec
  Line: 80
  Type: definition
  Uses: [nat.has_one, has_one.one, bee.drone, bee.sizeof, nat, eq]
  Size: 38
- Name: car.packings
  Line: 165
  Type: definition
  Uses: [car, list, nat]
  Size: 18
- Name: car.sum_size_one
  Line: 222
  Type: theorem
  Statement uses: [list.nil, car.rabbit, list.cons, nat.has_one, has_one.one, car.sum_size, nat, eq, car, list]
  Size: 169
  Proof uses lemmas: [car.sum_size_cons, nat.succ_inj, car.sum_size_zero, true_and, eq.refl, eq_self_iff_true, propext, congr_arg, congr, list.cons.inj_eq, eq.trans]
  and uses: [car.cadillac, eq.rec, car.size, nat.has_add, has_add.add, eq.mp, nat.has_zero, has_zero.zero, true, and, id, eq.mpr, car.cases_on, nat.no_confusion, nat.no_confusion_type, id_rhs, list.nil, car.rabbit, list.cons, list.cases_on, nat.has_one, has_one.one, car.sum_size, nat, eq, car, list]
  Proof size: 5394
- Name: car.sizeof
  Line: 137
  Type: definition
  Uses: [nat, car]
  Size: 100
- Name: car
  Line: 137
  Type: inductive
  Size: 4
- Name: bee.no_confusion
  Line: 80
  Type: definition
  Uses: [bee.no_confusion_type, eq, bee]
  Size: 333
- Name: car.has_sizeof_inst
  Line: 137
  Type: instance
  Target: has_sizeof.{1}
  Uses: [car, has_sizeof]
  Size: 32

-/
