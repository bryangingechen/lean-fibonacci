import data.list.range

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
  simp [range_concat, fib_sum,
    add_left_comm, add_comm],
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
---
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
  simp [packings, fibonacci, add_left_comm, add_comm],
  rw [num_packings_eq_fib n,
    num_packings_eq_fib (n+1),
    add_left_comm,
    add_right_inj,
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
  exact sum_size_zero (succ.inj h),
end
| (cadillac::cs) h :=
begin
  rw [sum_size_cons] at h,
  have : sum_size cs + 1 = 0 := succ.inj h,
  contradiction,
end
---
theorem all_packings : ∀ {n : ℕ} {cs : list car} (h : sum_size cs = n),
  cs ∈ packings n
| 0 cs h := by simp [packings, sum_size_zero h]
| 1 cs h := by simp [packings, sum_size_one h]
| (n+2) [] h := by contradiction
| (n+2) (rabbit::cs) h :=
begin
  rw [sum_size_cons,
    add_left_inj 1] at h,
  simp [packings, all_packings, h],
end
| (n+2) (cadillac::cs) h :=
begin
  rw [sum_size_cons,
    add_left_inj 2] at h,
  simp [packings, all_packings, h],
end

end car
