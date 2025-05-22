import Mathlib

variable {α β : Type} [DecidableEq α]

@[simp]
def dom : List (α × β) → Finset α := λ xs ↦ xs.map Prod.fst |>.toFinset

inductive Ok : List (α × β) → Prop
| nil : Ok []
| cons (xs : List (α × β)) (a : α) (b : β) : Ok xs → a ∉ dom xs → Ok ((a,b) :: xs)

theorem List.perm_dom  {xs ys : List (α × β)} (h : xs.Perm ys) (a : α) : a ∉ dom xs → a ∉ dom ys := by 
  induction h <;> aesop

theorem Ok.perm  {xs ys : List (α × β)} (h : xs.Perm ys) : Ok xs → Ok ys := by
  induction h <;> intros ok_xs
  case nil => exact Ok.nil
  case cons pair xs' ys' perm ih =>
    cases ok_xs
    case cons a b ok_xs' mem =>
      observe ok_ys' : Ok ys'
      constructor
      exact ih ok_xs'
      exact List.perm_dom perm a mem
  case swap p1 p2 xs' =>
    cases ok_xs
    case cons a1 b1 ok_xs dom_a1 =>
    cases ok_xs
    case cons a2 b2 ok_xs dom_a2 =>
      constructor
      constructor
      exact ok_xs
      aesop
      aesop
  case trans a b c p_ab p_bc ih_ab ih_bc => exact ih_bc (ih_ab ok_xs)

