open nat
open prop

-- A datatype Nat
-- (nat is a builtin)
inductive Nat : Type
| my_zero : Nat
| my_succ : Nat → Nat

-- a definition on nat
definition double : nat -> nat
| zero := zero
| (succ n) := (succ (succ (double n)))

#check double

-- an inductive property on nats
inductive even : nat -> Prop
| evenZ : even zero
| evenS : forall x, even x -> even (succ (succ x))

-- a proof that doubling produces even numbers
definition even_proof : ∀ (x : nat), (even (double x))
| zero := even.evenZ
| (succ n) := even.evenS (double n) (even_proof n)

-- another proof
definition even_proof2 : ∀ (n: nat), (even (double n)) :=
begin
  intro n,
  induction n,
  {
    exact even.evenZ
  },
  {
    constructor,
    exact n_ih
  }
end

-- or another proof
def even_proof3 : ∀ (n : ℕ), even (double n) :=
λ (n : ℕ), 
  nat.rec 
    -- base case
    even.evenZ 
    -- inductive case
    (λ (n_n : ℕ) (n_ih : even (double n_n)), even.evenS (double n_n) n_ih) 
    -- variable to induct on
    n

