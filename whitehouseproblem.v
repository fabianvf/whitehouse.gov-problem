(*
Alice and Bob are playing a game.  They are teammates, so
they will win or lose together.  Before the game starts,
they can talk to each other and agree on a strategy.

When the game starts, Alice and Bob go into separate soundproof
rooms – they cannot communicate with each other in any way.
They each flip a coin and note whether it came up Heads or Tails.
(No funny business allowed – it has to be an honest coin flip and
they have to tell the truth later about how it came out.)  Now
Alice writes down a guess as to the result of Bob’s coin flip;
and Bob likewise writes down a guess as to Alice’s flip.

If either or both of the written-down guesses turns out to be
correct, then Alice and Bob both win as a team.  But if both
written-down guesses are wrong, then they both lose.

The puzzle is this: Can you think of a strategy Alice and Bob
can use that is guaranteed to win every time?
*)

Inductive Flip: Set :=
  | heads
  | tails.

Definition flip_eq (f1: Flip) (f2: Flip): bool :=
  match f1, f2 with
    | heads, heads | tails, tails => true
    | _, _ => false
  end.

Definition Strategy := Flip -> Flip.

Inductive Person: Set :=
  person: Strategy -> Flip -> Person.

Definition identity (f: Flip): Flip :=
  f.

Definition opposite (f: Flip): Flip :=
  match f with
    | heads => tails
    | tails => heads
  end.

Definition Alice := person identity.
Definition Bob := person opposite.

Definition success (p1: Person) (p2: Person): Prop :=
  match p1, p2 with
    | person s1 f1, person s2 f2 =>
        if orb (flip_eq (s1 f1) f2) (flip_eq (s2 f2) f1) then True
        else False
  end.

Theorem solution: forall (f1 f2: Flip),
(success (Alice f1) (Bob f2)).
Proof. intros. destruct f1. destruct f2.
reflexivity. reflexivity. destruct f2.
reflexivity. reflexivity.
Qed.
