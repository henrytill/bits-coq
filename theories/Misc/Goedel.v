(* https://cstheory.stackexchange.com/a/20582 *)

From Stdlib Require Import Arith.

Inductive type : Type :=
| Nat : type
| Unit : type
| Arrow : type -> type -> type.

Fixpoint type_denote (ty : type) : Type :=
  match ty with
  | Nat => nat
  | Unit => unit
  | Arrow a b => type_denote a -> type_denote b
  end%type.

Notation "a ~> b" := (Arrow a b) (at level 60, right associativity).

Inductive term : type -> Type :=
| Zero : term Nat
| Succ : term (Nat ~> Nat)
| Const a b : term (a ~> b ~> a)
| Fork a b c : term ((a ~> b ~> c) ~> (a ~> b) ~> (a ~> c))
| Iter a : term (a ~> (a ~> a) ~> Nat ~> a)
| App a b : term (a ~> b) -> term a -> term b.

Check Fork.

Fixpoint iter (a : type) (base : type_denote a) (step : type_denote a -> type_denote a) (n : nat) : type_denote a :=
  match n with
  | O => base
  | S n' => step (iter a base step n')
  end.

Fixpoint term_denote {a : type} (tm : term a) : type_denote a :=
  match tm with
  | Zero => O
  | Succ => fun n => S n
  | Const _ _ => fun x y => x
  | Fork _ _ _ => fun f g x => f x (g x)
  | Iter _ => iter _
  | App _ _ f x => (term_denote f) (term_denote x)
  end.

Arguments Const {a b}.
Arguments Fork {a b c}.
Arguments Iter {a}.
Arguments App {a b}.

Section Tests.
  Let tm_1 := App Succ Zero.
  Let tm_2 := App Succ tm_1.
  Let tm_3 := App Succ tm_2.
  Let tm_5 := App Succ (App Succ tm_3).

  Let denote_tm_1 : term_denote tm_1 = 1 := eq_refl.
  Let denote_tm_2 : term_denote tm_2 = 2 := eq_refl.
  Let denote_tm_3 : term_denote tm_3 = 3 := eq_refl.
  Let denote_tm_5 : term_denote tm_5 = 5 := eq_refl.

  Check App Iter tm_5.
  Check App (App Iter tm_5) Succ.
  Check App (App (App Iter tm_5) Succ) tm_3.

  Let iter_8 := App (App (App Iter tm_5) Succ) tm_3.
  Let denote_iter_8 : term_denote iter_8 = 8 := eq_refl.
End Tests.
