Inductive expr : Type :=
| Val : nat -> expr
| Add : expr -> expr -> expr
| Sub : expr -> expr -> expr.
