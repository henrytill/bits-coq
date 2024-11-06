Inductive expr : Type :=
| ValE : nat -> expr
| AddE : expr -> expr -> expr.
