Require Import List.
Import List.ListNotations.

Lemma app_assoc_reverse {A : Type} (l m n : list A) :
  (l ++ m) ++ n = l ++ m ++ n.
Proof. symmetry. apply app_assoc. Qed.

Theorem app_nil_end {A : Type} (l : list A) : l = l ++ [].
Proof. symmetry; apply app_nil_r. Qed.
