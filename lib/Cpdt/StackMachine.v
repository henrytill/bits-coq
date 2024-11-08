From Coq Require Import Bool Arith List.
Import List.ListNotations.

Module Untyped.
  Definition stack := list nat.

  Module Binop.
    Inductive t : Set :=
    | Plus
    | Times.

    Definition denote (b : t) : nat -> nat -> nat :=
      match b with
      | Plus => plus
      | Times => mult
      end.
  End Binop.

  Module Instr.
    Inductive t  : Set :=
    | Const : nat -> t
    | Binop : Binop.t -> t.

    Definition denote (i : t) (s : stack) : option stack :=
      match i with
      | Const n => Some (n :: s)
      | Binop b =>
          match s with
          | arg1 :: arg2 :: s' => Some ((Binop.denote b) arg1 arg2 :: s')
          | _ => None
          end
      end.
  End Instr.

  Module Prog.
    Definition t := list Instr.t.

    Fixpoint denote (p : t) (s : stack) : option stack :=
      match p with
      | nil => Some s
      | i :: p' =>
          match Instr.denote i s with
          | None => None
          | Some s' => denote p' s'
          end
      end.
  End Prog.

  Module Exp.
    Inductive t : Set :=
    | Const : nat -> t
    | Binop : Binop.t -> t -> t -> t.

    Fixpoint denote (e : t) : nat :=
      match e with
      | Const n => n
      | Binop b e1 e2 => (Binop.denote b) (denote e1) (denote e2)
      end.

    Fixpoint compile (e : t) : Prog.t :=
      match e with
      | Const n => Instr.Const n :: nil
      | Binop b e1 e2 => compile e2 ++ compile e1 ++ Instr.Binop b :: nil
      end.

    Section Examples.
      Example denote_const :
        denote (Const 42) = 42.
      auto. Qed.

      Example denote_plus :
        denote (Binop Binop.Plus (Const 2) (Const 2)) = 4.
      auto. Qed.

      Example denote_nested :
        denote (Binop Binop.Times (Binop Binop.Plus (Const 2) (Const 2)) (Const 7)) = 28.
      auto. Qed.

      Example compile_const :
        compile (Const 42) = [Instr.Const 42].
      auto. Qed.

      Example compile_plus :
        compile (Binop Binop.Plus (Const 2) (Const 2)) =
          [Instr.Const 2; Instr.Const 2; Instr.Binop Binop.Plus].
      auto. Qed.

      Example compile_nested :
        compile (Binop Binop.Times (Binop Binop.Plus (Const 2) (Const 2)) (Const 7)) =
          [Instr.Const 7; Instr.Const 2; Instr.Const 2; Instr.Binop Binop.Plus; Instr.Binop Binop.Times].
      auto. Qed.

      Example denote_compile_const :
        Prog.denote (compile (Const 42)) [] = Some [42].
      auto. Qed.

      Example denote_compile_plus :
        Prog.denote (compile (Binop Binop.Plus (Const 2) (Const 2))) [] = Some [4].
      auto. Qed.

      Example denote_compile_nested :
        Prog.denote (compile (Binop Binop.Times (Binop Binop.Plus (Const 2) (Const 2)) (Const 7))) [] = Some [28].
      auto. Qed.
    End Examples.

    Lemma app_assoc_reverse {A : Type} (l m n : list A) :
      (l ++ m) ++ n = l ++ m ++ n.
    Proof. symmetry. apply app_assoc. Qed.

    Lemma compile_correct' : forall e p s,
        Prog.denote (compile e ++ p) s = Prog.denote p (denote e :: s).
    Proof.
      induction e.
      - intros.
        unfold compile.
        unfold denote.
        unfold Prog.denote at 1.
        simpl.
        fold Prog.denote.
        reflexivity.
      - intros.
        unfold compile.
        fold compile.
        unfold denote.
        fold denote.
        rewrite app_assoc_reverse.
        rewrite IHe2.
        rewrite app_assoc_reverse.
        rewrite IHe1.
        unfold Prog.denote at 1.
        simpl.
        fold Prog.denote.
        reflexivity.
    Qed.

    Theorem app_nil_end {A : Type} (l : list A) : l = l ++ [].
    Proof. symmetry; apply app_nil_r. Qed.

    Theorem compile_correct : forall e,
        Prog.denote (compile e) nil = Some (denote e :: nil).
    Proof.
      intros.
      rewrite (app_nil_end (compile e)).
      rewrite compile_correct'.
      reflexivity.
    Qed.
  End Exp.
End Untyped.
