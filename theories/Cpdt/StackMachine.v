From Coq Require Import Bool Arith List.
From Bits.Cpdt Require Import Base.

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
    Inductive t : Set :=
    | Const : nat -> t
    | Binop : Binop.t -> t.

    Definition denote (i : t) (s : stack) : option stack :=
      match i with
      | Const n => Some (n :: s)
      | Binop b =>
          match s with
          | x :: y :: s' => Some ((Binop.denote b) x y :: s')
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
      Import List.ListNotations.

      Definition const := Const 42.
      Definition plus := Binop Binop.Plus (Const 2) (Const 2).
      Definition nested := Binop Binop.Times plus (Const 7).

      Example denote_const :
        denote const = 42.
      reflexivity. Qed.

      Example denote_plus :
        denote plus = 4.
      reflexivity. Qed.

      Example denote_nested :
        denote nested = 28.
      reflexivity. Qed.

      Example compile_const :
        compile const = [Instr.Const 42].
      reflexivity. Qed.

      Example compile_plus :
        compile plus = [Instr.Const 2; Instr.Const 2; Instr.Binop Binop.Plus].
      reflexivity. Qed.

      Example compile_nested :
        compile nested = [Instr.Const 7; Instr.Const 2; Instr.Const 2; Instr.Binop Binop.Plus; Instr.Binop Binop.Times].
      reflexivity. Qed.

      Example denote_compile_const :
        Prog.denote (compile const) [] = Some [42].
      reflexivity. Qed.

      Example denote_compile_plus :
        Prog.denote (compile plus) [] = Some [4].
      reflexivity. Qed.

      Example denote_compile_nested :
        Prog.denote (compile nested) [] = Some [28].
      reflexivity. Qed.
    End Examples.

    Lemma compile_correct' :
      forall (e : t) (p : Prog.t) (s : stack),
        Prog.denote (compile e ++ p) s = Prog.denote p (denote e :: s).
    Proof.
      induction e.
      - simpl.
        reflexivity.
      - intros.
        simpl.
        rewrite app_assoc_reverse.
        rewrite IHe2.
        rewrite app_assoc_reverse.
        rewrite IHe1.
        reflexivity.
    Qed.

    Lemma compile_correct'':
      forall (e : t) (p : Prog.t) (s : stack),
        Prog.denote (compile e ++ p) s = Prog.denote p (denote e :: s).
    Proof.
      induction e.
      - simpl.
        reflexivity.
      - intros.
        simpl.
        repeat rewrite app_assoc_reverse.
        repeat rewrite IHe2.
        repeat rewrite IHe1.
        reflexivity.
    Qed.

    Theorem compile_correct :
      forall (e : t),
        Prog.denote (compile e) nil = Some (denote e :: nil).
    Proof.
      intros.
      rewrite (app_nil_end (compile e)).
      rewrite compile_correct'.
      reflexivity.
    Qed.
  End Exp.
End Untyped.

Module Typed.
  Set Implicit Arguments.

  Module Ty.
    Inductive t : Set :=
    | Nat
    | Bool.

    Definition denote (ty : t) : Set :=
      match ty with
      | Nat => nat
      | Bool => bool
      end.
  End Ty.

  Module Binop.
    Inductive t : Ty.t -> Ty.t -> Ty.t -> Set :=
    | Plus : t Ty.Nat Ty.Nat Ty.Nat
    | Times : t Ty.Nat Ty.Nat Ty.Nat
    | Eq : forall a, t a a Ty.Bool
    | Lt : t Ty.Nat Ty.Nat Ty.Bool.

    Definition denote {x y r : Ty.t} (b : t x y r) : Ty.denote x -> Ty.denote y -> Ty.denote r :=
      match b with
      | Plus => plus
      | Times => mult
      | Eq Ty.Nat => Nat.eqb
      | Eq Ty.Bool => eqb
      | Lt => leb
      end.
  End Binop.

  Definition tstack := list Ty.t.

  Fixpoint vstack (ts : tstack) : Set :=
    match ts with
    | nil => unit
    | t :: ts' => Ty.denote t * vstack ts'
    end%type.

  Module Instr.
    Inductive t : tstack -> tstack -> Set :=
    | NConst : forall s, nat -> t s (Ty.Nat :: s)
    | BConst : forall s, bool -> t s (Ty.Bool :: s)
    | Binop : forall x y r s, Binop.t x y r -> t (x :: y :: s) (r :: s).

    Definition denote {a b : tstack} (i : t a b) : vstack a -> vstack b :=
      match i with
      | NConst _ n => fun s => (n, s)
      | BConst _ b => fun s => (b, s)
      | Binop _ b => fun s =>
                       let '(x, (y, s')) := s in
                       ((Binop.denote b) x y, s')
      end.
  End Instr.

  Module Prog.
    Inductive t : tstack -> tstack -> Set :=
    | Nil : forall a, t a a
    | Cons : forall a b c, Instr.t a b -> t b c -> t a c.

    Fixpoint denote {a b : tstack} (p : t a b) : vstack a -> vstack b :=
      match p with
      | Nil _ => fun s => s
      | Cons i p' => fun s => denote p' (Instr.denote i s)
      end.

    Fixpoint concat {a b c : tstack} (p : t a b) : t b c -> t a c :=
      match p with
      | Nil _ => fun q => q
      | Cons i p' => fun q => Cons i (concat p' q)
      end.

    Lemma concat_correct :
      forall (a b c : tstack) (p : Prog.t a b) (q : Prog.t b c) (s : vstack a),
        Prog.denote (Prog.concat p q) s = Prog.denote q (Prog.denote p s).
    Proof.
      induction p.
      - simpl.
        reflexivity.
      - intros.
        simpl.
        rewrite IHp.
        reflexivity.
    Qed.
  End Prog.

  Module Exp.
    Inductive t : Ty.t -> Set :=
    | NConst : nat -> t Ty.Nat
    | BConst : bool ->  t Ty.Bool
    | Binop : forall x y r, Binop.t x y r -> t x -> t y -> t r.

    Fixpoint denote {x : Ty.t} (e : t x) : Ty.denote x :=
      match e with
      | NConst n => n
      | BConst b => b
      | Binop b e1 e2 => (Binop.denote b) (denote e1) (denote e2)
      end.

    Fixpoint compile {x : Ty.t} (e : t x) (ts : tstack) : Prog.t ts (x :: ts) :=
      match e with
      | NConst n => Prog.Cons (Instr.NConst _ n) (Prog.Nil _)
      | BConst b => Prog.Cons (Instr.BConst _ b) (Prog.Nil _)
      | Binop b e1 e2 =>
          Prog.concat
            (compile e2 _)
            (Prog.concat
               (compile e1 _)
               (Prog.Cons (Instr.Binop _ b) (Prog.Nil _)))
      end.

    Section Examples.
      Definition nconst := NConst 42.
      Definition bconst := BConst false.
      Definition plus := Binop Binop.Plus (NConst 2) (NConst 2).
      Definition nested := Binop Binop.Times plus (NConst 7).
      Definition nested_eq := Binop (Binop.Eq Ty.Nat) plus (NConst 7).
      Definition nested_lt := Binop Binop.Lt plus (NConst 7).

      Example denote_nconst :
        denote nconst = 42.
      reflexivity. Qed.

      Example denote_bconst :
        denote bconst = false.
      reflexivity. Qed.

      Example denote_nested :
        denote nested = 28.
      reflexivity. Qed.

      Example denote_nested_eq :
        denote nested_eq = false.
      reflexivity. Qed.

      Example denote_nested_lt :
        denote nested_lt = true.
      reflexivity. Qed.

      Eval simpl in compile nconst nil.

      Eval simpl in compile bconst nil.

      Eval simpl in compile nested nil.

      Eval simpl in compile nested_eq nil.

      Eval simpl in compile nested_lt nil.

      Example denote_compile_nconst :
        Prog.denote (compile nconst nil) tt = (42, tt).
      reflexivity. Qed.

      Example denote_compile_bconst :
        Prog.denote (compile bconst nil) tt = (false, tt).
      reflexivity. Qed.

      Example denote_compile_nested :
        Prog.denote (compile nested nil) tt = (28, tt).
      reflexivity. Qed.

      Example denote_compile_nested_eq :
        Prog.denote (compile nested_eq nil) tt = (false, tt).
      reflexivity. Qed.

      Example denote_compile_nested_lt :
        Prog.denote (compile nested_lt nil) tt = (true, tt).
      reflexivity. Qed.
    End Examples.

    Lemma compile_correct' :
      forall (x : Ty.t) (e : t x) (ts : tstack) (s : vstack ts),
        Prog.denote (compile e ts) s = (Exp.denote e, s).
    Proof.
      induction e.
      - simpl.
        reflexivity.
      - simpl.
        reflexivity.
      - intros.
        simpl.
        repeat rewrite Prog.concat_correct.
        repeat rewrite IHe2.
        repeat rewrite IHe1.
        reflexivity.
    Qed.

    Theorem compile_correct :
      forall (x : Ty.t) (e : t x),
        Prog.denote (compile e nil) tt = (Exp.denote e, tt).
    Proof.
      intros.
      simpl.
      rewrite compile_correct'.
      reflexivity.
    Qed.
  End Exp.
End Typed.
