From Coq Require Import Arith List String.
From Bits.Machine Require Lexer Parser.
Import Parser.MenhirLibParser.Inter.
Import List.ListNotations.

Open Scope string_scope.

Inductive op : Type :=
| PUSH : nat -> op
| ADD : op
| SUB : op.

Fixpoint eval (e : Syntax.expr) : nat :=
  match e with
  | Syntax.Val n => n
  | Syntax.Add e1 e2 => eval e1 + eval e2
  | Syntax.Sub e1 e2 => eval e1 - eval e2
  end.

Definition stack := list nat.
Definition code := list op.

Fixpoint exec (c : code) (s : stack) : stack :=
  match c, s with
  | [], s' => s'
  | (PUSH n :: c'), s' => exec c' (n :: s')
  | (ADD :: c'), (m :: n :: s') => exec c' ((n + m) :: s')
  | (SUB :: c'), (m :: n :: s') => exec c' ((n - m) :: s')
  | (ADD :: _), _ => []
  | (SUB :: _), _ => []
  end.

Fixpoint compile' (e : Syntax.expr) (c : code) : code :=
  match e with
  | Syntax.Val n => PUSH n :: c
  | Syntax.Add e1 e2 => compile' e1 (compile' e2 (ADD :: c))
  | Syntax.Sub e1 e2 => compile' e1 (compile' e2 (SUB :: c))
  end.

Definition compile (e : Syntax.expr) : code := compile' e [].

Lemma compile'_exec_eval :
  forall e c s, exec (compile' e c) s = exec c (eval e :: s).
Proof.
  intros e.
  induction e; intros c s.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    reflexivity.
  - simpl.
    rewrite IHe1.
    rewrite IHe2.
    simpl.
    reflexivity.
Qed.

Theorem compile_exec_eval :
  forall e, exec (compile e) [] = [eval e].
Proof.
  intros e.
  unfold compile.
  rewrite compile'_exec_eval.
  simpl.
  reflexivity.
Qed.

Section Tests.
  Let _test_compile_val : compile (Syntax.Val 5) = [PUSH 5] := eq_refl.
  Let _test_compile_add : compile (Syntax.Add (Syntax.Val 3) (Syntax.Val 4)) = [PUSH 3; PUSH 4; ADD] := eq_refl.
  Let _test_compile_sub : compile (Syntax.Sub (Syntax.Val 4) (Syntax.Val 3)) = [PUSH 4; PUSH 3; SUB] := eq_refl.

  Let _test_exec_compile_val : exec (compile (Syntax.Val 5)) [] = [5] := eq_refl.
  Let _test_exec_compile_add : exec (compile (Syntax.Add (Syntax.Val 3) (Syntax.Val 4))) [] = [7] := eq_refl.
  Let _test_exec_compile_sub : exec (compile (Syntax.Sub (Syntax.Val 4) (Syntax.Val 3))) [] = [1] := eq_refl.
End Tests.

Definition parse_string s :=
  match option_map (Parser.parse_expr 50) (Lexer.lex_string s) with
  | Some (Parsed_pr f _) => Some f
  | _ => None
  end.

Definition example := "(1 + (2 + (3 + (4 + 5))))".

Definition example_ops := option_map compile (parse_string example).

Compute example_ops.

Compute option_map (fun ops => exec ops []) (example_ops).
