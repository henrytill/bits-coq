From Coq Require Import BinNat Ascii String.
From Machine Require Import Parser.
Import Parser.MenhirLibParser.Inter.

Open Scope char_scope.
Open Scope bool_scope.

CoFixpoint TheEnd : buffer := Buf_cons (EOF tt) TheEnd.

Definition is_digit c := (("0" <=? c) && (c <=? "9"))%char.

Example test_is_digit_0 : is_digit "0" = true.
Proof. simpl. reflexivity. Qed.

Example test_is_digit_1 : is_digit "1" = true.
Proof. simpl. reflexivity. Qed.

Example test_is_digit_42 : is_digit "9" = true.
Proof. simpl. reflexivity. Qed.

Example test_is_digit_a : is_digit "a" = false.
Proof. simpl. reflexivity. Qed.

Fixpoint readnum acc s :=
  match s with
  | String "0" s => readnum (acc * 10) s
  | String "1" s => readnum (acc * 10 + 1) s
  | String "2" s => readnum (acc * 10 + 2) s
  | String "3" s => readnum (acc * 10 + 3) s
  | String "4" s => readnum (acc * 10 + 4) s
  | String "5" s => readnum (acc * 10 + 5) s
  | String "6" s => readnum (acc * 10 + 6) s
  | String "7" s => readnum (acc * 10 + 7) s
  | String "8" s => readnum (acc * 10 + 8) s
  | String "9" s => readnum (acc * 10 + 9) s
  | _ => (acc, s)
  end.

Example readnum_1 : readnum 0 "1" = (1, ""%string).
Proof. simpl. reflexivity. Qed.

Example readnum_137 : readnum 0 "137" = (137, ""%string).
Proof. simpl. reflexivity. Qed.

Fixpoint lex_string_cpt n s :=
  match n with
  | 0 => Some TheEnd
  | S n =>
      match s with
      | EmptyString => Some TheEnd
      | String c s' =>
          match c with
          | " " => lex_string_cpt n s'
          | "009" => lex_string_cpt n s' (* \t *)
          | "010" => lex_string_cpt n s' (* \n *)
          | "013" => lex_string_cpt n s' (* \r *)
          | "(" => option_map (Buf_cons (LPAREN tt)) (lex_string_cpt n s')
          | ")" => option_map (Buf_cons (RPAREN tt)) (lex_string_cpt n s')
          | "+" => option_map (Buf_cons (ADD tt)) (lex_string_cpt n s')
          | _ =>
              if is_digit c then
                let (m, s) := readnum 0 s in
                option_map (Buf_cons (NUM m)) (lex_string_cpt n s)
              else
                None
          end
      end
  end.

Definition lex_string (s : string) := lex_string_cpt (length s) s.
