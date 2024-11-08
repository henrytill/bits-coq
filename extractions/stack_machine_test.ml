type nat = [%import: Stack_machine.nat] [@@deriving eq, show]

let nat_of_int = Stack_machine.nat_of_int

module Typed = struct
  module Ty = struct
    type t = [%import: Stack_machine.Typed.Ty.t] [@@deriving eq, show]
  end

  type tstack = [%import: Stack_machine.Typed.tstack] [@@deriving eq, show]

  module Binop = struct
    type t = [%import: Stack_machine.Typed.Binop.t] [@@deriving eq, show]
  end

  module Instr = struct
    type t = [%import: Stack_machine.Typed.Instr.t] [@@deriving eq, show]
  end

  module Prog = struct
    type t = [%import: Stack_machine.Typed.Prog.t] [@@deriving eq, show]

    include (Stack_machine.Typed.Prog : module type of Stack_machine.Typed.Prog with type t := t)
  end

  module Exp = struct
    type t = [%import: Stack_machine.Typed.Exp.t] [@@deriving eq, show]

    include (Stack_machine.Typed.Exp : module type of Stack_machine.Typed.Exp with type t := t)
  end
end

let testable_nat = Alcotest.testable pp_nat equal_nat
let testable_prog = Alcotest.testable Typed.Prog.pp Typed.Prog.equal

let denote_nconst () =
  let open Typed in
  let expected = nat_of_int 42 in
  let nconst = Exp.NConst expected in
  let denotation = Exp.denote Ty.Nat nconst |> Obj.obj in
  Alcotest.(check testable_nat) "same nat" expected denotation

let compile_nconst () =
  let open Typed in
  let input = nat_of_int 42 in
  let expected =
    Prog.Cons ([], [ Ty.Nat ], [ Ty.Nat ], Instr.NConst ([], input), Prog.Nil [ Ty.Nat ])
  in
  let nconst = Exp.NConst input in
  let denotation = Exp.compile Ty.Nat nconst [] in
  Alcotest.(check testable_prog) "same prog" expected denotation

let denote_compile_nconst () =
  let open Typed in
  let input = nat_of_int 42 in
  let nconst = Exp.NConst input in
  let denotation = Prog.denote [] [] (Exp.compile Ty.Nat nconst []) (Obj.repr ()) |> Obj.obj in
  Alcotest.(check (pair testable_nat unit)) "same pair" (input, ()) denotation

let () =
  Alcotest.(
    run "Stack_machine"
      [
        ( "Exp",
          [
            test_case "denote_nconst" `Quick denote_nconst;
            test_case "compile_nconst" `Quick compile_nconst;
            test_case "denote_compile_nconst" `Quick denote_compile_nconst;
          ] );
      ])
