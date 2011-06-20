(** エントリポイント *)

open Absyn
open Context

(* プロンプト記号の定義 *)
let prompt = "> "
let print_prompt() =
  print_string prompt;
  flush stdout

let print_bind ctx b tm =
  print_string (to_string_binding ctx (b,tm));
  print_newline()

(** Read-Eval-Print-Loop *)
let repl parse tokenize =
  let lexbuf = Lexing.from_channel stdin in
  let store = Store.create() in
  let def_binds ctx bs tm =
    let rec iter bs tms o ctx' = match bs,tms with
      | [],[] -> ctx'
      | Wild as b::bs',tm::tms' ->
          let v = Core.eval ctx store tm in
            print_bind ctx b v;
            iter bs' tms' o ctx'
      | (Eager x) as b::bs',tm::tms' ->
          let v = Core.eval ctx store tm in
            print_bind ctx b v;
            iter bs' tms' (o + 1) (Context.add_term ctx' x v o)
      | (Lazy x) as b::bs',tm::tms' ->
          print_bind ctx b tm;
          iter bs' tms' (o + 1) (Context.add_term ctx' x tm o)
      | _ -> assert false
    in
      match bs with
        | [b] -> iter bs [tm] 1 ctx
        | bs -> match Core.eval_tuple ctx store tm with
            | TmTpl tms when List.length bs == List.length tms ->
                iter bs tms 1 ctx
            | _ -> failwith "*** tuple mismatch ***"
  in
  let rec loop ctx =
    print_prompt();
    flush stdout; (
    try
      let result = parse tokenize lexbuf in
      let ctx = (
        match result ctx with
          | Eval tm ->
              let v = Core.eval ctx store tm in
                Printf.printf
                  "%s\n===> %s\n" (to_string ctx tm) (to_string ctx v);
                ctx
          | Defn(bs,tm) -> def_binds ctx bs tm
          | Data(c,arity) ->
              Const.add_ctor c arity;
              Printf.printf "data %s/%d\n" c arity;
              ctx
          | Noop -> print_newline(); ctx
      )
      in
        loop ctx
    with e -> Error.report e
    ); loop ctx
  in
    loop Context.empty

let main() =
  try
    repl Parser.toplevel Lexer.token
  with End_of_file -> ()

let _ = main()
