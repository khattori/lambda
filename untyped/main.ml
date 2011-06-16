open Absyn
open Context

let prompt = "> "
let print_prompt() =
  print_string prompt;
  flush stdout

let print_bind ctx x s tm =
  print_string x;
  print_string (match s with Eager -> " = " | Lazy -> " ::= ");
  print ctx tm;
  print_newline()

let repl parse tokenize =
  let lexbuf = Lexing.from_channel stdin in
  let store = Store.create() in
  let def_binds ctx binds =
    let rec loop ctx' o binds =
      match binds with
        | [] -> ctx'
        | (Eager,x,tm)::binds' ->
            let v = Core.eval ctx store tm in
              print_bind ctx x Eager v;
              loop (Context.add_term ctx' x v o) (o + 1) binds'
        | (Lazy,x,tm)::binds' ->
            print_bind ctx x Lazy tm;
            loop (Context.add_term ctx' x tm o) (o + 1) binds'
    in
      loop ctx 1 binds
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
                print ctx tm;
                print_newline();
                print_string "===> ";
                print ctx v;
                ctx
          | Defn binds -> def_binds ctx binds
          | Noop -> ctx
      )
      in
        print_newline();
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
