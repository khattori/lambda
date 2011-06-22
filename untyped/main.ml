(** エントリポイント *)

open Absyn
open Context
open Lexing

(* プロンプト記号の定義 *)
let prompt = "> "
let print_prompt() =
  print_string prompt;
  flush stdout

(* バッチモード設定 *)
let batch_mode_ref = ref false  (* -b *)

let print_bind ctx b tm =
  if not !batch_mode_ref then (
    print_string (to_string_binding ctx (b,tm));
    print_newline()
  )

let print_result ctx v =
  if not !batch_mode_ref then
    Printf.printf "===> %s\n" (to_string ctx v)

let print_data c arity =
  if not !batch_mode_ref then
    Printf.printf "data %s/%d\n" c arity

let def_binds store ctx bs tm =
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

(** コマンド実行 *)
let command_exec store ctx cmd =
  match cmd with
    | Eval tm ->
        let v = Core.eval ctx store tm in
          print_result ctx v;
          ctx
    | Defn(bs,tm) ->
        def_binds store ctx bs tm
    | Data(c,arity) ->
        print_data c arity;
        ctx
    | Noop -> ctx

(** ファイルを読み込んで評価する *)
let load_file parse store ctx fname =
  try
    let infile = open_in fname in
    let lexbuf = Lexing.from_channel infile in
      try
        Lexer.init lexbuf fname;
        let result = parse Lexer.token lexbuf in
        let cmds = result ctx in
          Printf.printf "file '%s' load...\n" fname;
          List.fold_left (command_exec store) ctx cmds
      with e -> Error.report lexbuf.lex_start_p e; ctx
  with Sys_error msg -> Printf.printf "Error: %s\n" msg; ctx

(** Read-Eval-Print-Loop *)
let repl parse store ctx =
  let lexbuf = Lexing.from_channel stdin in
  let rec loop ctx =
    print_prompt();
    try
      let result = parse Lexer.token lexbuf in
      let cmd = result ctx in
      let ctx = command_exec store ctx cmd in
        loop ctx
    with e -> (
      Error.report lexbuf.lex_start_p e;
      loop ctx
    )
  in
    loop ctx

(* 実行モジュール名を取得 *)
let prog_name = Filename.basename Sys.executable_name

(* 使用方法情報 *)
let usage = Printf.sprintf "Usage: %s [options] [files]" prog_name

(* デバッグモード設定 *)
let set_debug_mode () =
  Printexc.record_backtrace true;
  Printexc.print_backtrace stdout

(* バージョン情報表示 *)
let print_version() =
  Printf.printf "Untyped Lambda Interpreter, version 0.0.1\n"

(* 
 * add_file : ファイル一覧にファイル名を追加
 * get_files: ファイル一覧を取得
 *)
let ( add_file,
      get_files ) =
  let files = ref [] in
    (
      (fun fname -> files := fname :: !files),
      (fun ()    -> List.rev !files)
    )

(** メイン関数

    Usage: untyped [opsions] [file]...

    デフォルトでは，引数で指定したファイルが読み込まれ，対話モードで動
    作する．

    [オプション]
    -b    バッチモード
    引数で指定したファイルを読み込み，実行した後で終了する
    -d    デバッグモード
    -v    バージョン表示
*)
let main() =
  Arg.parse [
    "-b", Arg.Set  batch_mode_ref, "Run in batch mode";
    "-d", Arg.Unit set_debug_mode, "Run in debug mode";
    "-v", Arg.Unit
      (fun () -> print_version(); exit 0),"Print version and exit";
  ] add_file usage;
  let ctx = Context.empty in
  let store = Store.create() in
  let ctx =
    List.fold_left
      (load_file Parser.main store)
      ctx (get_files())
  in
    if !batch_mode_ref then exit 0;
    try
      print_version();
      repl Parser.toplevel store ctx
    with End_of_file -> ()

let _ = main()
