(** エントリポイント *)

open Absyn
open Context
open Lexing

(* プロンプト記号の定義 *)
let prompt = "> "
let print_prompt() =
  print_string prompt;
  flush stdout


(** Read-Eval-Print-Loop *)
let repl store ctx =
  let lexbuf = Lexing.from_channel stdin in
  let rec loop ctx =
    print_prompt();
    try
      let result = Parser.toplevel Lexer.token lexbuf in
      let cmd = result ctx in
      let ctx = Command.exec store ctx cmd in
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
let (
  add_file,
  get_files
) =
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
    "-b", Arg.Set  Command.batch_mode_ref, "Run in batch mode";
    "-d", Arg.Unit set_debug_mode, "Run in debug mode";
    "-v", Arg.Unit
      (fun () -> print_version(); exit 0),"Print version and exit";
  ] add_file usage;
  let ctx = Context.empty in
  let store = Store.create() in
  let _ =
    Command.set_loader (Loader.load_module store) (Loader.use_module store) in
  let ctx =
    List.fold_left
      (fun ctx fname -> Context.join (Loader.load_file store fname) ctx)
      ctx (get_files())
  in
    if !Command.batch_mode_ref then exit 0;
    try
      print_version();
      repl store ctx
    with End_of_file -> ()

let _ = main()
