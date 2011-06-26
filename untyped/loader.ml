open Sys
open Filename
open Lexing

exception Invalid_extname of string

(*
ファイル指定の方法
   コマンドラインから
  ./foo.prog      --- 起動ディレクトリからの相対パス
  /hoge/foo.prog  --- 絶対パス

   コマンドから
  use foo;

*)

(* ファイル拡張子 *)
let prog_ext = ".prog"
(* サーチパス拡張子 *)
let search_paths = ["./"]

let (
  add_loading,
  add_loaded,
  del_loaded,
  is_loaded,
  get_loaded
) =
  let _loaded_modules_ref = ref []
  in
    (
      (fun mname ->
         _loaded_modules_ref :=
           (mname,ref Context.empty)::!_loaded_modules_ref),
      (fun mname ctx ->
         (List.assoc mname !_loaded_modules_ref) := ctx),
      (fun mname ->
         _loaded_modules_ref :=
           List.filter (fun (m,_) -> m <> mname) !_loaded_modules_ref),
      (fun mname ->
         List.mem_assoc mname !_loaded_modules_ref),
      (fun mname ->
         !(List.assoc mname !_loaded_modules_ref))
    )
(*
 * fpath2mname: ファイルパスから標準モジュール名に変換
 * 
 *   - extensionが.progであること．
 *   - basenameからextensionを取り除いたもの．
 *)
let fpath2mname fpath =
  if not (check_suffix fpath prog_ext) then
    raise (Invalid_extname fpath)
  else
    chop_extension (basename (fpath))

(* サーチパスを参照してモジュールのファイルを検索する *)
let search_filepath mname =
  let fname = mname ^ prog_ext in
  let path =
    List.find
      (fun path -> Sys.file_exists (concat path fname))
      search_paths
  in
    concat path fname

(** ファイルを読み込んで評価する
    コンテクストは新たに作成する
    ---> すなわち、ファイルは常に空のコンテクストで評価される
*)
let load_file store fname =
  try
    let ctx = Context.empty in
    let mname = fpath2mname fname in
    let infile = open_in fname in
    let lexbuf = Lexing.from_channel infile in
      try
        add_loading mname;
        Lexer.init lexbuf fname;
        let result = Parser.main Lexer.token lexbuf in
        let cmds = result ctx in
        let ctx = List.fold_left (Command.exec store) ctx cmds in
          Printf.printf "file '%s' loaded.\n" fname;
          close_in infile;
          add_loaded mname ctx;
          ctx
      with e ->
        Error.report lexbuf.lex_start_p e;
        del_loaded mname;
        close_in infile;
        ctx
  with
    | Sys_error msg ->
        Printf.printf "Error: %s\n" msg; Context.empty
    | Invalid_extname s ->
        Printf.printf "Error: invalid extension '%s'\n" s; Context.empty

(** モジュールを読み込んで評価する *)
let load_module store mname =
  try
    let fname = search_filepath mname in
      load_file store fname
  with Not_found ->
    Printf.printf "Error: module '%s' not found\n" mname;
    Context.empty

(** モジュールが未読み込みであれば読み込む *)
let use_module store mname =
  if is_loaded mname then
    get_loaded mname
  else
    load_module store mname

