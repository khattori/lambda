open Context
open Absyn

(* コマンド定義 *)
type t =
  | Defn of binder * term
  | Eval of term
  | Use  of string * term Context.t
  | Noop

(* バッチモード設定 *)
let batch_mode_ref = ref false  (* -b *)

let print_result ctx v =
  if not !batch_mode_ref then
    Printf.printf "===> %s\n" (to_string ctx v)

let print_data c arity =
  if not !batch_mode_ref then
    Printf.printf "data %s/%d\n" c arity

let print_bind ctx b tm =
  if not !batch_mode_ref then (
    print_string (to_string_binding ctx (b,tm));
    print_newline()
  )

(** 大域変数を定義する *)
let def_bind store ctx b tm = match b with
  | Wild ->
      let v = Core.eval ctx store tm in
        print_bind ctx b v
  | Eager x ->
      let v = Core.eval ctx store tm in
        print_bind ctx b v;
        Context.add_term ctx x v 1
  | Lazy x ->
      print_bind ctx b tm;
      Context.add_term ctx' x tm 1

(* ロード関数のテーブル定義 *)
type loader_t = {
  mutable load_module : string -> term Context.t;
  mutable use_module  : string -> term Context.t;
}
let dummy_loader f = assert false

(* ロード済みファイル一覧 *)
let (
  set_loader,
  load_module,
  use_module
) =
  let _loader = {
    load_module = dummy_loader;
    use_module  = dummy_loader;
  }
  in
    (
      (fun loadm usem ->
         _loader.load_module <- loadm;
         _loader.use_module  <- usem),
      (fun mname -> _loader.load_module mname),
      (fun mname -> _loader.use_module mname)
    )
(* load     :モジュールをロードする(ロード済みでも再ロード) *)
(* use      :モジュールを使用する（未ロードならロードする） *)
(* load_file:ファイルをロードする（ファイルパス指定）       *)

(** コマンド実行 *)
let exec store ctx cmd =
  match cmd with
    | Eval tm ->
        let v = Core.eval ctx store tm in
          print_result ctx v;
          ctx
    | Defn(b,tm) ->
        def_bind store ctx b tm
    | Use(name,ctx') -> Context.join ctx' ctx
    | Noop -> ctx
