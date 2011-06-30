open Context
open Absyn

(* コマンド定義 *)
type t =
  | Defn of binder * term
  | Eval of term
  | Use  of string * (term, typ) Context.t
  | Noop

(* バッチモード設定 *)
let batch_mode_ref = ref false  (* -b *)

let print_result ctx v ty =
  if not !batch_mode_ref then
    Printf.printf "===> %s: %s\n" (to_string ctx v) (typ_to_string ctx ty)

let print_bind ctx b tm ty =
  if not !batch_mode_ref then
    Printf.printf "%s = %s: %s\n"
      (binder_to_string b) (to_string ctx tm) (typ_to_string ctx ty)


(** 大域変数を定義する *)
let def_bind store ctx b tm = match b with
  | Wild ->
      let ty = Core.typing ctx tm in
      let v = Core.eval ctx store tm in
        print_bind ctx b v ty;
        ctx
  | Eager x ->
      let ty = Core.typing ctx tm in
      let v = Core.eval ctx store tm in
        print_bind ctx b v ty;
        Context.add_term ctx x v ty 1
  | Lazy x ->
      let ty = Core.typing ctx tm in
        print_bind ctx b tm ty;
        Context.add_term ctx x tm ty 1

(* ロード関数のテーブル定義 *)
type loader_t = {
  mutable load_module : string -> (term, typ) Context.t;
  mutable use_module  : string -> (term, typ) Context.t;
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
        let ty = Core.typing ctx tm in
        let v = Core.eval ctx store tm in
          print_result ctx v ty;
          ctx
    | Defn(b,tm) ->
        def_bind store ctx b tm
    | Use(name,ctx') -> Context.join ctx' ctx
    | Noop -> ctx
