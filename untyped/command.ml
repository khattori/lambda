open Context
open Absyn

(* コマンド定義 *)
type t =
  | Defn of binder list * term
  | Eval of term
  | Data of string * int
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
    | Defn(bs,tm) ->
        def_binds store ctx bs tm
    | Data(c,arity) ->
        print_data c arity;
        ctx
    | Use(name,ctx') -> Context.join ctx' ctx
    | Noop -> ctx
