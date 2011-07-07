open Context
open Absyn

(* コマンド定義 *)
type t =
  | Defn of binder list * term
  | Data of string * string list * ctor list
  | Eval of term
  | Use  of string
  | Noop
and ctor = string * Type.t list

(* バッチモード設定 *)
let batch_mode_ref = ref false  (* -b *)

let print_result ctx v ty =
  if not !batch_mode_ref then
    Printf.printf "===> %s: %s\n"
      (to_string ctx v) (Type.to_string ctx ty)

let print_bind ctx b tm ty =
  if not !batch_mode_ref then
    Printf.printf "%s = %s: %s\n"
      (binder_to_string b) (to_string ctx tm) (Type.to_string ctx ty)

(** 大域変数を定義する *)
let def_binds store ctx bs tm =
  let rec iter bts tms o ctx' = match bts,tms with
    | [],[] -> ctx'
    | (Wild as b,ty)::bs',tm::tms' ->
        let v = Core.eval ctx store tm in
          print_bind ctx b v ty;
          iter bs' tms' o ctx'
    | ((Eager x) as b,ty)::bs',tm::tms' ->
        let v = Core.eval ctx store tm in
          print_bind ctx b v ty;
          iter bs' tms' (o + 1) (Context.add_term ctx' x v ty o)
    | ((Lazy x) as b,ty)::bs',tm::tms' ->
        print_bind ctx b tm ty;
        iter bs' tms' (o + 1) (Context.add_term ctx' x tm ty o)
    | _ -> assert false
  in
    match bs with
      | [b] ->
          let tm',ty = Core.typing ctx tm b in
            iter [b,ty] [tm'] 1 ctx
      | bs ->
          let tm',tys = Core.typings ctx tm bs in
          let bts = List.combine bs tys in
            match Core.eval_tuple ctx store tm' with
              | TmTpl tms -> iter bts tms 1 ctx
              | _ -> assert false

(* ロード関数のテーブル定義 *)
type loader_t = {
  mutable load_module : string -> (term, Type.t) Context.t;
  mutable use_module  : string -> (term, Type.t) Context.t;
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
        let tm',ty = Core.typing ctx tm Wild in
        let v = Core.eval ctx store tm' in
          print_result ctx tm' ty;
          print_result ctx v ty;
          ctx
    | Defn(bs,tm) ->
        def_binds store ctx bs tm
    | Data _ -> ctx
    | Use name -> ctx
    | Noop -> ctx
