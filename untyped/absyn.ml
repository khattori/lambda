(**
   Absyn: ���ۍ\���ؒ�`
*)
open Printf
open Context

exception Parse_error

(* ���̒�` *)
(*
  E ::= x (�� Ident)
      | c (�� Const)
      | \B.E
      | E1 E2
      | let B = E1 in E2
      | case E of c1 -> E1 | ... -> En
      | E1,...,En
  B ::= x | \x | _ | B,B 
  ,_ 0�ȏ�̂Ă���
  ,x...  0�ȏ��tuple
let xs... 
let _,x,xs ... xs��nil���C�P�l���C�^�v���l�ƂȂ�
*)

type term =
  | TmVar of int
  | TmCon of Const.t
  | TmAbs of binder list * term
  | TmApp of term * term
  | TmLet of binder list * term * term
  | TmCas of term * case list
  | TmTpl of term list
and case = PatnCase of Const.t * term | DeflCase of term
and command =
  | Defn of binder list * term
  | Eval of term
  | Data of string * int
  | Noop

let rec to_string ctx tm =
  match tm with
    | TmVar x -> Context.index2name ctx x
    | TmCon c -> Const.to_string c
    | TmAbs(bs,tm) ->
        let s = bind_type_to_string s in
        let ctx',x' = Context.fresh_name ctx x in
          sprintf "(%s\\%s" s x' ^ "." ^ to_string ctx' tm ^ ")"
    | TmApp(tm1,tm2) ->
        "(" ^ to_string ctx tm1 ^ " " ^ to_string ctx tm2 ^ ")"
    | TmLet(binds,tm2) ->
        "(let " ^
          let ctx',s = List.fold_left (to_string_bind ctx) (ctx,"") binds
          in
            s ^ "in " ^ to_string ctx' tm2 ^ ")"
    | TmCas(tm1,cases,def) ->
        "(case " ^ to_string ctx tm1 ^ " of " ^
            String.concat " | " (
              (List.map (to_string_case ctx) cases) @ (
                match def with
              | None -> []
              | Some tm2 -> [sprintf "... -> %s" (to_string ctx tm2)] )) ^
          ")"
    | TmTpl tms ->
        "(" ^ String.concat ", " (List.map (to_string ctx) tms) ^ ")"
and to_string_case ctx (c,tm) =
  sprintf "%s -> %s" (Const.to_string c) (to_string ctx tm)
and to_string_bind ctx (ctx',str) (s,x,tm) =
  let s = bind_type_to_string s in
  let ctx'', x' = Context.fresh_name ctx' x in
    ctx'', str ^ sprintf "%s%s = " s x' ^ to_string ctx tm ^ "; "

(*
 * print: ���ۍ\���؂̏o��
 *)
let rec print ctx tm =
  print_string (to_string ctx tm)

(* De Bruijin index *)
(*
 * map: ���u���̂��߂̕⏕�֐�
 *
 *)
let term_map onvar t =
  let rec walk c t = match t with
    | TmVar x         -> onvar c x
    | TmAbs(s,x,t1)   -> TmAbs(s,x,walk (c + 1) t1)
    | TmApp(t1,t2)    -> TmApp(walk c t1,walk c t2)
    | TmLet(binds,t2) ->
        TmLet(List.map (fun (s,x,t1) -> s,x,walk c t1) binds,
              walk (c + (List.length binds)) t2)
    | TmCas(t1,cs,t2opt) ->
        TmCas(walk c t1,
              List.map (fun (con,t) -> con,walk c t) cs,
              walk_opt c t2opt)
    | TmTpl(ts) -> TmTpl(List.map (walk c) ts)
    | con             -> con
  and walk_opt c topt = match topt with
    | None -> None | Some t -> Some(walk c t)
  in
    walk 0 t

(*
 * shift: �V�t�g����
 * 
 *   ��d,c(k)                = k          --- if k < c
 *                             k + d      --- if k >= c
 *   ��d,c(\.t1)             = \.��d,c+1(t1)
 *   ��d,c(t1 t2)            = ��d,c(t1) ��d,c(t2)
 *   ��d,c(let x = t1 in t2) = let x = ��d,c(t1) in ��d,c+1(t2)
 * 
 *)
let term_shift d t =
  term_map
    (fun c x -> if x >= c then TmVar(x + d) else TmVar x)
    t

(*
 * subst: �u������
 * 
 *   [j:->s]k                  = s     --- if k = j
 *                               k     --- else
 *   [j:->s]\.t1               = \.[j+1:->��1,0(s)]t1
 *   [j:->s](t1 t2)            = [j:->s]t1 [j:->s]t2
 *   [j:->s](let x = t1 in t2) = let x = [j:->s]t1 in [j+1:->��1,0(s)]t2
 * 
 * �ȉ��̎����ł́Cshift�������C�ɂ���Ă���
 *)
let term_subst j s t =
  term_map
    (fun c x -> if x == j + c then term_shift c s else TmVar x)
    t

(*
 * subst_top: ���Ȗ�ɂ�����u��
 * 
 *   (\x.t1) t2 �� ��-1,0([0:->��1,0(t2)]t1)
 *
 *)
(*
let term_subst_top t1 t2 =
  term_shift (-1) (term_subst 0 (term_shift 1 t2) t1)
*)
(*
 * (\x.t1) t2 �� ��0(t1,t2)
 * 
 * ��n(m,t)     = m        if m < n
 * ��n(n,t)     = ��n,0(t)
 * ��n(m,t)     = m-1      if m > n
 * ��n(\.t',t)  = \.��n+1(t',t)
 * ��n(t1 t2,t) = ��n(t1,t) ��n(t2,t)
 *)
let term_subst_top t1 t2 =
  term_map
    (fun c x ->
       if x < c then TmVar x
       else if x == c then term_shift c t2
       else TmVar(x - 1))
    t1

(*
 * is_value: �����l���ǂ�������
 * 
 *)
let rec is_value tm =
  let rec walk tm =
    match tm with
      | TmApp(tm1,tm2) when is_value tm2 -> walk tm1 - 1
      | TmTpl tms when List.for_all is_value tms -> 0
      | TmCon(c) when Const.is_cstr c -> Const.arity c
      | TmCon(c) when Const.is_dstr c -> Const.arity c - 1
      | TmCon _ | TmAbs _ -> 0
      | _ -> -1
  in
    walk tm >= 0

let check_value oncon tm =
  let rec walk tm =
    match tm with
      | TmCon(c) when oncon c -> Const.arity c
      | TmApp(tm1,tm2) when is_value tm2 -> walk tm1 - 1
      | _ -> -1
  in
    walk tm == 0

(*
 * is_dstr_value: �����f�X�g���N�^���ǂ�������
 *)
let is_dstr_value tm =
  check_value Const.is_dstr tm

(*
 * is_cstr_value: �����R���X�g���N�^���ǂ�������
 *)
let is_cstr_value tm =
  check_value Const.is_cstr tm


