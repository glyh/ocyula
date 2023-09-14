(*
uniquely decide any bindings 
*)

(* dependency resolving order: 
   1. look for closest previous definition 
   2. if failed, look for closest later definition
*) (* Allows me to write: 
   iseven = fn(x) if x == 0 then true else isodd(x-1) end
   (* we allow the definition of later refered symbol to depends on side effects *)
   (* because in the type system we have something like effectful value, their evaluation triggers side effect only ONCE *)
   isodd = fn(x) if x == 0 then true else iseven(x-1) end
*)

open Ast

exception Unreachable

type src = PassDeCallLam.dst
type dst = <
   seq: no;
   pattern: yes;
   lambda: no;
   call: no;
   recbind: yes; 
   unique_id: yes;
   bind_only: yes;
   letin: no>

module ReferMap = CCPersistentHashtbl.Make(struct
   type t = string
   let equal s t = s = t
   let hash = Hashtbl.hash
end)
type refer_map = dst id_t ReferMap.t

type is_alias_of =
   | IsAliasOf of dst id_t * dst id_t

type alias_map = is_alias_of list

module AliasMapCollapsed = CCPersistentHashtbl.Make(struct
   type t = dst id_t
   let equal s t = s = t
   let hash = Hashtbl.hash
end)
type alias_map_collapsed = dst id_t AliasMapCollapsed.t

(* returns the deduplicated expression and the refer map *)
(* 
   In the bound map, we store all the variables that is already bounded at this point of the expression 
   In the refer map, we store all the variables that not yet defined at this point.
*)

type bound_info = {
   bound: refer_map ; 
   bounding: refer_map; (* we're on RHS of a pattern matching *)
   refer: refer_map ; 
   alias: alias_map ; 
}

let new_bound () = 
   { 
      bound = ReferMap.empty(); 
      bounding = ReferMap.empty(); 
      refer = ReferMap.empty (); 
      alias = []
   }

(* Whenever we enter a scope, we must clear the refer map, because we don't want to allow 
   values to depend on another value in a inner scope. bound map can be leaved untouched. *)
let enter_scope (b: bound_info) : bound_info = 
   let { bound; bounding; _ } = b in { bound; bounding; refer = ReferMap.empty (); alias = [] }

(* Whenever we exit a scope, we must reset the bound map to the map before we enter the 
   scope because we don't want to allow values to depend on another value in a inner scope. 
   Refer map should be merged to the outer refer map though.  *)
let leave_scope (outer: bound_info) (inner: bound_info) =
   let merge_ref_gen_alias outer_ref inner_ref : (refer_map * alias_map) =
      let alias_out : alias_map ref = ref [] in
      let refer_out = 
         ReferMap.merge ~f:(
            fun _ info -> 
            match info with
            | `Both (outer, inner) -> 
               (* they are the same symbol *)
               (* we always prefer previous symbol that is not aliased, there won't be a cycle here. *)
               alias_out := IsAliasOf(inner, outer) :: !alias_out;
               Some outer
            | `Left r | `Right r -> Some r
         ) outer_ref inner_ref
      in (refer_out, !alias_out)
   in
   let {bound; bounding; refer = out_r; alias = out_a } = outer in
   let { refer = in_r; alias = in_a; _ } = inner in
   let (refer_merged, alias_generated) = merge_ref_gen_alias in_r out_r in
   let alias_new = out_a @ alias_generated @ in_a (* this order is important *)
   in
   { 
      bound; bounding; 
      (* TODO: if in_r and out_r contains same symbols, it means that they should actually be the same one, we have another data structure to store such data *)
      refer = refer_merged;
      alias = alias_new
   }

let lookup_sym (b: bound_info) (s: src id_t) (is_unpin: bool) : (bound_info * dst id_t) =
   match s with
   | Gensym(i) -> b, Gensym(i)
   | Concrete(s) -> 
      (* query whether we have v in scope, if so, replace v with reference to that value, 
         o.w. issue a reference to later definition *)
      begin match (ReferMap.get s b.refer, ReferMap.get s b.bounding, ReferMap.get s b.bound) with
      | Some(s), _, _ -> b, s
      | _, Some(s), _ when not is_unpin -> b, s
      | _, None, Some(s) -> b, s
      | _ -> (* either not found in both map, or found in bounding but requires unpin *)
         let sym = Unique(s, gensym()) in
         { b with refer = ReferMap.add b.refer s sym }, sym
      end

let uniqualize (s: src id_t) : dst id_t = 
   match s with
   | Gensym(i) -> Gensym(i)
   | Concrete(s) -> Unique(s, gensym())

let introduce_sym : (bound_info * src id_t) -> (bound_info * dst id_t) = fun (b, s) ->
   match s with
   | Gensym i -> b, Gensym i
   | Concrete sym -> 
      let uid = begin match ReferMap.get sym b.refer with
      | Some(s) -> s
      | None -> Unique(sym, gensym())
      end in
      { 
         b with 
            bounding = ReferMap.remove b.bounding sym; 
            bound = ReferMap.add b.bound sym uid;
            refer = ReferMap.remove b.refer sym
      }, uid

(* the following 2 functions are used to create self reference *)
let introducing_sym : (bound_info * src id_t) -> (bound_info * dst id_t) = fun (b, s) ->
   match s with
   | Gensym i -> b, Gensym i
   | Concrete sym -> 
      let uid = begin match ReferMap.get sym b.refer with
      | Some(s) -> s
      | None -> Unique(sym, gensym())
      end in
      {
        b with 
          bounding = ReferMap.remove b.bounding sym; 
          bound = ReferMap.add b.bound sym uid;
          refer = ReferMap.remove b.refer sym
      }, uid

let introduced_sym : (bound_info * dst id_t) -> bound_info = fun (b, s) ->
   match s with
   | Gensym _ -> b
   | Unique(sym, _) -> 
      {
         b with 
            bounding = ReferMap.remove b.bounding sym;
            bound = ReferMap.add b.bound sym s
      }

(* let rec de_seq: type a. (a, src) gen_ast -> (a, dst) gen_ast = function *)
let rec deduplicate_id_b_seq 
   : type a. bound_info * (a, src) gen_ast list -> bool -> bound_info * (a, dst) gen_ast list = 
   fun (b, es) do_scope ->
      let b' = if do_scope then enter_scope b else b in
      let (b', es') = 
         List.fold_left 
            (fun (b, e_acc) e -> 
               let (b, e) = deduplicate_id_b (b, e) in 
               (b, e_acc @ [e]) (* OPTIMIZE: reverse the list *)
            ) 
            (b', []) 
            es 
      in
      let b' = if do_scope then leave_scope b b' else b' in
      (b', es')

and deduplicate_id_b : type a. bound_info * (a, src) gen_ast -> bound_info * (a, dst) gen_ast = fun (b, e) ->
   let f = deduplicate_id_b in
   let fs = deduplicate_id_b_seq in
   let f_scope : type a. bound_info * (a, src) gen_ast -> bound_info * (a, dst) gen_ast = fun (b, e) -> 
      let b' = enter_scope b in
      let b', e = f (b', e) in
      let b = leave_scope b b' in
      b, e
   in
   match e with
   | Concrete _ | Gensym _ -> raise Unreachable

   | Bind s -> 
      let b, s = f (b, s) in 
      b, Bind s
   | Union(ps) -> 
      let b, ps = fs (b, ps) false in 
      b, Union(ps)
   | PatTuple(ps) -> 
      let b, ps = fs (b, ps) false in
      b, PatTuple(ps)
   | PatList(ps) ->
      let b, ps = fs (b, ps) false in
      b, PatTuple(ps)
   | PLit(l) -> b, PLit(l)
   | PAny() -> b, PAny()
   | With(p, e) -> 
      let b, p = f (b, p) in
      let b, e = f (b, e) in
      b, With(p, e)
   | Updatable(p) -> 
      let b, p = f (b, p) in
      b, Updatable(p)
   | Pin(s) -> 
      let b, s = lookup_sym b s false in
      b, Pin(s)
   | Lens(obj, m, args) -> 
      let b, obj = f (b, obj) in
      let b, m = lookup_sym b m false in
      let b, args = fs (b, args) false in
      b, Lens(obj, m, args)
   | Seq(es) -> 
      let b, es = fs (b, es) true in 
      (b, Seq es)
   | Val(s) -> 
      let b, s = lookup_sym b s false in
      b, Val(s)
   | UnPin(s) -> 
      let b, s = lookup_sym b s true in
      b, Val(s)
   | BindOnly(lhs, rhs) ->
      (* let uid = uniqualize lhs in *)
      let b, uid = introducing_sym (b, lhs) in
      let b, e = f (b, rhs) in
         introduced_sym (b, uid), e
   | Assert e -> 
      let b, e = f (b,e) in b, Assert e
   | Lit l -> b, Lit l
   | Binary(op, l, r) -> 
      let b, l = f (b, l) in
      let b, r = f (b, r) in
         b, Binary(op, l, r)
   | Unary(op, e) ->
      let b, e = f (b, e) in
      b, Unary(op, e)
   | If(test, tb, fb) -> 
      let b, test = f (b, test) in
      let b, tb = f_scope (b, tb) in 
      let b, fb = f_scope (b, fb) in 
      b, If(test, tb, fb)
   | Tuple(es) -> 
      let b, es = fs (b, es) false in 
      (b, Tuple es)
   | List(es) -> 
      let b, es = fs (b, es) false in 
      (b, List es)
   | KthTuple(e, k) -> 
      let b, e = f (b, e) in
      b, KthTuple(e, k) 
   | Abs(id, e) -> 
      let b_inner, id = introduce_sym (b |> enter_scope, id) in
      let b_inner, e = f (b_inner, e) in 
      let b = leave_scope b b_inner in 
      b, Abs(id, e) 
   | App(fn, x) -> 
      let b, fn = f (b, fn) in
      let b, x = f (b, x) in
         b, App(fn, x)
   | CaseMatch (matched, branches) -> 
      let dedup_branch (b, (p, cond, e)) = 
         let b' = enter_scope b in
         let b', p = f (b', p) in 
         let b', cond = f (b', cond) in
         let b'' = enter_scope b' in
         let b'', e = f (b'', e) in
         let b' = leave_scope b' b'' in
         let b = leave_scope b b' in
         b, (p, cond, e)
      in
      let b, matched = deduplicate_id_b (b, matched) in
      let b, branches = List.fold_left
         (fun (b, bs) bi -> 
            let b, bi = dedup_branch (b, bi) in
            b, bs @ [bi]
         )
         (b, []) branches
      in
      (b, CaseMatch(matched, branches))

type reason = 
   | UnboundId of dst id_t list
exception ScopeException of reason

let collpase_alias (a: alias_map) : alias_map_collapsed = 
   let rec collpase_alias_r (a, collapsed) =
      match a with 
      (* reads: `alias` should be replaced by `middle` which may be an alias to something else *)
      | IsAliasOf(alias, middle) :: rest ->
         let base: dst id_t = begin match AliasMapCollapsed.get middle collapsed with
         | None -> middle
         | Some(base') -> base'
         end in
         collpase_alias_r
         (rest, 
          AliasMapCollapsed.add collapsed alias base)
      | [] -> collapsed
   in collpase_alias_r (a, AliasMapCollapsed.empty()) 

let rec clean_alias : type a. alias_map_collapsed -> (a, dst) gen_ast -> (a, dst) gen_ast = fun a e ->
   match e with
   | Unique _ as e ->
      begin match AliasMapCollapsed.get e a with
      | Some(target) -> target
      | None -> e
      end
   | Gensym _ as e ->
      begin match AliasMapCollapsed.get e a with
      | Some(target) -> target
      | None -> e
      end
   | Bind _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Lens _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Union _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Updatable _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Pin _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | PatTuple _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | PatList _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | PLit _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | PAny _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | With _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Assert _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Val _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Lit _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Binary _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Unary _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Seq _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | If _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Tuple _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | KthTuple _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | List _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | Abs _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | App _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | BindOnly _ as e -> shallow_map {f = fun e -> clean_alias a e} e
   | CaseMatch _ as e -> shallow_map {f = fun e -> clean_alias a e} e

let deduplicate_id : src exp_t -> dst exp_t = fun e ->
   let (b, e) = deduplicate_id_b (new_bound(), e) in
   let {refer; alias; _} = b in 
      if not (ReferMap.is_empty refer)
      then 
         (* any remaining refers indicates an unbounded symbol *)
         let unbounded_syms = refer |> ReferMap.to_list |> List.map snd in
            raise (ScopeException (UnboundId unbounded_syms))
      else
         (*TODO: collpase the aliases *)
         let alias = collpase_alias alias in
         clean_alias alias e
