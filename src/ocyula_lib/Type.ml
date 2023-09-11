exception Unimplemented

type reason = 
   | Unbound of int
   | Mismatch of term * term
   | Uninferable of term
   | Uncheckable
   | CantApplyNonFunction of term * term
and term = 
   | Type
   | Var of int (* de Brujin Index *)
   | Lam of term
   | App of term * term
   | Pi of term * term
   | Ann of term * ty
and ty = term

exception TypeError of reason


type ctx = term list (* here we're using de Brujin's index to refer to binding variables *)

(* we're using de Brujin Index so there won't be aliasing issue *)
let rec check_type tm ty (ctx: ctx) : unit = match (tm, ty) with 
   | Lam(inner), Pi(a, b) -> 
      check_type inner b (a :: ctx)
   | any, ty -> 
      let ty2 = infer_type any ctx in
         if ty2 != ty 
         then raise (TypeError(Mismatch(ty, ty2)))
         else ()
and infer_type (tm: term) (ctx: ctx) : ty = match tm with
   | Var(i) -> 
      if i >= List.length ctx 
      then raise (TypeError (Unbound i))
      else List.nth ctx i
   | App(f, x) ->
      begin match infer_type f ctx with
      | Pi(a, b) -> 
         check_type x a ctx;
         subst b 0 x
      | t -> raise (TypeError(CantApplyNonFunction(f, t)))
      end
   | Pi(a, b) -> 
      check_type a Type ctx;
      check_type b Type (a :: ctx);
      Type
   | Type -> Type
   | Ann(e, ty) ->
      check_type ty Type ctx;
      check_type e ty ctx;
      ty
   (* so for now we have to annotate any lambdas *)
   | _ -> raise (TypeError(Uninferable tm))
and subst (target: term) (var: int) (by: term) : term = 
   raise Unimplemented
