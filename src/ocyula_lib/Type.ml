(* TODO: rewrite everything, this is BIDI, doesn't quite work with HM type inference. *)
exception Unimplemented

type reason = 
   | Unbound of int
   | Mismatch of term * term
   | Uninferable of term
   | Uncheckable
   | CantApplyNonFunction of term * term
and term = 
   | TyType
   | TyBool
   | TyPi of term * term
   | TySigma of term * term (* like Pi type, we also use debrujin index here. yes this is a dependent type pair *)
   | Var of int (* de Brujin Index *)
   | Lam of term
   | App of term * term
   | Ann of term * ty
   | LitBool of bool
   | If of term * term * term
   | Prod of term * term
   (* we use 0 for y, 1 for x, i.e. [(x, y) -> a]λx.λy.b *)
   | LetPair of term * term
and ty = term

exception PreCondViolation
let rec to_base_x (x: int) (i: int) =
   if i < 0 || x <= 0 then 
      raise PreCondViolation
   else if i < x then
      [i]
   else 
      i mod x :: (to_base_x x (i / x))

let gensym i = 
   let syms = to_base_x 26 i in
      syms 
      |> List.map (fun i -> char_of_int ((int_of_char 'a') + i - 1))
      |> List.to_seq
      |> String.of_seq

type ctx = term list (* here we're using de Brujin's index to refer to binding variables *)

let rec show_ctx (t: term) (ctx: string list) (i: int) : string = 
   let f = fun t -> show_ctx t ctx i in
   match t with
   | TyType -> "type"
   | Var(i) -> 
      if i < List.length ctx
      then List.nth ctx i
      else "u" ^ string_of_int i
   | Lam(t) -> 
      let v = gensym i in
      "λ" ^ v ^ (show_ctx t (v :: ctx) (i + 1)) 
   | App(g, x) ->
      (f g) ^ " " ^ (f x)
   | TyPi(a, b) -> 
      let v = gensym i in
      "("^ v ^ ":" ^ (f a) ^ ")->" ^ (show_ctx b (v::ctx) (i + 1)) 
   | Ann(a, b) -> 
      "(" ^ (f a) ^ ":" ^ (f b) ^ ")"
   | TyBool -> "bool"
   | LitBool(true) -> "true" 
   | LitBool(false) -> "false" 
   | If(cond, true_branch, false_branch) -> 
      "(if " ^ (f cond) ^  " do " 
         ^ (f true_branch) ^ 
      " else " 
         ^ (f false_branch) ^ 
      " end)"
   | _ -> raise Unimplemented

let show (t: term) = 
   show_ctx t [] 0

let rec shift_c (t: term) d c = 
   match t with
   | Var(i) -> Var(if i < c then i else i + d)
   | Lam(t) -> Lam(shift_c t d (c + 1))
   | App(f, x) -> App(shift_c f d c, shift_c x d c)
   | TyPi(a, b) -> TyPi(shift_c a d c, shift_c b d (c+1)) (* note that b here is bounded by x *)
   | TySigma(a, b) -> TySigma(shift_c a d c, shift_c b d (c+1))
   | Ann(e, t) -> Ann(shift_c e d c, shift_c t d c)
   | If(test, t, f) -> If(shift_c test d c, shift_c t d c, shift_c f d c)
   | Prod(lhs, rhs) -> Prod(shift_c lhs d c, shift_c rhs d c)
   | TyType | TyBool | LitBool _ as e -> e

let shift (t: term) d = shift_c t d 0

let rec subst_one (target: term) (var: int) (by: term) : term =
   match target with
   | TyType | TyBool | LitBool _ as e -> e
   | Var i ->
      if var == i then by else Var i
   | Lam body ->
      Lam(subst_one body (var + 1) (shift by 1))
   | App(f, x) -> 
      App(subst_one f var by, subst_one x var by)
   | TyPi(a, b) -> 
      TyPi(subst_one a var by, subst_one b (var + 1) (shift by 1))
   | Ann(e, t) -> 
      Ann(subst_one e var by, subst_one t var by)
   | TySigma(a, b) -> 
      TySigma(subst_one a var by, subst_one b (var + 1) (shift by 1))
   | If(test, t, f) ->
      If(subst_one test var by, subst_one t var by, subst_one f var by)
   | Prod(lhs, rhs) -> 
      Prod(subst_one lhs var by, subst_one rhs var by)

exception TypeError of reason

let (=*=) (lhs: ty) rhs =
   lhs = rhs

(* we're using de Brujin Index so there won't be aliasing issue *)
let rec check_type tm ty (ctx: ctx) : unit = match (tm, ty) with 
   | Lam(inner), TyPi(a, b) -> 
      check_type inner b (a :: ctx)
   | Prod(x, y), TySigma(a, b) -> 
      check_type x a ctx;
      check_type y (subst_one b 0 x) ctx
   | If(test, t, f), ty -> (* on ref implementation this is a checking rule rather than inference rule *)
      check_type test TyBool ctx;
      check_type t ty ctx;
      check_type f ty ctx
   | LetPair(a, b), ty -> 
      _ -> raise Unimplemented
   | any, ty -> 
      let ty2 = infer_type any ctx in
         if not (ty2 =*= ty)
         then raise (TypeError(Mismatch(ty, ty2)))
         else ()
and infer_type (tm: term) (ctx: ctx) : ty = match tm with 
   | TyType | TyBool -> TyType
   | TyPi(a, b) | TySigma(a, b) -> 
      check_type a TyType ctx;
      (* WARN: here we don't really evaluate b to normal form so I suspect there's a problem with the algorithm *)
      check_type b TyType (a :: ctx);
      TyType
   | Var(i) -> 
      if i >= List.length ctx 
      then raise (TypeError (Unbound i))
      else List.nth ctx i
   | App(f, x) ->
      begin match infer_type f ctx with
      | TyPi(a, b) -> 
         check_type x a ctx;
         subst_one b 0 x
      | t -> raise (TypeError(CantApplyNonFunction(f, t)))
      end
   | Ann(e, ty) ->
      check_type ty TyType ctx;
      check_type e ty ctx;
      ty
   (* so for now we have to annotate any lambdas *)
   | LitBool _ -> TyBool
   | Lam _ | Prod _ | If _ | LetPair _ -> raise (TypeError(Uninferable tm))
