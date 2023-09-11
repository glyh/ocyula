exception Unimplemented

type reason = 
   | Unbound of int
   | Mismatch of term * term
   | Uninferable of term
   | Uncheckable
   | CantApplyNonFunction of term * term
and term = 
   | TyType
   | Var of int (* de Brujin Index *)
   | Lam of term
   | App of term * term
   | Pi of term * term
   | Ann of term * ty
   | TyBool
   | LitBool of bool
   | If of term * term * term
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
   | Pi(a, b) -> 
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
let show (t: term) = 
   show_ctx t [] 0

let rec shift_c (t: term) d c = 
   match t with
   | Var(i) -> Var(if i < c then i else i + d)
   | Lam(t) -> Lam(shift_c t d (c + 1))
   | App(f, x) -> App(shift_c f d c, shift_c x d c)
   | Pi(a, b) -> App(shift_c a d c, shift_c b d (c+1)) (* note that b here is bounded by x *)
   | Ann(e, t) -> Ann(shift_c e d c, shift_c t d c)
   | any -> any

let shift (t: term) d = shift_c t d 0

let rec subst_one (target: term) (var: int) (by: term) : term =
   match target with
   | Var i ->
      if var == i then by else Var i
   | Lam body ->
      Lam(subst_one body (var + 1) (shift by 1))
   | App(f, x) -> 
      App(subst_one f var by, subst_one x var by)
   | Pi(a, b) -> 
      Pi(subst_one a var by, subst_one b (var + 1) (shift by 1))
   | Ann(e, t) -> 
      Ann(subst_one e var by, subst_one t var by)
   | any -> any

exception TypeError of reason

let (=*=) (lhs: ty) rhs =
   lhs = rhs

(* we're using de Brujin Index so there won't be aliasing issue *)
let rec check_type tm ty (ctx: ctx) : unit = match (tm, ty) with 
   | Lam(inner), Pi(a, b) -> 
      check_type inner b (a :: ctx)
   | any, ty -> 
      let ty2 = infer_type any ctx in
         if not (ty2 =*= ty)
         then raise (TypeError(Mismatch(ty, ty2)))
         else ()
and infer_type (tm: term) (ctx: ctx) : ty = match tm with | Var(i) -> 
      if i >= List.length ctx 
      then raise (TypeError (Unbound i))
      else List.nth ctx i
   | App(f, x) ->
      begin match infer_type f ctx with
      | Pi(a, b) -> 
         check_type x a ctx;
         subst_one b 0 x
      | t -> raise (TypeError(CantApplyNonFunction(f, t)))
      end
   | Pi(a, b) -> 
      check_type a TyType ctx;
      (* WARN: here we don't really evaluate b to normal form so I suspect there's a problem with the algorithm *)
      check_type b TyType (a :: ctx);
      TyType
   | TyType -> TyType
   | Ann(e, ty) ->
      check_type ty TyType ctx;
      check_type e ty ctx;
      ty
   (* so for now we have to annotate any lambdas *)
   | TyBool -> TyType
   | LitBool _ -> TyBool
   | If(test, t, f) ->
      check_type test TyBool ctx;
      let tb_ty = infer_type t ctx in
      let fb_ty = infer_type f ctx in
      if not (tb_ty =*= fb_ty)
      then raise (TypeError(Mismatch(tb_ty, fb_ty)))
      else tb_ty
   | Lam _ -> raise (TypeError(Uninferable tm))
