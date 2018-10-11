module NBE = struct

exception Todo let todo() = raise Todo
exception TypeError

(* Symbols are strings annotated with unique identifiers. *)
type sym = {name: string; id: int}
type tp = Base | Fn of tp * tp
type cx = (sym * tp) list

let next_id = ref 0
let nextId() = let x = !next_id in next_id := x + 1; x
let gensym name () = {name = name; id = nextId()}


(* ===== LANGUAGE ALGEBRAS as MODULES (a la tagless final style) ===== *)
(* Lambda calculus in intensional normal form.
 * "term" = normal/checking form. "expr" = neutral/synthesizing form. *)
module type NORMAL = sig
  type term
  type expr
  val expr: expr -> term
  val var: sym -> expr
  val app: expr * term -> expr
  val lam: sym * term -> term
end

(* A bidirectionally-typed lambda calculus. *)
module type BIDI = sig
  include NORMAL
  val asc: tp * term -> expr
end

(* Explicitly typed lambda calculus. *)
module type TYPED = sig
  type term
  val var: tp * sym -> term
  val lam: tp * tp * sym * term -> term
  (* app A B (M : A -> B) (N : A) *)
  val app: tp * tp * term * term -> term
end


(* ===== Normalisation by evaluation (intensional) =====
 * Based on http://homepages.inf.ed.ac.uk/slindley/nbe/nbe-cambridge2016.pdf
 *)
module Nbe(N: NORMAL) = struct
  type value = Neut of N.expr | Func of (value -> value)

  let rec reify: value -> N.term = function
    | Neut e -> N.expr e
    | Func f -> let x = gensym "_" () in
                N.lam (x, reify (f (Neut (N.var x))))

  (* TODO: better environment representation *)
  type env = (sym * value) list
  type term = env -> value
  let norm (t: term): N.term = reify (t [])

  let var (a,x) = List.assoc x
  let lam (a,b,x,m) env = Func (fun v -> m ((x,v)::env))
  let app (a,b,m,n) env = match m env with
    | Func f -> f (n env)
    | Neut f -> Neut (N.app (f, reify (n env)))
end
module Nbe_: NORMAL -> TYPED = Nbe


(* ===== LANGUAGES as EQUIRECURSIVE TYPES ==== *)
(* Normal & neutral term formers. *)
type ('norm, 'neut) neut = [ `Var of sym | `App of 'neut * 'norm ]
type ('norm, 'neut) norm = [ ('norm,'neut) neut | `Lam of sym * 'norm ]

(* Normal & neutral terms. *)
type neutral = (normal, neutral) neut
and  normal  = (normal, neutral) norm


(* Type-annotated bidirectional terms. *)
module Bidi = struct
  type expr = [ (term, expr) neut | `Asc of tp * term ]
  and term = [ (term, expr) norm | `Asc of tp * term ]
  let var x = `Var x let app x = `App x let lam x = `Lam x let asc x = `Asc x
  let expr x = (x :> term)

  (* Translate into another bidirectional system. *)
  module Elim(B: BIDI) = struct
    let rec doTerm: term -> B.term = function
      | `Lam (x,m) -> B.lam (x, doTerm m)
      | #expr as e -> B.expr (doExpr e)

    and doExpr: expr -> B.expr = function
      | `Asc (tp, tm) -> B.asc (tp, doTerm tm)
      | `Var x -> B.var x
      | `App (e,m) -> B.app (doExpr e, doTerm m)
  end
end
module Bidi_: BIDI = Bidi


(* A bidirectional type checker translates uses of an explicitly-typed language
 * into uses of a bidirectionally-typed one. *)
module Check(T: TYPED): BIDI
        with type term = cx -> tp -> T.term
        with type expr = cx -> tp * T.term
= struct
  type term = cx -> tp -> T.term
  type expr = cx -> tp * T.term

  let asc (a,m) cx = (a, m cx a)

  let expr e cx expected =
    let (inferred, term) = e cx in
    if expected = inferred then term
    else raise TypeError

  let var x cx =
    let a = try List.assoc x cx with Not_found -> raise TypeError
    in (a, T.var (a,x))

  let app (e,m) cx =
    match e cx with
    | (Fn(a,b), eterm) -> (b, T.app (a, b, eterm, m cx a))
    | _ -> raise TypeError

  let lam (x,m) cx = function
    | Fn(a,b) -> T.lam (a, b, x, m ((x,a)::cx) b)
    | _ -> raise TypeError
end


(* Now let's put these pieces together and make an actual typechecker! *)

end
