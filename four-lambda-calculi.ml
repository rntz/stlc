type var = string
type tp = Base | Fn of tp * tp

(* Normal & neutral term formers. *)
type ('norm, 'neut) neutF
  = [ `Var of var
    | `App of 'neut * 'norm ]
type ('norm, 'neut) normF =
  [ ('norm, 'neut) neutF
  | `Lam of var * 'norm ]

(* Normal & neutral lambda-calculus terms *)
type norm = (norm,neut) normF
and  neut = (norm,neut) neutF

(* Bidirectionally-typed checking & synthesizing terms. *)
type check = (check, synth) normF
and  synth = [ (check, synth) neutF | `Asc of tp * check ]

(* Ordinary (not bidirectional or normal) lambda calculus terms. *)
type term = (term, term) normF

(* Lambda calculus terms, allowing type annotations. *)
type termAnn = [ (termAnn, termAnn) normF | `Asc of tp * termAnn ]

(* I just defined four different languages! Without unnecessarily
 * duplicating constructors! And I get free subtyping coercions between them!
 * Unfortunately, I do need to explicitly cast, because OCaml's type checker
 * isn't smart enough:
 *)
let norm2check (x: norm): check = (x :> check)
let neut2synth (x: neut): synth = (x :> synth)
let term2termAnn (x: term): termAnn = (x :> termAnn)
let check2termAnn (x: check): termAnn = (x :> termAnn)
let synth2termAnn (x: synth): termAnn = (x :> termAnn)

(* In my fantasy of an ideal structurally-typed FP language, the above functions
 * would be allowed but unnecessary; subtyping would handle these conversions
 * silently. *)
