module Clase7.Imp

open FStar.Mul

type var = string

type expr =
  | Var   : var -> expr
  | Const : int -> expr
  | Plus  : expr -> expr -> expr
  | Minus : expr -> expr -> expr
  | Times : expr -> expr -> expr
  | Eq    : expr -> expr -> expr

type stmt =
  | Assign : var -> expr -> stmt
  | IfZ    : expr -> stmt -> stmt -> stmt
  | Seq    : stmt -> stmt -> stmt
  | Skip   : stmt
  | While  : expr -> stmt -> stmt

type state = var -> int

let rec eval_expr (s : state) (e : expr) : int =
  match e with
  | Var x -> s x
  | Const n -> n
  | Plus  e1 e2 -> eval_expr s e1 + eval_expr s e2
  | Minus e1 e2 -> eval_expr s e1 - eval_expr s e2
  | Times e1 e2 -> eval_expr s e1 * eval_expr s e2
  | Eq e1 e2 -> if eval_expr s e1 = eval_expr s e2 then 0 else 1

let override (#a:eqtype) (#b:Type) (f : a -> b) (x:a) (y:b) : a -> b =
  fun z -> if z = x then y else f z

(* Relación de evaluación big step. *)
noeq
type runsto : (p:stmt) -> (s0:state) -> (s1:state) -> Type0 =
  | R_Skip : s:state -> runsto Skip s s
  | R_Assign : s:state -> #x:var -> #e:expr -> runsto (Assign x e) s (override s x (eval_expr s e))

  | R_Seq :
    #p:stmt -> #q:stmt ->
    #s:state -> #t:state -> #u:state ->
    runsto p s t -> runsto q t u -> runsto (Seq p q) s u

  | R_IfZ_True :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto t s s' ->
    squash (eval_expr s c == 0) ->
    runsto (IfZ c t e) s s'

  | R_IfZ_False :
    #c:expr -> #t:stmt -> #e:stmt ->
    #s:state -> #s':state -> runsto e s s' ->
    squash (eval_expr s c <> 0) ->
    runsto (IfZ c t e) s s'

  | R_While_True :
    #c:expr -> #b:stmt -> #s:state -> #s':state -> #s'':state ->
    runsto b s s' ->
    squash (eval_expr s c = 0) ->
    runsto (While c b) s' s'' ->
    runsto (While c b) s s''

  | R_While_False :
    #c:expr -> #b:stmt -> #s:state ->
    squash (eval_expr s c <> 0) ->
    runsto (While c b) s s

// Demostrar que esta regla es admisible, es decir, que
// podemos "asumir" que la tenemos para demostrar, pero no
// necesitamos analizarla cuando destruímos una prueba:
//
// | R_While :
//   #c:expr -> #b:stmt ->
//   #s:state -> #s':state ->
//   runsto (IfZ c (Seq b (While c b)) Skip) s s' ->
//   runsto (While c b) s s'
let r_while (#c:expr) (#b:stmt) (#s #s' : state) (pf : runsto (IfZ c (Seq b (While c b)) Skip) s s')
  : runsto (While c b) s s'
= if (eval_expr s c) = 0
  then (
    match pf with
    | R_IfZ_True #c #seq #skip #s #s' rseq _ -> (
      match rseq with
      | R_Seq #b #while #s #s'' #s' rb rwhile -> R_While_True #c #b #s #s'' #s' rb () rwhile
    )
  )
  else R_While_False #c #b #s ()

type cond = state -> bool

noeq
type hoare : (pre:cond) -> (p:stmt) -> (post:cond) -> Type0 =
  | H_Skip : pre:cond -> hoare pre Skip pre // {P} Skip {P}
  | H_Seq :
    #p:stmt -> #q:stmt ->
    #pre:cond -> #mid:cond -> #post:cond ->
    hoare pre p mid -> hoare mid q post ->
    hoare pre (Seq p q) post  // {pre} p {mid} /\ {mid} q {post}    ==>    {pre} p;q {post}
  | H_Assign :
    #x:var -> #e:expr ->
    #pre:cond ->
    hoare (fun s -> pre (override s x (eval_expr s e))) (Assign x e) pre
  | H_If :
    #c:expr -> #t:stmt -> #e:stmt ->
    #pre:cond -> #post:cond ->
    hoare (fun s -> pre s && (eval_expr s c) = 0) t post ->
    hoare (fun s -> pre s && (eval_expr s c) <> 0) e post ->
    hoare pre (IfZ c t e) post
  | H_While :
    #e:expr -> #p:stmt ->
    #inv:cond ->
    hoare (fun s -> inv s && (eval_expr s e) = 0) p inv ->
    hoare inv (While e p) (fun s -> inv s && (eval_expr s e) <> 0)

let rec hoare_ok (p:stmt) (pre:cond) (post:cond) (pf : hoare pre p post)
                 (s0 s1 : state) (e_pf : runsto p s0 s1)
  : Lemma (requires pre s0)
          (ensures  post s1)
= match e_pf with
  | R_Skip _ -> ()
  | R_Assign _ -> ()
  | R_Seq #q #r #s0 #t #s1 rq rr -> (
    match pf with
    | H_Seq #q #r #pre #mid #post hq hr -> (
      hoare_ok q pre mid hq s0 t rq;
      hoare_ok r mid post hr t s1 rr
    )
  )
  | R_IfZ_True #c #q #r #s0 #s1 rq _ -> (
    match pf with
    | H_If #c #q #r #pre #post hq _ -> (
      hoare_ok q (fun s -> pre s && (eval_expr s c) = 0) post hq s0 s1 rq
    )
  )
  | R_IfZ_False #c #q #r #s0 #s1 rr _ -> (
    match pf with
    | H_If #c #q #r #pre #post _ hr -> (
      hoare_ok r (fun s -> pre s && (eval_expr s c) <> 0) post hr s0 s1 rr
    )
  )
  | R_While_True #c #q #s0 #s' #s1 rq _ rp -> (
    match pf with
    | H_While #c #q #pre hq -> (
      hoare_ok q (fun s -> pre s && (eval_expr s c) = 0) pre hq s0 s' rq;
      hoare_ok (While c q) pre (fun s -> pre s && (eval_expr s c) <> 0) pf s' s1 rp
    )
  )
  | R_While_False #c #q #s0 _ -> ()

let st0 : state = fun _ -> 0

let test1 : hoare (fun _ -> true) (Assign "x" (Const 1)) (fun s -> s "x" = 1) =
  H_Assign #"x" #(Const 1) #(fun s -> s "x" = 1)

