module Clase5.Listas

open FStar.List.Tot

val sum_int : list int -> int
let rec sum_int xs =
  match xs with
 | [] -> 0
 | x::xs' -> x + sum_int xs'

(* Demuestre que sum_int "distribuye" sobre la concatenación de listas. *)
let rec sum_append (l1 l2 : list int)
  : Lemma (sum_int (l1 @ l2) == sum_int l1 + sum_int l2)
  = 
    match l1 with
    | [] -> ()
    | _::xs -> sum_append xs l2


(* Idem para length, definida en la librería de F*. *)
let rec len_append (l1 l2 : list int)
  : Lemma (length (l1 @ l2) == length l1 + length l2)
  =
    match l1 with
    | [] -> ()
    | _::xs -> len_append xs l2

let rec snoc (xs : list int) (x : int) : list int =
  match xs with
  | [] -> [x]
  | y::ys -> y :: snoc ys x

(* unit-tests *)
let _ = assert (snoc [1;2;3] 4 == [1;2;3;4])
let _ = assert (snoc [1;2;3] 5 == [1;2;3;5])

let rec rev_int (xs : list int) : list int =
  match xs with
  | [] -> []
  | x::xs' -> snoc (rev_int xs') x

let rec snoc_append (xs ys : list int) (z : int)
  : Lemma (snoc (xs @ ys) z = xs @ snoc ys z)
  = match xs with
    | [] -> ()
    | _::xss -> snoc_append xss ys z

let rec rev_append_int (xs ys : list int)
  : Lemma (rev_int (xs @ ys) == rev_int ys @ rev_int xs)
= match xs with
  | [] -> ()
  | x::xs' -> (
    //assert (rev_int ((x :: xs') @ ys) = rev_int (x :: (xs' @ ys)));
    //assert (rev_int (x :: (xs' @ ys)) = snoc (rev_int (xs' @ ys)) x);
    rev_append_int xs' ys;
    //assert (snoc (rev_int (xs' @ ys)) x = snoc (rev_int ys @ rev_int xs') x);
    snoc_append (rev_int ys) (rev_int xs') x
    //assert (snoc (rev_int ys @ rev_int xs') x = rev_int ys @ snoc (rev_int xs') x);
    //assert (rev_int ys @ snoc (rev_int xs') x = rev_int ys @ rev_int xs)
  )

let rec snoc_int (xs : list int) (y : int)
  : Lemma (snoc xs y = xs @ [y])
  = match xs with
    | [] -> ()
    | _::xss -> snoc_int xss y

let rec rev_rev (xs : list int)
  : Lemma (rev_int (rev_int xs) == xs)
= 
  match xs with
  | [] -> ()
  | x::xss -> (
    //assert (rev_int (rev_int xs) == rev_int (rev_int (x::xss)));
    //assert (rev_int (rev_int (x::xss)) = rev_int (snoc (rev_int xss) x));
    snoc_int (rev_int xss) x;
    //assert (rev_int (snoc (rev_int xss) x) = rev_int (rev_int xss @ [x]));
    rev_append_int (rev_int xss) [x];
    //assert (rev_int (rev_int xss @ [x]) = rev_int [x] @ rev_int (rev_int xss));
    //assert (rev_int [x] @ rev_int (rev_int xss) = [x] @ rev_int (rev_int xss));
    rev_rev xss
    //assert ([x] @ rev_int (rev_int xss) = [x] @ xss);
    //assert ([x] @ xss = xs)
  )

let rev_injective (xs ys : list int)
  : Lemma (requires rev_int xs == rev_int ys) (ensures xs == ys)
= rev_rev xs;
  //assert (xs = rev_int (rev_int xs));
  //assert (rev_int (rev_int xs) = rev_int (rev_int ys));
  rev_rev ys
  //assert (rev_int (rev_int ys) = ys)
