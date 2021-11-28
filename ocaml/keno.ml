exception Integer_arithmetic_overflow_or_underflow

(* Some MG-Book SML functions implmented using OCaml StdLib *)
let append l m = l @ m
let reduce f u lst = List.fold_right f lst u
let flat = List.flatten
let member = List.mem
let pos n lst = List.nth lst (n-1)


(* Ported stuff from SML to OCaml *)

let pair x y = (x,y)


let allpairs xs ys =
     flat(List.map(function x -> List.map (pair x) ys) xs)

exception Fromto

(* create list with integers from n to m (ascending) *)
let rec fromto n m =
  if n>(m+1) then raise Fromto
  else if n=m+1 then []
  else n::fromto (n+1) m
  
(* create int list from 1 to the argument given *)
let nlist = fromto 1



(* create list of pairs with elemtn x as first member and list items as second member *)
let combine x l = List.map (function y -> (x,y)) l


(* remove x from lst *)
let rec remove x lst =
  match lst with
    [] -> []
  | (hd::tl) -> 
        if (x=hd) then remove x tl
        else hd::(remove x tl)
       
(* get last element of l *)
let last l = List.hd(List.rev l)


(* get maximum element of list *)
let maximum = function
    [] -> invalid_arg "empty list"
  | x::xs -> List.fold_left max x xs

(* get maximum element of list of lists *)
let kmax ill = maximum (List.map maximum ill)

(* from lst get element on position n (1st elem means n = 1) *)
let pos n lst = List.nth lst (n-1)


(* replace item by w in lst *)
let rec replace item lst w =
    match lst with
    | [] -> []
    | hd::tl ->
                if (hd=item) then w::(replace item tl w)
                else hd::(replace item tl w)


(* remove duplicates from lst *)
let rec rd lst =
    match lst with
        | [] -> []
        | [x] -> [x]
        | hd::tl -> hd :: rd(remove hd tl)


(* create list with n elements, where each element is the given item *)
let rec nlistof n item =
    match n with
        | 0            -> []
        | x when x > 0 -> item :: nlistof (n-1) item
        | _            -> invalid_arg "neg. number"

(* Fakulaet (n!) *)
let rec _fak n = match n with
    | 0 -> 1
    | l -> l * _fak (l-1)

(* Fakulaet (n!) *)
(* wrapping _fak, because of int overflow issues; once there was a BitInt in OCaml Stdlib,
  but it has been removed. Zarith module could be used instead (as recommended), but so far
  I don't want to add additional dependencies. *)
let fak n =
    let res = _fak n in
    if res < 0 || n > 33 then raise Integer_arithmetic_overflow_or_underflow else res


(* number of combinations (n over k) AKA binomial coefficient *)
let choose n k =
   (fak n) / ((fak k) * fak (n-k))

(* power function (m^n) *)
let rec powers m n =
   if n=0 then 1
   else if n=1 then m
   else m*(powers m (n-1))



exception Place
type keno = int
type kseq = keno list


let tnf ks =
    let rec pos n lst = match n, lst with
        | _, [] -> raise Place
        | 1, (hd::tl) -> hd
        | n, (hd::tl) -> pos (n-1) tl

    and firstocc item lst =
      let rec place1 item liste n = match item,liste, n with
        | _ , [], _        -> raise Place
        | item, (x::xs), n -> if item=x then n
                                    else place1 item xs n+1
      in
        place1 item lst 1

    and nfirst n lst = match n, lst with
        | _, []       -> raise Place
        | 1, (hd::tl) -> [hd]
        | n, (hd::tl) -> hd::nfirst (n-1) tl

    and tnf1 lst res n k = match lst, res, n, k with
        | [], _, _ ,_ -> res
       |(hd::tl), res, 1, k -> tnf1 tl [1] 2 2
       |(hd::tl), res, n, k ->
          if member (pos n ks) (nfirst (n-1) ks)
          then tnf1 tl
                  (res@[pos (firstocc (pos n ks) ks) res])(n+1) k
          else tnf1 tl
                  (res@[k]) (n+1) (k+1)
  in
    tnf1 ks [] 1 1



(* DNF: Deutero Normalform *)
let rec dnf ks =
    let rec count x lst = match x,lst with
        | _, []  -> 0
        | x, (y::ys) -> (if x=y then 1 else 0) + count x ys
    in
        flat (List.map (fun k -> nlistof (count k (tnf ks)) k)
                  (rd (tnf ks)))


