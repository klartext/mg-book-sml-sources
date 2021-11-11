let append l m = l @ m


let rec reduce f u lst =
  match lst with
    [] -> u
  | (x::xs) -> f x (reduce f u xs)
 
let flat l = reduce append [] l

let pair x y = (x,y)


let allpairs xs ys =
     flat(List.map(function x -> List.map (pair x) ys) xs)

exception Fromto

let rec fromto n m =
  if n>(m+1) then raise Fromto
  else if n=m+1 then []
  else n::fromto (n+1) m
  
let nlist = fromto 1

let rec member x lst =
  match lst with
    [] -> false
  | (hd::tl) -> (x=hd) || member x tl


let combine x l = List.map (function y -> (x,y)) l


let rec remove x lst =
  match lst with
    [] -> []
  | (hd::tl) -> 
        if (x=hd) then remove x tl
        else hd::(remove x tl)
       
let last l = List.hd(List.rev l)


let maximum = function
    [] -> invalid_arg "empty list"
  | x::xs -> List.fold_left max x xs

let kmax ill = maximum (List.map maximum ill)

let rec pos n lst = 
  match lst with
    [] -> invalid_arg "empty list"
   | (hd::tl) -> 
      match n with
        1 -> hd 
      | m -> pos (m-1) tl

(*
*)


