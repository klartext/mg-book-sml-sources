(* Some MG-Book SML functions implmented using OCaml StdLib *)
let append l m = l @ m
let reduce f u lst = List.fold_right f lst u
let flat = List.flatten
let member = List.mem
let pos n lst = List.nth lst (n-1)


(* Plainly ported stuff from SML to OCaml *)

let pair x y = (x,y)


let allpairs xs ys =
     flat(List.map(function x -> List.map (pair x) ys) xs)

exception Fromto

let rec fromto n m =
  if n>(m+1) then raise Fromto
  else if n=m+1 then []
  else n::fromto (n+1) m
  
let nlist = fromto 1



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

let pos n lst = List.nth lst (n-1)

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

