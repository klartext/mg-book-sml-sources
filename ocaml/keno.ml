exception Integer_arithmetic_overflow_or_underflow

(* Some MG-Book SML functions implmented using OCaml StdLib *)
let append l m = l @ m
let reduce f u lst = List.fold_right f lst u
let flat = List.flatten
let member = List.mem
let pos n lst = List.nth lst (n-1)
let exists = List.exists
let map = List.map
let length = List.length


(* Ported stuff from SML to OCaml *)

let pair x y = (x,y)


let allpairs xs ys =
     flat(map(function x -> map (pair x) ys) xs)

exception Fromto

(* create list with integers from n to m (ascending) *)
let rec fromto n m =
  if n>(m+1) then raise Fromto
  else if n=m+1 then []
  else n::fromto (n+1) m

(* create int list from 1 to the argument given *)
let nlist = fromto 1



(* create list of pairs with elemtn x as first member and list items as second member *)
let combine x l = map (function y -> (x,y)) l


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
let kmax ill = maximum (map maximum ill)

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


(* TNF: Trito Normalform (Wert-Abstraktion) *)
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



(* DNF: Deutero Normalform (Positions-Abstraktion) *)
let rec dnf ks =
    let rec count x lst = match x,lst with
        | _, []  -> 0
        | x, (y::ys) -> (if x=y then 1 else 0) + count x ys
    in
        flat (map (fun k -> nlistof (count k (tnf ks)) k)
                  (rd (tnf ks)))

(* PNF: Proto Normalform (Iterations-Abstraktion) *)
let pnf ks = (nlistof (List.length ks - List.length (rd ks)) 1)@tnf(rd ks)


(* comparison functions for trito/deutero/proto normal forms *)
let teq a b = (tnf a = tnf b)
let deq a b = (dnf a = dnf b)
let peq a b = (pnf a = pnf b)


(* number/cardinality of normal forms / aequivalence classes of PNF's *)
let pcard n = n

let rec sum start endval f =
    if (start > endval) then 0
    else (f start) + sum  ( start + 1) endval f



(* P / p: number of possible partitions *)
let rec p (x,y) = match x, y with
    | (n,1) -> 1
    | (n,k) ->
                 if k>n then 0
                 else if k=n then 1
                 else p(n-1,k-1) + p(n-k,k)


(* number/cardinality of normal forms / aequivalence classes of DNF's *)
let dcard n = sum 1 n (fun k -> p(n,k))


(* S / stirling: stirling number of the second kind  *)
let rec stirling (n,k) =
    match n, k with
        | n, 1 -> 1
        | n, k ->
                 if k > n then 0
                 else if k = n then 1
                 else stirling (n-1, k-1) + k * stirling (n-1, k)


(* number/cardinality of normal forms / aequivalence classes of TNF's *)
let tcard n = sum 1 n (fun k -> stirling(n,k))


(* calculating the PNF's of length n *)
let pcontexture n =
   map (fun k -> (nlistof (n-k) 1)@(nlist k))
       (nlist n)




let combine a l = map (fun x -> a::x) l

(* remove elem from lst *)
let rec remov elem lst =
    match elem, lst with
        | x, [] -> []
        | x, (y::ys) -> if (x=y) then ys else y :: remov x ys


(* create all permutations of elements in the input list as list of lists *)
let rec allperms li =
    match li with
        | []      -> []
        | [x]     -> [[x]]
        | [x;y]   -> [ [x;y]; [y;x] ]
        | l -> flat ( map (fun a -> combine a (allperms (remov a l))) l)


let rec allsums n k =
    match n, k with
        | n, 1 -> [[n]]
        | n, k ->
                    if (n = k) then [nlistof n 1]
                    else
                    flat ( map (fun e -> combine e (allsums (n-e) (k-1)))
                            (nlist (n-k+1)))


(* Exists -> List.exists, moved up *)

(* remove duplicates from lst - (?) should be functionally the same as function 'rd' from above *)
let rec remdups lst =
    match lst with
        | []         -> []
        |hd :: tl    -> if exists (fun x -> (member x tl)) (allperms hd)
                        then remdups tl
                        else hd::(remdups tl)


let allpartitions n k = remdups (allsums n k)

let pd_concrete ks =
   map (fun p -> flat (map (fun k -> nlistof (pos k p) k)
                         (nlist (length (rd ks)))))
       (allpartitions (length ks) (length (rd ks)))


(* calculating the DNF's of length n *)
let dcontexture n =
   flat(map pd_concrete (pcontexture n))



let dt_concrete ks =
    rd (map (fun i -> tnf i) (allperms ks))

let t_contexture n=
   flat(map dt_concrete (dcontexture n));


type en_t = E | N

let delta (i,j) z =
   if (pos i z) = (pos j z)
   then (i,j,E)
   else (i,j,N)

type enstruc = (int * int * en_t) list list


(* pairstructure n creates a strcuture of possible pairs for a sequence of length n *)
let pairstructure n =
   map ( fun j -> map (fun i -> (i,j))
                      (fromto 1 (j-1))
       ) (fromto 1 n)


(* epsilon/nu structrure *)
let en_structure z =
   map (fun trl -> map (fun pair -> delta pair z)
                      trl)
       (pairstructure (length z))

(* alternative implementation than before; see page 56 of mg-book *)
let teq a b = (en_structure a) = (en_structure b)


exception Entoks

(* epsilon/nu structure to kenogram sequence; mg-book page 56 *)
let en_to_ks (en_struc:enstruc) =
  let rec entoks1 li ks =
    match li, ks with
        | [], ks            -> ks
        |((f,s,en)::tl), ks ->
            begin
                let fir = pos f ks in
                let sec = if (length ks < s) then [] else pos s ks in

                 begin
                    match en, sec with
                        | E, [] -> entoks1 tl (ks@[fir])
                        | E, sec_ when member (List.hd fir) sec_ -> entoks1 tl (replace sec_ ks fir)
                        | E, sec_ when not (member (List.hd fir) sec_) -> raise Entoks
                        | N, [] -> entoks1 tl (ks@[remove (List.hd fir) (nlist ((kmax ks)+1))])
                        | N, sec_ when fir = sec_ -> raise Entoks
                        | N, sec_ when member (List.hd fir) sec_ -> entoks1 tl (replace sec_ ks (remove (List.hd fir) sec_))
                        | _ -> entoks1 tl ks
                 end
            end
  in
    (flat (entoks1 (flat en_struc) [[1]]))


