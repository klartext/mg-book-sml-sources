(* Kapitel 4 Kenogrammatik *)
fun append l m = l @ m;

fun reduce f u [] = u
   |reduce f u (x::xs)=
        f x (reduce f u xs);
        
fun flat l = reduce append [] l

fun pair x y =(x,y);

fun allpairs xs ys=
     flat(map(fn x=> map (pair x) ys) xs);

exception Fromto;
fun fromto n m=
  if n>(m+1) then raise Fromto
  else if n=m+1 then []
  else n::fromto (n+1) m;
  
val nlist = fromto 1;
      
      
fun member x [] = false
   |member x (hd::tl) = (x=hd) orelse member x tl;

fun combine x l = map (fn y => (x,y)) l;

fun remove x [] =[]
   |remove x (hd::tl) = 
        if (x=hd) then remove x tl
        else hd::(remove x tl);
        
fun last l= hd(rev l);

fun kmax ill = max (map max ill)
and max l = max1 0 l
and max1 n [] = n
   |max1 n (hd::tl)= if n>hd then max1 n tl
                     else max1 hd tl;

exception Place;   
fun pos n [] = raise Place
   |pos 1 (hd::tl) = hd
   |pos n (hd::tl) = pos (n-1) tl;

fun replace item [] w = []
   |replace item (hd::tl) w =
        if (hd=item) then w::(replace item tl w)
        else hd::(replace item tl w);

fun rd []=[]
   |rd [x]=[x]
   |rd (x::xs) = x::rd(remove x xs);

fun nlistof 0 x = []
   |nlistof n x = x::nlistof (n-1) x;

fun fak 0=1
   |fak n= n * fak (n-1);

fun choose n k=
   (fak n) div ((fak k)* fak (n-k));

fun powers m n=
   if n=0 then 1
   else if n=1 then m
   else m*(powers m (n-1));
   

type keno = int;
type kseq = keno list;

fun tnf ks =
  let
    fun pos n [] = raise Place
       |pos 1 (hd::tl) = hd
       |pos n (hd::tl) = pos (n-1) tl;
       
    fun firstocc item list =
      let
        fun place1 item [] n = raise Place
           |place1 item (x::xs) n = if item=x then n
                                    else place1 item xs n+1;
      in
        place1 item list 1
      end; 
    
    fun nfirst n [] =raise Place
       |nfirst 1 (hd::tl)=[hd]
       |nfirst n (hd::tl)=hd::nfirst (n-1) tl;
       
    fun tnf1 [] res n k = res
       |tnf1 (hd::tl) res 1 k = tnf1 tl [1] 2 2
       |tnf1 (hd::tl) res n k =
          if member (pos n ks) (nfirst (n-1) ks)            
          then tnf1 tl 
                  (res@[pos (firstocc (pos n ks) ks) res])(n+1) k          
          else tnf1 tl 
                  (res@[k]) (n+1) (k+1);  
  in        
    tnf1 ks [] 1 1  
  end;
  
  
  fun dnf ks =
  let
    fun count x []= 0
       |count x (y::ys)= (if x=y then 1 else 0)+count x ys;
  in
    flat (map (fn k=> nlistof (count k (tnf ks)) k)
              (rd (tnf ks)))
  end;


fun pnf ks = (nlistof (length ks - length(rd ks)) 1)@tnf(rd ks);


fun teq a b = (tnf a = tnf b);

fun deq a b = (dnf a = dnf b);

fun peq a b = (pnf a = pnf b);


fun Pcard n = n;

fun sum from to f=
        if (from > to) then 0
        else (f from) + sum  ( from + 1) to f;

fun P (n,1) = 1
   |P (n,k) =
     if k>n then 0
     else if k=n then 1
     else P(n-1,k-1) + P(n-k,k);

fun Dcard n = sum 1 n (fn k => P(n,k));


fun S (n,1) = 1
   |S (n,k) =
     if k>n then 0
     else if k=n then 1
     else S(n-1,k-1) + k*S(n-1,k);

fun Tcard n = sum 1 n (fn k => S(n,k));


fun Pcontexture n =
   map (fn k => (nlistof (n-k) 1)@(nlist k))
       (nlist n);


fun allperms []=[]
   |allperms [x]=[[x]]
   |allperms [x,y]=[[x,y],[y,x]]
   |allperms l=
     let
      fun remov x [] =[]
         |remov x (y::ys) = if (x=y) then ys
                            else y::remov x ys;
      fun combine a l=
         map (fn x => a::x) l;
     in
      flat ( map (fn a => combine a (allperms (remov a l)))
                 l)
     end;

fun combine a l=
         map (fn x => a::x) l;
          
fun allsums n 1=[[n]]
   |allsums n k= 
     if (n=k) then [nlistof n 1]
     else 
       flat(map (fn e => combine e (allsums (n-e) (k-1)))
                (nlist (n-k+1)));               

fun allpartitions n k=
  let
    fun Exists f [] = false
       |Exists f (hd::tl)= 
          if (f hd) then true
          else Exists f tl;
    fun remdups [] = []
       |remdups (hd::tl)=
          if Exists (fn x => (member x tl)) (allperms hd)
            then remdups tl
            else hd::(remdups tl);
  in
   remdups (allsums n k)
  end;
               
fun PDconcrete ks =
   map (fn p => flat (map (fn k => nlistof (pos k p) k)
                         (nlist (length (rd ks)))))
       (allpartitions (length ks) (length (rd ks)));

fun Dcontexture n =
   flat(map PDconcrete (Pcontexture n));


fun DTconcrete ks =
   rd(map (fn i => tnf i)
          (allperms ks));

fun Tcontexture n=
   flat(map DTconcrete (Dcontexture n));


datatype EN = E|N;

fun delta (i,j) z=
   if (pos i z) = (pos j z)
     then (i,j,E)
     else (i,j,N);


type enstruc = (int*int*EN) list list;

(* pairstructure n erzeugt die Struktur der m"oglichen Paare
   f"ur eine Sequenz der L"ange n *)
fun pairstructure n =
   map (fn j => map (fn i => (i,j))
                    (fromto 1 (j-1)))
       (fromto 1 n);

fun ENstructure z =
   map (fn trl => map (fn pair => delta pair z)
                      trl)
       (pairstructure (length z));


fun teq a b = (ENstructure a) = (ENstructure b);

exception Entoks;
fun ENtoKS enstruc = 
  let
   fun entoks1 [] ks = ks 
      |entoks1 ((f,s,en)::tl) ks =
        let 
          val fir = pos f ks;
          val sec = if (length ks< s) then [] else pos s ks;
        in
         (if (en=E andalso sec=[])
          then entoks1 tl (ks@[fir])
          else if (en=E andalso member (hd fir) sec)
            then entoks1 tl (replace sec ks fir)
          else if (en=E andalso not(member (hd fir) sec))
            then raise Entoks
          else if (en=N andalso sec=[])
            then entoks1 tl (ks@[remove (hd fir) 
                         (nlist ((kmax ks)+1:int))])
          else if (en=N andalso fir=sec) 
            then raise Entoks
          else if (en=N andalso member (hd fir) sec)
            then entoks1 tl (replace sec ks
                                     (remove (hd fir) sec))
          else entoks1 tl ks)
        end;
  in               
    (flat (entoks1 (flat enstruc) [[1]]))
  end;


fun Tref ks = tnf(rev ks);
fun Dref ks = dnf(Tref ks);
fun Pref ks = pnf(Tref ks);

val a=[1,2];
val b=[1,2,3,4];

fun AG ks = length (rd ks);

fun EE (n,k) =
  let
   fun combinec item list= map (fn x=> item::x) list;
   fun max  (x : int) y= if x>y then x else y;
   fun mkfg from to 0 = [[]]
      |mkfg from to step=
         flat(map (fn i => combinec i (mkfg (i+1) to (step-1)))
             (fromto from (max from to)));
  in
   mkfg  1 (n+1) k
  end;

fun mappat pat template=
   map (fn x => pos x template) pat;

fun mkpats a b =
  let
   fun max (x:int) y= if x>=y then x
                else y;
   fun free n ([] : int list) = []
      |free n (hd::tl) =
          if hd<=n then hd::(free n tl)
          else [];
   fun possperms [] ag=[]
      |possperms [x] ag = [[x]]
      |possperms rest ag=
         flat(map (fn k=> combine k (possperms (remove k rest)
                                               (max k (ag))))
                  (free (ag+1) rest ));          
  in
   flat
     (map (fn e => possperms e (AG a))
          (EE (AG a,AG b)))
  end;  
   
fun combinea item list=
   map (fn x=> item@x) list;
         
fun kconcat ks1 ks2=
   combinea ks1 (map (fn pat => mappat ks2 pat)
                     (mkpats ks1 ks2));


fun Dconcat a b = rd (map dnf (kconcat a b));
fun Pconcat a b = rd (map pnf (kconcat a b));


fun Ekard (n,k) =
  let
   fun max (x: int) y = if x>y then x else y;
   fun Xi from to 0 = 1
      |Xi from to step=
         sum from to (fn i => Xi (i+1) (max to (i+1)) (step-1));
  in
   Xi 1 (n+1) k
  end;

fun NN (a,b) =
  let
   val M = EE ((AG a),(AG b));
   fun e i =pos i M;
   fun gn [] = 0
      |gn (x::xs) = if (x>((AG a)+1)) then 1+(gn xs)
                  else gn xs;
  in
   sum 1 (Ekard(AG a,AG b)) 
       (fn i => (fak (length (e i))) div (fak(1+gn(e i))) )
  end;

fun collfits a [] rule = []
   |collfits a (b::bs) (rule as (x,y,en))= 
       if ((en=E) andalso ((pos x a)=(pos (y) b))) 
       then 
         b::collfits a bs rule       
       else if ((en=N) andalso ((pos x a)<>(pos (y) b))) 
       then                
         b::collfits a bs rule 
       else collfits a bs rule; 


(*
fun collfits a [] rule = []
   |collfits a (b::bs) (rule as (x,y,en))= 
       if ((en=E) andalso ((pos x a)=(pos (y-(length a)) b))) 
       then 
         b::collfits a bs rule       
       else if ((en=N) andalso ((pos x a)<>(pos (y-(length a)) b))) 
       then                
         b::collfits a bs rule 
       else collfits a bs rule; 
*)

fun mapvermat a bs []=bs
   |mapvermat a [] enstruc = []
   |mapvermat a bs (rule::rules)=
       mapvermat a (collfits a bs rule) rules;

fun kligate a b enstruc =
   combinea a
            (mapvermat a 
                       (map (fn pat => mappat b pat)
                            (mkpats a b))     
                       enstruc);

(* Kapitel 5 Kenoarithmetik*)


exception Pis;
fun PIS (n,k) = if k=n then raise Pis
                else (n,k+1);
fun PTS0 (n,k) = (n+1,k);
fun PTS1 (n,k) = (n+1,k+1);

fun firstocc item list =
              let
                fun place1 item [] n = raise Place
                   |place1 item (x::xs) n = if item=x then n
                                            else place1 item xs n+1;
              in
                place1 item list 1
              end; 

fun nfirst n [] =raise Place
   |nfirst 0 _ = []
   |nfirst 1 (hd::tl)=[hd]
   |nfirst n (hd::tl)=hd::nfirst (n-1) tl;
   
fun forall [] p = true
   |forall (x::xs) p = if (p x)= false then false
                       else forall xs p;

exception Dis;
fun DIS D =
  if (forall D (fn x => x=1)) then raise Dis
  else
   let
     val m = sum 1 (length D) (fn i => (pos i D))
     val i = ((firstocc 1 D) - 1) handle Place => (length D)
     val pi = (pos i D)-1
     val u = m - (sum 1 (i-1) (fn k => (pos k D)))
     val j = u div pi
     val rest = u mod pi
     val news = map (fn x => pi) (fromto 1 (j-1)) ;
   in
     (nfirst (i-1) D) @ [pi] @ news @ (if rest=0 then [] 
                                        else [rest])
   end; 



fun remnils []=[]
   |remnils (hd::tl) = if hd=[] then remnils tl
   		       else hd::(remnils tl);
		       
fun replacepos n list w=
    let
     exception Replace;
     fun replacepos1 n [] x m= raise Replace
        |replacepos1 n (hd::tl) x m=
           if n=m then x::tl
           else hd::(replacepos1 n tl x (m+1));
    in
     replacepos1 n list w 1
    end;

fun DTS D =
   [((pos 1 D)+1)::(tl D)] @
   (remnils (map (fn i => if (pos i D) > (pos (i+1) D) 
                          then replacepos (i+1) D ((pos (i+1) D)+1)
                          else [])
                 (fromto 1 ((length D)-1)))) @
   [D@[1]]
  
datatype 'a seq = Nil
                | Cons of 'a * (unit -> 'a seq);

fun head (Cons (x,_))=x;
fun tail (Cons(_,xf))=xf();

fun nfirstq (0, xq)=[]
   |nfirstq (n, Nil)=[]
   |nfirstq (n, Cons(x,xf))= x::(nfirstq (n-1, xf ()));

fun ifrom k = Cons(k,fn ()=> ifrom(k+1));

exception Tis;
fun TIS ts=
  let
   val n=length ts;
   fun lastrep []=[]
      |lastrep seq=
        let
         fun member x []=false
            |member x (y::ys)= (x=y) orelse member x ys;
         val (last::rest) = rev seq;
        in
         if (member last rest) then seq
         else lastrep (rev rest)
        end;
  in
   if (pos n ts)=n then raise Tis
    else if (last ts) <= (max (nfirst (n-1) ts))
          then (nfirst (n-1) ts) @ [1+(last ts)]
    else let
          val first = rev(lastrep (nfirst (n-1) ts));
         in
          (rev (tl first))@[1+(hd first)]@(nlistof (n-(length first)) 1)
         end
  end;

fun Tsucc(ts) = TIS(ts)
        handle Tis =>(nlistof ((length ts)+1) 1);



fun from k = Cons(k,fn () => from (Tsucc k));

val TU = from [1];





fun kmul [] b = [[]]
   |kmul a [] = [[]]
   |kmul a [1] = [a]
   |kmul [1] b = [b]
   |kmul a b = 
     let
        fun makeEN a k [] = []
           |makeEN a k kyet=
             flat(map 
                  (fn mem => map 
                              (fn p => (((firstocc mem b)-1)*(length a)+p,
                                       p,
                                       if (k=mem) then E 
                                       else N))
                                              
                              (nlist(length a)))
                                 
                   (rd kyet));
               
        fun kmul1 a [] used res = res 
           |kmul1 a (hd::tl) used res =
              kmul1 a tl (hd::used)
                 (flat(map (fn x => kligate x a 
                                       (makeEN a hd used))
                           res));        
     in
        kmul1 a b [] [[]]
     end;

(* Kapitel 6 Morphogrammatik*)

val Q = Tcontexture 4;
  
exception Mg;
fun mg i = if i<1 orelse i>15 then raise Mg  
           else pos i Q;  

type 'a mat = 'a list list;

fun maufn m n= 
  let 
   fun combine it list= map (fn x=> it::x) list; 
   fun maufn1 n []=[] 
      |maufn1 0 l =[] 
      |maufn1 1 l = map (fn x=> [x]) l 
      |maufn1 p l = 
         flat(map (fn x => combine x (maufn1 (p-1) (remove x l))) 
                  l); 
   fun remdups []=[] 
      |remdups ([x,y]::tl)= 
         if x=y then remdups tl 
         else if member [y,x] tl then [x,y]::(remdups(remove [y,x] tl)) 
         else [x,y]::(remdups tl); 
  in 
   remdups(maufn1 n (nlist m)) 
  end; 
  
fun matpos i j c= 
   pos j (pos i c); 
    
fun sort l= 
  let 
     exception Assoc; 
     fun assoc n []= raise Assoc 
        |assoc n ((k,pair)::tl)= 
           if n=k then (k,pair) 
           else assoc n tl; 
  in 
   map (fn k=> assoc k l) 
       (nlist (length l)) 
  end;  
  
fun k (i,j)=((j*(j-1)) div 2)-i+1;  
  
fun subsystems n= 
  sort(map (fn [i,j] => (k(i,j),[i,j])) 
             (maufn n 2)); 
                
fun LL (w: ''a mat)= 
  let 
   val n = length w; 
  in 
   tnf(flat (map (fn (k,[i,j])=> [matpos i i w,matpos i j w, 
                                  matpos j i w,matpos j j w]) 
             (subsystems n)))    
  end;     

fun set (i,j,x,mat)=
  let
   fun replacepos n list w=
    let
     exception Replace;
     fun replacepos1 n [] x m= raise Replace
        |replacepos1 n (hd::tl) x m=
           if n=m then x::tl
           else hd::(replacepos1 n tl x (m+1));
    in
     replacepos1 n list w 1
    end;
  in
   replacepos i mat (replacepos j (pos i mat) x)
  end;

fun L_1 kseq = 
  let
   val epsilon = 0.0000000001;
   exception Subsystems; 
   val n = 0.5+Math.sqrt(0.25+real((length kseq) div 2));
   val n = if real(floor n) - n <= epsilon then floor n 
           else raise Subsystems; 
   val subs = subsystems n; 
   val mat = nlistof n (nlistof n 0); 
   fun kstomm [] subs mat=mat 
      |kstomm (ii::ij::ji::jj::restks)  
              ((k,[i,j])::restpairs)  
              mat= 
         kstomm restks  
                restpairs 
                (set (i,i,ii, 
                       (set (i,j,ij, 
                              (set (j,i,ji, 
                                     (set (j,j,jj, mat))))))))  
  in 
   kstomm kseq subs mat 
  end;  


fun TNFMM (w: ''a mat) = L_1(LL w);  


type mg = kseq; 
type mgchain = mg list;  
  
fun makemg i j c= 
   tnf [matpos i i c,matpos i j c,matpos j i c,matpos j j c]; 
    
fun decompose mm = 
  let 
   val n = length mm; 
  in 
   map (fn (k,[i,j])=> makemg i j mm) 
        (subsystems n)
  end;     


fun makeEN (k,ik,jk) subsystems= 
   flat(map (fn (l,[il,jl])=> 
               if il=ik then [((l-1)*4+1,1,E)] 
          else if il=jk then [((l-1)*4+1,4,E)] 
          else if jl=jk then [((l-1)*4+4,4,E)] 
          else if jl=ik then [((l-1)*4+4,1,E)] 
          else []) 
            (nfirst (k-1) subsystems)); 
        
fun kligs x ys ENS= 
   flat (map (fn y=> kligate y x ENS) 
       ys); 
    
fun compose1 [] (subs:(int*int list) list) res subsystems=res 
   |compose1 (hd::tl) ((k,[ik,jk])::subs) res subsystems= 
     (compose1 tl  
               subs  
               (kligs hd  
                      res  
                      (makeEN (k,ik,jk) subsystems))  
               subsystems); 

fun kstomm [] subs mat=mat
   |kstomm (ii::ij::ji::jj::restks) ((k,[i,j])::restpairs) mat=
     kstomm restks restpairs
            (set (i,i,ii,(set (i,j,ij,(set (j,i,ji,(set (j,j,jj, mat)))))))) ;
            
fun Kom mk =
  let   
   exception Compose;
   val epsilon = 0.0000000001;
   val n = 0.5+Math.sqrt(0.25+real(2*(length mk)));
   val n = if real(floor n) - n <= epsilon then floor n
           else raise Compose;
   val mat= nlistof n (nlistof n 1);
   val subsystems =subsystems n;
  in
   map (fn ks=> kstomm ks subsystems mat)
       (compose1 mk subsystems [[]] subsystems) 
  end;
     

         
fun remzeros [] = []
   |remzeros (0::tl) = remzeros tl
   |remzeros (hd::tl) = hd::(remzeros tl);

exception Assoc
fun assoc x [] = raise Assoc
   |assoc x ((y,z)::rest) = if x=y then z
                            else assoc x rest;


fun filter p [] = []
   |filter p (x::xs) =
      if p x then x :: filter p xs
      else filter p xs;
fun mem xs x = member x xs;

fun difference s t =
  filter (not o mem t) s;

fun intersection s t=
   filter (mem s) t;

fun seteq a b =
   (difference a b)= [] andalso (difference b a) = [];

fun disjuncts subs n=
  let
   fun intersected sk sl =
      let
        val subsystems = subsystems n;
        val [ik,jk] = assoc sk subsystems;
        val [il,jl] = assoc sl subsystems;
      in
       (il=ik) orelse (il=jk) orelse (jk=jl) orelse (jl=ik)
      end;
   fun allintersectedwith si =
      remzeros(map (fn sj => if (intersected si sj) then sj
                             else 0)
                   (subs));

   fun allconnectedto sis =
      let
        val step = rd(flat(map allintersectedwith sis));
      in
        if (seteq sis step) then sis
        else allconnectedto step
      end;

   fun alldisjunctions [] =[]
      |alldisjunctions (hd::tl) =
        let
         val thisdisj = allconnectedto [hd];
         val rest = difference (hd::tl) thisdisj;
        in
         if rest=[] then [thisdisj]
         else thisdisj::(alldisjunctions rest)
        end;
  in
   alldisjunctions subs
  end;



fun hauptdiag disj n =
  let
   val positions = rd (flat (map (fn s =>  (assoc s (subsystems n)))
                                 disj));
   val hdiag = map (fn pos => if (member pos positions) then pos
                              else 0)
                   (nlist n);
   fun split [] os = (os,[])
      |split (0::rest) os = split rest (0::os)
      |split x os = (os,x);


   val (leados,rest) = split hdiag [];
   val (followos,revdisj) = split (rev rest) [];
   val revdiag = leados@revdisj@followos
  in
   map (fn p => if (pos p hdiag)= 0 andalso
                     (pos p revdiag)= 0 then 0
                  else p)
       (nlist n)
  end;

fun exists pred []      = false
   |exists pred (x::xs) = if pred x then true else exists pred xs;

fun alltouchedby disj alldisj n =
  let
   fun remdups [] res = res
      |remdups (hd::tl) res =
	if (member hd res) then remdups tl res
	else remdups tl (hd::res);
   val touched= map k
                    (remdups (allpairs (remzeros (hauptdiag disj n))
			               (remzeros (hauptdiag disj n)))
			      []);
  in
   rd(flat(remnils(map (fn disi => if (exists (fn s => member s touched) 
					      disj)
                                   then disi
                                   else [])
                       alldisj)))
  end;


fun allRBs [] n = []
   |allRBs (hd::tl) n =
     let
        val thisRB = hd@(alltouchedby hd tl n);
        val rest = difference (flat (hd::tl)) thisRB
     in
        if rest=[] then [thisRB]
        else thisRB::(allRBs (disjuncts rest n) n)
     end;


fun reflectRB RB mat=
 let
  val n = length mat;
  fun poke [] m = m
     |poke (si::tl) m =
        let
         val [i,j] = assoc si (subsystems n);
        in
 	 poke tl
         (set (i,i,pos i (pos i mat),
         set (i,j,pos j (pos i mat),
         set (j,i,pos i (pos j mat),
         set (j,j,pos j (pos j mat),m)))))
        end;

  fun split [] os = (os,[])
     |split (0::rest) os = split rest (0::os)
     |split x os = (os,x);

  val rhomat = poke RB (nlistof n (nlistof n 0));

  val (leados,rest) = split (flat rhomat) [];
  val (followos,revrho) = split (rev rest) [];
  val flatmat = flat mat;
  val flatrhomat = (leados @ revrho @ followos);
exception Nthcdr;
fun nthcdr n [] = raise Nthcdr
   |nthcdr 0 liste = liste
   |nthcdr n (hd::tl) = nthcdr (n-1) tl;

fun elements n m liste=
  nfirst (m-n+1) (nthcdr n liste);


fun mkmat n liste =
   map (fn z => elements (z*n) (z*n+n-1) liste)
       (fromto 0 (n-1));
 in
  mkmat n (map (fn i => if (pos i flatrhomat)=0 then (pos i flatmat)
                     else (pos i flatrhomat))
               (nlist (n*n)))
 end;


fun reflectall [] mat = mat
   |reflectall (RB::rest) mat =
           reflectall rest (reflectRB RB mat);

fun r I mat=
   reflectall (allRBs (disjuncts I (length mat)) (length mat)) mat;

fun pot [] = [[]]
   |pot [x] = [[],[x]]
   |pot (hd::tl) =
     let
        val half = pot tl
     in
        half@(map (fn l => hd::l)
                 half)
     end;

fun RG n =
  map (fn I => r I)
      (remnils (pot (rev (nlist (choose n 2)))));


(* Kapitel 7 Klassifikation des Operandensystems*)

datatype fc = F|C; 
 
fun FCstructure hd = 
  map (fn (k,[i,j]) => if (pos i hd)=(pos j hd) then C 
            else F) 
    (subsystems (length hd));


fun allFCs n = 
  rd(map (fn ks => FCstructure ks) 
    (Tcontexture n)); 


fun FCtype mg = if (pos 1 mg)=(pos 4 mg) then C 
        else F; 
fun FCtypes MK = 
  map (fn mg => FCtype mg) 
    MK; 
 
 
fun exmm MK = 
  if (member (FCtypes MK) 
       (allFCs (floor(0.5+Math.sqrt(0.25+ 
                      real(2*(length MK))))))) 
  then true 
  else false; 

datatype gh=G|H;
fun ghtyp mg=
   if (pos 2 mg)=(pos 3 mg) then H
   else G;

fun GHtypes mk = map ghtyp mk;

datatype klor =K|L|O|R;

fun klortyp mg=
  if (pos 1 mg) = (pos 4 mg)
    then if (pos 2 mg)=(pos 3 mg)
           then O
           else R
    else if (pos 2 mg)=(pos 3 mg) 
           then L
           else K;

fun KLORtypes mk = map klortyp mk;


(*Kapitel 9 Kombinatorische Analyse der Polysemie*)

fun sum from to f=        
   if (from > to) then 0        
   else (f from) + sum  ( from + 1) to f;
   
fun S (n,1) = 1   
   |S (n,k) =     
     if k>n then 0     
     else if k=n then 1     
     else S(n-1,k-1) + k*S(n-1,k);


fun NF m = sum 1 m (fn k => S(m,k));


fun P (n,1) = 1
   |P (n,k) =
     if k>n then 0
     else if k=n then 1
     else P(n-1,k-1) + P(n-k,k);


fun GF m = sum 1 m (fn k => P(m,k));

fun fak 0=1
   |fak n= n * fak (n-1);

fun choose n k=
   (fak n) div ((fak k)* fak (n-k));

fun powers m n=
   if n=0 then 1
   else if n=1 then m
   else m*(powers m (n-1));


fun sigma n11 n12 n13 n22 n23 n24=
  let
   val l1=n11+n12+n13;
   val l2=n22+n23+n24;
  in
    ((fak l1) div ((fak n11)*(fak n12)*(fak n13)))
   * (powers 3 n12) *
    ((fak l2) div ((fak n22)*(fak n23)*(fak n24)))
   * (powers 4 n22) * (powers 5 n23)
  end;


fun max []=0
   |max [x]=x
   |max (x::xs)=
     let
      val restmax = max xs;
     in
      if (x > restmax) then x else restmax
     end;
fun k n= n;

fun RR n11 n12 n13 n22 n23 n24=
  let
   val kJ = if (n11+n12+n13)=3 then 1
            else if (n22+n23+n24)=3 then 3
            else 2;
  in
   max (kJ::(map (fn (n,j,r) => if (n=0) then 0
                                else (k j)+r)
                   [(n11,1,0),(n12,1,1),(n13,1,2),
                    (n22,2,0),(n23,2,1),(n24,2,2)]))
  end;


fun M n11 n12 n13 n22 n23 n24=
  let
   val kJ = if (n11+n12+n13)=3 then 1
            else if (n22+n23+n24)=3 then 3
            else 2;
  in
   kJ + n12 + (2*n13) + n23 + (2*n24)
  end;


fun dr n2 n3=
  if n3<>0 then 2
  else if n2<>0 then 1
  else 0;


exception A
fun a1 (n1,n2,n3,m,j) =
   if (j=1) andalso 
      ((m<(RR n1 n2 n3 0 0 0)) orelse (m>(M n1 n2 n3 0 0 0))) 
      then 0
   else if j=2 andalso 
           ((m<(RR 0 0 0 n1 n2 n3)) orelse (m>(M 0 0 0 n1 n2 n3)))
      then 0 
   else if n1=n1+n2+n3 then 1
   else if n3<>0 then
    sum 0 (dr n2 n3)
         (fn q => (choose (m-(k j)-q) ((dr n2 n3)-q))
                 *((fak(dr n2 n3)) div (fak q))
                 *a1(n1+1,n2,n3-1,m-q,j))
   else
     sum 0 (dr n2 n3)
         (fn q => (choose (m-(k j)-q) ((dr n2 n3)-q))
                 *((fak(dr n2 n3)) div (fak q))
                 *a1(n1+1,n2-1,n3,m-q,j));

exception B;
fun a (n11,n12,n13,n22,n23,n24,m) =
 let
   val J = if (n11+n12+n13)=3 then 1
            else if (n22+n23+n24)=3 then 3
            else if (n11+n12+n13+n22+n23+n24)=3 then 2
            else raise A;
 in
   if (m<(RR n11 n12 n13 n22 n23 n24))
       orelse (m>(M n11 n12 n13 n22 n23 n24)) 
      then 0
   else if J=1 then a1(n11,n12,n13,m,1)
   else if J=3 then a1(n22,n23,n24,m,2)
   else if n11=1 andalso n22=2 then 1
   else if (n12>0 orelse n13>0) then
     sum 0 (dr n12 n13)
         (fn q => (choose (m-(k 1)-q) ((dr n12 n13)-q))
                 *((fak(dr n12 n13)) div (fak q))
                 *a(n11+1,if n12=0 then 0 else n12-1,
                          if n13=0 then 0 else n13-1,
                    n22,n23,n24,m-q))
   else if (n24>0) then
     sum 0 (dr n23 n24)
         (fn q => (choose (m-(k 2)-q) ((dr n23 n24)-q))
                 *((fak(dr n22 n24)) div (fak q))
                 *a(n11,n12,n13,n22+1,n23,if n24=0 then 0 
                                          else n24-1,m-q))
   else if (n23>0) then
     sum 0 (dr n23 n24)
         (fn q => (choose (m-(k 2)-q) ((dr n23 n24)-q))
                 *((fak(dr n22 n24)) div (fak q))
                 *a(n11,n12,n13,n22+1,if n23=0 then 0 
                                      else n23-1,n24,m-q))
   else raise B
  end;


exception Fromto;
fun fromto n m =
  if n>m+1 then raise Fromto
  else if n=m+1 then []
  else n::fromto (n+1) m;


fun MP n11 n12 n13 n22 n23 n24=
 let
  val alist =
       map (fn m => a(n11,n12,n13,n22,n23,n24,m))
           (fromto (RR n11 n12 n13 n22 n23 n24) 
                   (M n11 n12 n13 n22 n23 n24))
 in
  (map (fn x => (print (Int.toString x); print " ")) alist;
  sum (RR n11 n12 n13 n22 n23 n24) (M n11 n12 n13 n22 n23 n24) 
      (fn m => a(n11,n12,n13,n22,n23,n24,m)))
 end;


(* Ende *) 

