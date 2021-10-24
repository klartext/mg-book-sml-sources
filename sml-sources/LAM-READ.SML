use "ParsePrint.ML"; 


(*** Lambda-terms ***)

signature LAMBDA =
  sig
  datatype term = Free  of string
              | Bound of string
              | Int of int
              | Op of string
              | Abs   of string*term
              | Apply of term*term
  val abstract: string -> term -> term
  val inst: (string * term) list -> term -> term
  end;
  

functor LambdaFUN(Basic: BASIC) : LAMBDA =
  struct
  local open Basic in
  datatype term = Free  of string
		| Bound of string
		| Int of int
		| Op of string
		| Abs   of string*term
		| Apply of term*term;

  (*Convert occurrences of b to bound index i in a term*)
  fun abstract  b (Free a) = if a=b then  Bound(a)  else  Free a
    | abstract  b (Bound j) = Bound j
    | abstract  b (Abs(a,t)) = Abs(a, abstract b t)
    | abstract  b (Apply(t,u)) = Apply(abstract b t, abstract b u);

  
 
  (*Substitution for free variables*)
    fun member x [] = false
       |member x (y::ys) = (x=y) orelse (member x ys);

  fun isop x = member x ["I","K","S","B","C","Y","CONS","HD","TL","+",
                         "ADD","MUL","SUB","DIV",
			"IF","EQ","AND","OR","NOT","PR","PAR","SET"];
  
  fun isnum str =
   let
    fun forall [] p = true
       |forall (x::xs) p = (p x) andalso (forall xs p);

   in
    forall (explode str)
           (fn ch => member ch ["0","1","2","3","4","5","6","7","8","9"])
	   
   end;

  fun mkint "" num = num
     |mkint str num =
       let val dig =hd(explode str);
	    val rest=implode(tl(explode str));
       in
	mkint rest (10*num + (if dig="0" then 0
			      else if dig="1" then 1
			      else if dig="2" then 2
			      else if dig="3" then 3
			      else if dig="4" then 4
			      else if dig="5" then 5
			      else if dig="6" then 6
			      else if dig="7" then 7
			      else if dig="8" then 8
			      else 9))
	end;

  fun inst env (Free a) = if (isnum a) then Int(mkint a 0)
			  else if (isop a) then Op(a)
			  else (inst env (lookup(env,a)) 
		                 handle Lookup => Free a)
    | inst env (Bound i) = Bound i
    | inst env (Abs(a,t)) = Abs(a, inst env t)
    | inst env (Apply(t1,t2)) = Apply(inst env t1, inst env t2);
  end
  end;


(*** Parsing of lambda terms ***)
signature PARSELAM = 
  sig
  type term
  val abslist: string list * term -> term
  val applylist: term * term list -> term
  val read: string -> term
  end;

functor ParseLamFUN (structure Parse: PARSE 
		     and       Lambda: LAMBDA) : PARSELAM =
  struct
  local open Parse  open Lambda  in
  type term = term;

  (*Abstraction over several free variables*)
  fun abslist([],    t) = t
    | abslist(b::bs, t) = Abs(b, abstract  b (abslist(bs, t)));

  (*Application of t to several terms*)
  fun applylist(t, []) = t
    | applylist(t, u::us) = applylist(Apply(t,u), us);

  fun makelambda ((((_,b),bs),_),t) = abslist(b::bs,t)

  (*term/atom distinction prevents left recursion; grammar is ambiguous*)
  fun term toks =
   (   $"%" -- id -- repeat id -- $"." -- term	>> makelambda
     || atom -- repeat atom			>> applylist
    ) toks
  and atom toks =
    (   id					>> Free
     || $"(" -- term -- $")"			>> (#2 o #1)
    ) toks;
  val read = reader term;
  end
  end;






(******** SHORT DEMONSTRATIONS ********)

structure Basic = BasicFUN();
structure LamKey = 
    struct val alphas = []
           and symbols = ["(", ")", "'", "->"]
    end;
structure LamLex = LexicalFUN (structure Basic=Basic and Keyword=LamKey);
structure Parse = ParseFUN(LamLex);


structure Lambda = LambdaFUN(Basic);
structure ParseLam = ParseLamFUN (structure Parse=Parse and Lambda=Lambda);

open Basic;  open Lambda; 


val stdenv = map  (fn (a,b) => (a, ParseLam.read b))
[    (*booleans*)
 ("true", "%x y.x"),           ("false",  "%x y.y"), 
 ("if", "%p x y. p x y"),
     (*ordered pairs*)
 ("pair", "%x y f.f x y"),  
 ("fst", "%p.p true"),         ("snd", "%p.p false"),
     (*natural numbers*)
 ("suc", "%n f x. n f (f x)"),
 ("iszero", "%n. n (%x.false) true"),
 ("0", "%f x. x"),             ("1", "suc 0"),
 ("2", "suc 1"),               ("3", "suc 2"),
 ("4", "suc 3"),               ("5", "suc 4"),
 ("6", "suc 5"),               ("7", "suc 6"),
 ("8", "suc 7"),               ("9", "suc 8"),
 ("add",  "%m n f x. m f (n f x)"),
 ("mult", "%m n f. m (n f)"),
 ("expt", "%m n f x. n m f x"),
 ("prefn", "%f p. pair (f (fst p)) (fst p)"),
 ("pre",  "%n f x. snd (n (prefn f) (pair x x))"),
 ("sub",  "%m n. n pre m"),
      (*lists*)
 ("nil",  "%z.z"),
 ("cons", "%x y. pair false (pair x y)"),
 ("null", "fst"),
 ("hd", "%z. fst(snd z)"),     ("tl", "%z. snd(snd z)"),
     (*recursion for call-by-name*)
 ("YN", "%f. (%x.f(x x))(%x.f(x x))"),
 ("fact", "YN (%g n. if (iszero n) 1 (mult n (g (pre n))))"),
 ("append", "YN (%g z w. if (null z) w (cons (hd z) (g (tl z) w)))"),
 ("inflist", "YN (%z. cons MORE z)"),
     (*recursion for call-by-value*)
 ("YV", "%f. (%x.f(%y.x x y)) (%x.f(%y.x x y))"),
 ("factV", "YV (%g n. (if (iszero n) (%y.1) (%y.mult n (g (pre n))))y)") ];


fun read a = inst stdenv (ParseLam.read a);



