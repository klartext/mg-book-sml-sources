(* Parallele Kombinatormaschine + Implementierung der PR*)

fun last l = hd(rev l);
fun remove x [] = []
   |remove x (hd::tl) =
	if x = hd then remove x tl
        else hd::(remove x tl);

(* ****************** *)
datatype Emark = Eval|Busy|Ready;

datatype node = atom of (value * Emark ref * (node ref list) ref)
               |comb of (comb  * Emark ref * (node ref list) ref)
               |app of  ((node ref * node ref) * Emark ref * 
                                             (node ref list) ref);

fun alloc snode =
 let
   fun allocate (satom(x)) = atom(x,ref Ready, ref [])
      |allocate (scomb(com)) = comb(com,ref Ready, ref [])
      |allocate (sapp(a,b)) = app((ref (allocate a),ref (allocate b)),
                                  ref Eval, ref [])
 in
   ref(allocate snode)
 end;

fun dealloc (ref (atom(x,_,_))) = satom(x)
   |dealloc (ref (comb(k,_,_))) = scomb(k)
   |dealloc (ref (app((a,b),_,_))) = sapp(dealloc a,dealloc b);



fun is_atom (atom(_)) = true
   |is_atom (comb(_)) = false
   |is_atom (app(_))  = false;

fun is_app (atom(_)) = false
   |is_app (comb(_)) = false
   |is_app (app(_))  = true;

fun copy (ref(atom(x,ref Emark,ref wq))) = 
        ref(atom(x,ref Emark,ref wq))
   |copy (ref(comb(x,ref Emark,ref wq))) = 
        ref(comb(x,ref Emark,ref wq))
   |copy (ref(app((rator,rand),ref Emark,ref wq))) =
        ref(app((copy rator,copy rand),ref Emark,ref wq));

fun equal (ref(atom(x,_,_))) (ref(atom(y,_,_))) = (x=y)
   |equal (ref(comb(x,_,_))) (ref(comb(y,_,_))) = (x=y)
   |equal (ref(app((xrator,xrand),_,_))) 
          (ref(app((yrator,yrand),_,_))) =
        (equal xrator yrator) andalso (equal xrand yrand)
   |equal _ _ = false;


fun get_mark (ref(atom(_,m,_))) = m
   |get_mark (ref(comb(_,m,_))) = m
   |get_mark (ref( app(_,m,_))) = m; 

fun get_q (ref(atom(_,_,q))) = q
   |get_q (ref(comb(_,_,q))) = q
   |get_q (ref( app(_,_,q))) = q; 

fun set_q (ref(atom(_,_,q))) x = q:=x
   |set_q (ref(comb(_,_,q))) x = q:=x
   |set_q (ref( app(_,_,q))) x = q:=x; 

val ENV = ref [] : (string * node ref) list ref;
fun define name value = 
	ENV := (name, alloc(ropt(c(read value))))::(!ENV);


exception Lookup;
fun lookup name =
let
 fun lookup1 name [] = raise Lookup
    |lookup1 name ((x,y)::rest) = if name=x then y 
                                else (lookup1 name rest)
in
 lookup1 name (!ENV)
end;

fun spine (ref(atom(a,m,q))) stack = (atom(a,m,q),stack)
   |spine (ref(comb(c,m,q))) stack = (comb(c,m,q),stack)
   |spine (node as (ref(app((l,r),_,_)))) stack = spine l (node::stack);

val Tasks = ref [] : node ref list ref;
val Taskcounter = ref 0;

fun newTask task = 
   (Taskcounter := 1+(!Taskcounter);
    Tasks := (task::(! Tasks)));

fun remTask task =
   Tasks := (remove task (! Tasks));

fun make_wait node =
 let
  val (k,(w::_)) = spine node [];
  val ref(app((ref rator,rand),_,q)) = w;
 in
  w := app((ref(app((ref(comb(WAIT,ref Eval,ref [])),
                     ref rator),ref Eval,q)),
            rand),ref Eval,q)
 end;

  fun make_unwait node =
   let
    val (_,w::_) = spine node [];
    val ref(app((ref c,ref k),_,_)) = w;
    fun iswait (app(_,_,_)) = false
       |iswait (atom(_,_,_)) = false
       |iswait (comb(c,_,_)) = if (c=WAIT orelse c=WAIT1)
			       then true else false;
   in
    if iswait(c) 
      then w := k
      else () 
   end;

fun wakeup waitQ =
  (map (fn task => (make_unwait task))
       (! waitQ);
   waitQ := []);


fun subEval (root,node) =
 let 
  val emark = get_mark node;
  val wq = get_q node;
 in
  if (! emark = Ready) then ()
  else if (! emark = Busy) then
   (make_wait root;
    wq := root::(! wq))
  else
   (make_wait root;
    emark := Busy;
    wq := root::(!wq);
    newTask node)
  end;

fun parEval (root,node) =
 let 
  val emark = get_mark node;
  val wq = get_q node;
 in
  if (! emark = Ready) then ()
  else if (! emark = Busy) then
   (make_wait root;
    wq := root::(! wq))
  else
   (emark := Busy;
    newTask node)
  end;


fun apply (WAIT,(node as ref(app((_,x),m,q)))::_) =
        node := app((ref(comb(WAIT1,ref Ready,ref [])),
                     x),m,q)
   |apply (WAIT1,(node as ref(app((_,x),m,q)))::_) =
        node := app((ref(comb(WAIT,ref Ready,ref [])),
                     x),m,q)
   |apply (I,(node as ref(app((_,ref x),_,ref q)))::_) =
        (node := x; set_q node q)
   |apply (K,ref(app((_,ref x),_,ref q))::(node as ref(app(_,_,_)))::_) =
        (node := x; set_q node q)
   |apply (S,(ref(app((_,x),_,_)))::(ref(app((_,y),_,_)))
              ::(node as (ref(app((_,z),m,q))))::_) =
        node := app((ref(app((x,z),ref Eval,q)),
                     ref(app((y,z),ref Eval,q))),
                    ref Eval,q)
   |apply (B,(ref(app((_,x),_,_)))::(ref(app((_,y),_,_)))
              ::(node as (ref(app((_,z),m,q))))::_) =
	node := app((x,ref (app((y,z),ref Eval,q))),ref Eval,q)
   |apply (C,(ref(app((_,x),_,_)))::(ref(app((_,y),_,_)))
              ::(node as (ref(app((_,z),m,q))))::_) =
	node := app((ref(app((x,z),ref Eval,q)),y),ref Eval,q)

   |apply (Y,(node as ref(app((_,f),m,q)))::_) =
        node := app((f,node),ref Eval,q)
   |apply (DEF(name),(node as ref(app((_,_),_,_)))::_) =
        node := !(copy(lookup name))
   |apply (PLUS,ref(app((_,ref(atom(int x,_,_))),_,_))::(node as 
                ref(app((_,ref(atom(int y,_,_))),_,q)))::_) =
        node := atom(int(x+y),ref Ready,q)
   |apply (PLUS,(stack as ref(app((_,x),_,_))::
                          ref(app((_,y),_,_))::_)) =
        (subEval (last stack,x);
         subEval (last stack,y); ())
   |apply (MINUS,ref(app((_,ref(atom(int x,_,_))),_,_))::(node as 
                 ref(app((_,ref(atom(int y,_,_))),_,q)))::_) =
        node := atom(int(x-y),ref Ready,q)
   |apply (MINUS,(stack as ref(app((_,x),_,_))::
                          ref(app((_,y),_,_))::_)) =
        (subEval (last stack,x);
         subEval (last stack,y); ())
   |apply (TIMES,ref(app((_,ref(atom(int x,_,_))),_,_))::(node as 
                 ref(app((_,ref(atom(int y,_,_))),_,q)))::_) =
        node := atom(int(x*y),ref Ready,q)
   |apply (TIMES,(stack as ref(app((_,x),_,_))::
                          ref(app((_,y),_,_))::_)) =
        (subEval (last stack,x);
         subEval (last stack,y); ())
   |apply (DIV,ref(app((_,ref(atom(int x,_,_))),_,_))::(node as 
               ref(app((_,ref(atom(int y,_,_))),_,q)))::_) =
        node := atom(int(x div y),ref Ready,q)
   |apply (DIV,(stack as ref(app((_,x),_,_))::
                          ref(app((_,y),_,_))::_)) =
        (subEval (last stack,x);
         subEval (last stack,y); ())
   |apply (EQ,(stack as ref(app((_,x),_,_))::(node as
                          ref(app((_,y),_,q)))::_)) =
        if (!(get_mark x)) = Ready andalso
           (!(get_mark y)) = Ready 
          then node := atom(bool(equal x y),ref Ready,q)
        else
          (subEval (last stack,x);
          subEval (last stack,y); ())
   |apply (IF,(ref(app((_,ref(atom(bool test,_,_))),_,_))):: 
              (ref(app((_,x),_,_)))::(node as (ref(app((_,y),_,_))))::_) =
        if test then node := !x
        else node := !y
   |apply (IF,(stack as (ref(app((_,test),_,_)):: 
              ref(app((_,x),_,_))::(node as ref(app((_,y),_,q)))::_))) =
        subEval (last stack,test)
   |apply (CONS,_) = ()
   |apply (COPY,(node as ref(app((_,x),_,_)))::_) =
        node := !(copy x)
   |apply (PR, (stack as ( ref(app((_,f),_,_))::
                           ref(app((_,g),_,_))::
                           ref(app((_,xf),_,_))::(node as
                          (ref(app((_,xg),_,q))))::_))) =
        let
         val first =  ref(app((f,xf),ref Eval,ref []));
         val second = ref(app((g,xg),ref Eval,ref []));
        in
         (node := app((ref(app((ref(comb(CONS,ref Ready,ref [])),
                                first),ref Ready,ref [])),
                       second),ref Ready,q);
          parEval (last stack, first);
          parEval (last stack, second))
 	end
   |apply _ = ();


fun step node =
   let
    val (c,stack) = (spine node []);
   in
    if is_atom c then ()
    else let val comb(k,_,_)= c 
         in apply (k,stack) 
         end
   end;

fun evalstep (node as ref(atom(_,Emark,WQ))) = 
		(wakeup WQ;
		 remTask node;
		 Emark := Ready)
   |evalstep (node as ref(comb(_,Emark,WQ))) = 
		(wakeup WQ;
		 remTask node;
		 Emark := Ready)
   |evalstep (node as ref(app((ref rator,ref rand),Emark,WQ))) =
     let
      val old = copy node
     in
      (step node;
       if ((equal old node) orelse
           (!Emark = Ready) orelse
           (not (is_app (!node)))) (* Evaluation beendet ? *)
        then (wakeup WQ;           (* Wartende Prozesse reaktivieren *)
              remTask node;        (* Prozess entfernen *)
              Emark := Ready)      (* Knoten ist vollst"ndig evaluiert *)
        else ())                   (* der Scheduler kann die Evaluation 
                                      fortsetzen *)
     end;

val Seed = ref 4.34793435219781;
val Steps = ref 0;

fun Scheduler () =
 let
  fun rnd () =
   let
    val x = (! Seed)* 1475.37697;
    val res = x-real(floor x);
   in
    (Seed := res; res)
   end;
  fun intrand n = floor(rnd()*(real n));
 in
  if length(!Tasks) = 0 then ()
  else 
     (evalstep (nth(!Tasks,intrand (length (!Tasks))));
      Steps := 1+(!Steps);
      Scheduler())
 end;


fun eval node =
 (Steps := 0; Taskcounter := 0;
  Tasks := [];
  newTask node;
  Scheduler() handle _ => ();
  (show(dealloc node),!Steps,!Taskcounter));

fun run str = eval(alloc(c(read str)));

fun s () =
 let
  fun rnd () =
   let
    val x = (! Seed)* 1475.37697;
    val res = x-real(floor x);
   in
    (Seed := res; res)
   end;
  fun intrand n = floor(rnd()*(real n));
 in
  if length(!Tasks) = 0 then ""
  else 
     (evalstep (nth(!Tasks,intrand (length (!Tasks))));
      show(dealloc (last (!Tasks))))
 end;

fun rs str=
  (Tasks := [];
   newTask(alloc(ropt(c(read str))));
   s());
