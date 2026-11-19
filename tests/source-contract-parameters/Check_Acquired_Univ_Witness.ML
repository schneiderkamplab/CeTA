(* Local successor checks; no complete observer-family or Split acceptance. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-acquired-univ-caller/Acquired_Univ_Caller_Check.ML";
structure W = Acquired_Univ_Caller_Check;
fun read_file path = let val s=TextIO.openIn path val text=TextIO.inputAll s
 in TextIO.closeIn s; text end;
fun input s = map (fn c => W.Chr(IntInf.fromInt(Char.ord c))) (String.explode s);
fun output cs = String.implode(map(fn W.Chr n => Char.chr(IntInf.toInt n)) cs);
fun nat n = W.Nat(IntInf.fromInt n);
fun integer (W.Nat n) = IntInf.toInt n;
val directory = valOf(OS.Process.getEnv "OBSERVER_XML_DIRECTORY");
fun decode parser name = case parser(input(read_file(directory ^ "/" ^ name))) of
 W.Sumbot(W.Inr x)=>x | W.Sumbot(W.Inl e)=>raise Fail(name ^ ": " ^ output e);
fun require name b = if b then print(name ^ " PASS\n") else raise Fail name;
fun variable (W.Var v) = v | variable _ = raise Fail "expected variable";
fun call_args (W.LPCAtom(W.Fun(_,xs))::_)=xs | call_args _=raise Fail "expected call";
fun check region = let
 val (_, (states,(_, (frees,(_,(_,(_, _))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val (p,_)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 val (c,l,yes)=case valOf(List.nth(actions,3)) of
 W.LPPFCut(W.LPCRResolution(_,_,c,_,_,_,_,l,_,_,_,_,_,_,yes,_),_,_)=>(integer c,l,yes)
 | _=>raise Fail "resolution"
 val (_,body)=List.nth(p,c)
 val (x,y,z)=case hd body of W.LPCAtom(W.Fun(_,[x,W.Fun(_,[y,z])]))=>(x,y,z)
 | _=>raise Fail "source univ"
 val target=integer(W.lpcl_target yes)
 val (tx,ty,tz)=case List.nth(states,target) of
 (W.LPCGoals(W.LPCAtom(W.Fun(_,[x,W.Fun(_,[y,z])]))::_),_)::_=>(x,y,z)
 | _=>raise Fail "target univ"
 val bindings=W.lpcl_bindings yes
 fun coordinate (label,a,b) = (
 require (region ^ " " ^ label) (W.test_clause_coordinate l a b bindings);
 require (region ^ " REJECT_MISSING_" ^ label)
 (not(W.test_clause_coordinate l a b (List.filter(fn(v,_)=>v<>variable b)bindings))))
 val _=List.app coordinate [("INPUT",x,tx),("NAME",y,ty),("ARGS",z,tz)]
 val _=require (region ^ " FREE_COVERAGE")
  (List.all(fn v=>v=variable ty orelse v=variable tz)(List.nth(frees,target)))
 val _=require (region ^ " DISTINCT_OUTPUT_COORDINATES") (ty<>tz)
 in () end;
val _=List.app check ["0","47"];
val _=print "ACQUIRED_UNIV_WITNESS_COORDINATES_PASSED_COMPOSITION_OPEN\n";
