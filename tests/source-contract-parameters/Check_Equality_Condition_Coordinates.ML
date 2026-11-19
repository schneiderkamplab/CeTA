(* Local successor checks; no complete observer-family or Split acceptance. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-recursive-caller/Recursive_Caller_Check.ML";
structure W = Recursive_Caller_Check;
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
fun map_bindings f (W.Lpc_link_ext(j,vs,ts,ss,g,k,bs,sw,l,r,z)) =
 W.Lpc_link_ext(j,vs,ts,ss,g,k,f bs,sw,l,r,z);
fun check region = let
 val row=0
 val (nds,(states,(contexts,(frees,(functors,(_, (out,arity))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val (p,q)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 val action=valOf(List.nth(actions,row))
 val (a,b,gs,payload,saved,k,l,next,mode,outputs,yes,no,yf,nf)=case action of
  W.LPPFCut(W.LPCREquality(a,b,gs,ps,ss,k,l,n,m,os,y,no),yf,nf)=>(a,b,gs,ps,ss,k,l,n,m,os,y,no,yf,nf)
  | _=>raise Fail "equality"
 fun rebuild y n = W.LPPFCut(W.LPCREquality(a,b,gs,payload,saved,k,l,next,mode,outputs,y,n),yf,nf)
 fun run act=W.lpp_check_functor_source_action (fn _=>[]) (nat 10000) p q nds states contexts frees functors
  (List.nth(nds,row)) (List.nth(frees,row)) (List.nth(states,row))
  (List.nth(contexts,row)) (List.nth(functors,row)) out arity act
 val j=integer(W.lpcl_target yes)
 val target=case List.nth(states,j) of [(W.LPCGoals [],ps)]=>ps | _=>raise Fail "success shape"
 val slot=variable(hd target)
 val bs=W.lpcl_bindings yes
 fun replace term maps=(slot,term)::List.filter(fn(v,_)=>v<>slot)maps
 val _=require "RETAINED_EQUALITY_COORDINATES" (a=W.Var(input "V0") andalso b=W.Var(input "V1") andalso payload=[a,b] andalso null gs andalso null saved)
 val _=require "RETAINED_REFRESH_PREFIXES" (integer k=3 andalso integer l=6)
 val _=require "RETAINED_SUCCESS_INITIALIZATION" (j=1 andalso bs=[(input "V0",W.Var(input "V1"))])
 val _=require "RETAINED_FAILURE_INITIALIZATION" (integer(W.lpcl_target no)=2)
 val _=require "RETAINED_GROUND_TABLE" (W.lpcn_ground(List.nth(nds,row))=[input "V1"])
 val _=require "CHECKED_EQUALITY_ROW" (run action)
 val _=require "RETURN_PARAMETER_COORDINATE" (List.exists(fn(v,t)=>v=slot andalso t=b)bs)
 val _=require "RETURN_OUTPUT_COORDINATE" (length target=2 andalso hd target=List.nth(target,1))
 val _=require "NO_FREE_OUTPUT_PREMISE" (null(List.nth(frees,row)))
 val _=require "REJECT_WRONG_RETURN_BINDING" (not(run(rebuild(map_bindings (replace(W.Var(input "wrong"))) yes) no)))
 val _=require "REJECT_MISSING_RETURN_BINDING" (not(run(rebuild(map_bindings(List.filter(fn(v,_)=>v<>slot))yes)no)))
 val _=require "REJECT_SWAPPED_SUCCESS_FAILURE" (not(run(rebuild no yes)))
 in () end;
val _=check "19";
val _=print "EQUALITY_CONDITION_COORDINATES_CHECKED_FAMILY_OPEN\n";
