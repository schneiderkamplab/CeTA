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
fun replace xs i x = ListPair.map (fn (j,y)=>if i=j then x else y)
 (List.tabulate(length xs,fn j=>j),xs);
fun check region = let
 val (nds,(states,(contexts,(frees,(functors,(_, (out,arity))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val (p,q)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 val action=valOf(List.nth(actions,3))
 val link=case action of W.LPPFCut(W.LPCRResolution(_,_,_,_,_,_,_,_,_,_,_,_,_,_,yes,_),_,_)=>yes
 | _=>raise Fail "resolution"
 val target=integer(W.lpcl_target link)
 val (goals,payload,saved)=case List.nth(states,target) of
 (W.LPCGoals gs,ps)::ss=>(gs,ps,ss) | _=>raise Fail "target"
 fun checked states = W.lpp_check_functor_source_action (fn _=>[]) (nat 10000)
 p q nds states contexts frees functors (List.nth(nds,3)) (List.nth(frees,3))
 (List.nth(states,3)) (List.nth(contexts,3)) (List.nth(functors,3)) out arity action
 fun target_state gs ps ss=replace states target ((W.LPCGoals gs,ps)::ss)
 val _=require (region ^ " ACQUISITION_LINK") (checked states)
 val _=require (region ^ " REJECT_MISSING_PENDING") (not(checked(target_state [hd goals] payload saved)))
 val _=require (region ^ " REJECT_MISSING_PAYLOAD") (not(checked(target_state goals [] saved)))
 val _=require (region ^ " REJECT_REVERSED_PAYLOAD") (not(checked(target_state goals (rev payload) saved)))
 val _=require (region ^ " REJECT_FORGED_SAVED")
 (not(checked(target_state goals payload ((W.LPCGoals [],payload)::saved))))
 in () end;
val _=List.app check ["0","47"];
val _=print "ACQUIRED_UNIV_LINK_CONTROLS_PASSED_RESOLUTION_ASSEMBLY_OPEN\n";
