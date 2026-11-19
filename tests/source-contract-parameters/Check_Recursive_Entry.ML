(* Local successor checks; no complete observer-family or Split acceptance. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-recursive-entry/Recursive_Entry_Check.ML";
structure W = Recursive_Entry_Check;
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
fun check (region,row,kind) = let
 val (nds,(states,(contexts,(frees,(functors,(_, (out,arity))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val (p,q)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 val action=valOf(List.nth(actions,row))
 val (call,c,k,l,yes)=case action of
  W.LPPFCut(W.LPCRResolution(call,_,W.Nat c,_,_,_,k,l,_,_,_,_,_,_,yes,_),_,_)=>(call,IntInf.toInt c,k,l,yes)
  | _=>raise Fail "expected resolution action"
 val (head,body)=List.nth(p,c)
 val head_args=case head of W.Fun(_,xs)=>xs | _=>raise Fail "expected head"
 val bindings=W.lpcl_bindings yes
 val j=integer(W.lpcl_target yes)
 val (goals,payload)=case List.nth(states,j) of (W.LPCGoals gs,ps)::_=>(gs,ps) | _=>raise Fail "successor"
 val target_parameter=if kind="recursive" then List.nth(call_args goals,1) else List.nth(payload,1)
 val target_output=if kind="recursive" then List.nth(call_args goals,2) else List.nth(payload,2)
 val label=region ^ ":" ^ Int.toString row ^ "->" ^ Int.toString j
 val parameter=List.nth(head_args,1)
 val pv=variable target_parameter
 val source_ok=W.lpp_check_functor_source_action (fn _=>[]) (nat 10000) p q nds states contexts frees functors
  (List.nth(nds,row)) (List.nth(frees,row)) (List.nth(states,row))
  (List.nth(contexts,row)) (List.nth(functors,row)) out arity action
 val (x,y,n,m)=case head of W.Fun(_,[W.Fun(_,[W.Var x,W.Var y]),W.Var n,W.Var m])=>(x,y,n,m)
  | _=>raise Fail "cons head"
 val helper_call=call_args goals
 val tail_call=call_args(tl goals)
 val input_slot=variable(List.nth(helper_call,0))
 val helper_slot=variable target_output
 val tail_slot=variable(List.nth(tail_call,0))
 val caller_slot=variable(List.nth(tail_call,2))
 val fresh_variable=variable(List.nth(call_args body,2))
 fun run bs prefix hs cs maps = W.test_entry_coordinates head bs prefix x y n m fresh_variable
  input_slot pv hs tail_slot cs maps
 val _=require ("SOURCE_ROW " ^ label) source_ok
 val _=require ("SOURCE_CALL_SHAPE " ^ label)
  (case (call,head) of (W.Fun(p,[_,W.Var _,W.Var _]),W.Fun(q,_))=>p=q | _=>false)
 val _=require ("RECURSIVE_ENTRY_MAPS " ^ label) (run body l helper_slot caller_slot bindings)
 val _=require ("CALLER_RETURN_ROLE " ^ label) (List.nth(tail_call,2)=List.nth(payload,2))
 val _=List.app (fn slot=>require ("REJECT_MISSING_" ^ output slot ^ " " ^ label)
  (not(run body l helper_slot caller_slot (List.filter(fn(v,_)=>v<>slot)bindings))))
  [input_slot,pv,helper_slot,tail_slot,caller_slot]
 val _=require ("REJECT_ALIASED_OUTPUT_SLOTS " ^ label) (not(run body l helper_slot helper_slot bindings))
 val _=require ("REJECT_SWAPPED_OUTPUT_ROLES " ^ label) (not(run body l caller_slot helper_slot bindings))
 val _=require ("REJECT_MISSING_BODY_OCCURRENCE " ^ label) (not(run [] l helper_slot caller_slot bindings))
 val _=require ("REJECT_WRONG_PREFIX " ^ label) (not(run body (nat(integer l+1)) helper_slot caller_slot bindings))
 val unused=input "__unused_entry_evidence"
 val augmented=(unused,W.Var unused)::bindings
 val _=require ("UNUSED_EVIDENCE_REMOVAL " ^ label)
  (run body l helper_slot caller_slot augmented andalso
   run body l helper_slot caller_slot (List.filter(fn(v,_)=>v<>unused)augmented))
 in () end;
val _=List.app check [("0",23,"recursive"),("35",3,"recursive")];
val _=print "RECURSIVE_ENTRY_FIXTURES_PASSED_FULL_FAMILY_OPEN\n";
