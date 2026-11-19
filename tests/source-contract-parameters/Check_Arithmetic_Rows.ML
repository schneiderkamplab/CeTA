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
 val row=15
 val (nds,(states,(contexts,(frees,(functors,(_, (out,arity))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val (p,q)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 val action=valOf(List.nth(actions,row))
 val (result,middle,facts)=case action of W.LPPFIs triple=>triple | _=>raise Fail "arithmetic"
 val j=integer(W.lpcl_target middle)
 val (a,e,payload)=case List.nth(states,row) of
  (W.LPCGoals(W.LPCAtom(W.Fun(_,[a,e]))::_),ps)::_=>(a,e,ps)
  | _=>raise Fail "source shape"
 val (output_slot,scalar_slot,target_payload)=case List.nth(states,j) of
  [(W.LPCGoals[W.LPCUnify(W.Var a,W.Var b)],ps)] => (a,b,ps)
  | _=>raise Fail "target shape"
 val parameter_slot=variable(List.nth(target_payload,1))
 val parameter_term=List.nth(payload,1)
 val bindings=W.lpcl_bindings middle
 fun run act=W.lpp_check_functor_source_action (fn _=>[]) (nat 10000) p q nds states contexts frees functors
  (List.nth(nds,row)) (List.nth(frees,row)) (List.nth(states,row))
  (List.nth(contexts,row)) (List.nth(functors,row)) out arity act
 fun changed f = W.LPPFIs(result,map_bindings f middle,facts)
 fun replace slot term bs=(slot,term)::List.filter(fn(v,_)=>v<>slot)bs
 val v0=W.Var(input "V0")
 val v1=W.Var(input "V1")
 val v2=W.Var(input "V2")
 val marker=case payload of [W.Fun(f,[W.Fun(g,[]),n]),n2,out_term] =>
   if n=v1 andalso n2=v1 andalso out_term=v0 then (f,g) else raise Fail "source payload coordinates"
   | _=>raise Fail "source payload shape"
 val (marker_f,marker_g)=marker
 val _=require ("RETAINED_ARITHMETIC_BOUNDARY_SHAPE " ^ region)
   (j=19 andalso a=v0 andalso output_slot=input "V0" andalso scalar_slot=input "V1" andalso
    List.nth(states,row)=[(W.LPCGoals[W.LPCAtom(W.Fun(W.LPCUser(input "2:is"),[v0,e]))],payload)] andalso
    target_payload=[W.Fun(marker_f,[W.Fun(marker_g,[]),v2]),v2,v0])
 val label=region ^ ":15->" ^ Int.toString j
 val _=require ("CHECKED_ARITHMETIC_ROW " ^ label) (run action)
 val _=require ("OUTPUT_COORDINATE " ^ label) (a=W.Var output_slot)
 val _=require ("SCALAR_COORDINATE " ^ label) (List.exists(fn(v,t)=>v=scalar_slot andalso t=W.Var result)bindings)
 val _=require ("PARAMETER_PAYLOAD_COORDINATE " ^ label) (List.exists(fn(v,t)=>v=parameter_slot andalso t=parameter_term)bindings)
 val _=require ("REJECT_WRONG_SCALAR " ^ label) (not(run(changed(replace scalar_slot (W.Var(input "wrong"))))))
 val _=require ("REJECT_MISSING_SCALAR " ^ label) (not(run(changed(List.filter(fn(v,_)=>v<>scalar_slot)))))
 val _=require ("REJECT_PARAMETER_ALIAS " ^ label) (not(run(changed(replace parameter_slot (W.Var result)))))
 val _=require ("REJECT_NONFRESH_RESULT " ^ label) (not(run(W.LPPFIs(output_slot,middle,facts))))
 in () end;
val _=List.app check ["0","47"];
val _=print "ARITHMETIC_ROWS_CHECKED_DYNAMIC_CONDITIONS_OPEN\n";
