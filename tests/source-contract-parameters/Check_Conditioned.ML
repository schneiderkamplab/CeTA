(* Local equality rows only; this does not authenticate either Split return. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-conditioned-equality/Conditioned_Check.ML";
structure W = Conditioned_Check;
fun read_file path = let val s=TextIO.openIn path val text=TextIO.inputAll s
 in TextIO.closeIn s; text end;
fun input s = map (fn c => W.Chr(IntInf.fromInt(Char.ord c))) (String.explode s);
fun output cs = String.implode(map(fn W.Chr n => Char.chr(IntInf.toInt n)) cs);
fun nat n = W.Nat(IntInf.fromInt n);
val directory = valOf(OS.Process.getEnv "OBSERVER_XML_DIRECTORY");
fun decode parser name = case parser(input(read_file(directory ^ "/" ^ name))) of
 W.Sumbot(W.Inr x)=>x | W.Sumbot(W.Inl e)=>raise Fail(name ^ ": " ^ output e);
fun require name b = if b then print(name ^ " PASS\n") else raise Fail name;
fun check region = let
 val (nds,(states,(contexts,(frees,(functors,(_, (out,arity))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val (p,q)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 val row=12
 val action=valOf(List.nth(actions,row))
 val (a,b,k,l,yes,no)=case action of
  W.LPPFCut(W.LPCREquality(a,b,_,_,_,k,l,_,_,_,yes,no),_,_)=>(a,b,k,l,yes,no)
  | _=>raise Fail "expected equality action"
 val parameter=case b of W.Fun(_,[W.Fun(_,[]),W.Var v])=>v
  | _=>raise Fail "expected restricted parameter replacement"
 val ground=W.lpcn_ground(List.nth(nds,row))
 val bindings=W.lpcl_bindings yes
 val target=case List.nth(states,15) of
  (W.LPCGoals(W.LPCAtom(W.Fun(_,[_,W.Fun(_,[v,_])]))::_),_)::_=>v
  | _=>raise Fail "expected arithmetic successor"
 val target_parameter=case target of W.Var v=>v | _=>raise Fail "expected target parameter variable"
 val before_parameter=W.Var parameter
 val label=region ^ ":12->15"
 fun refresh gs ks ls bs = W.test_parameter_refresh ks ls gs before_parameter target bs
 fun source_check ss cs = W.lpp_check_functor_source_action (fn _=>[]) (nat 10000) p q nds ss cs frees functors
  (List.nth(nds,row)) (List.nth(frees,row)) (List.nth(states,row))
  (List.nth(contexts,row)) (List.nth(functors,row)) out arity action
 val mapped=valOf(List.find(fn (v,_)=>v=target_parameter) bindings)
 val wrong=List.map(fn(v,t)=>if v=target_parameter then (v,a) else (v,t))bindings
 val changed_ground=if null ground then [parameter] else []
 in
 require ("SOURCE_EQUALITY_ROW " ^ label) (source_check states contexts);
 require ("REJECT_MISSING_SUCCESSOR_STATE " ^ label) (not(source_check (List.take(states,15)) contexts));
 require ("REJECT_MISSING_SUCCESSOR_CONTEXT " ^ label) (not(source_check states (List.take(contexts,15))));
 require ("SUCCESS_TARGET " ^ label) (W.lpcl_target yes=nat 15);
 require ("FAILURE_TARGET " ^ label) (W.lpcl_target no=nat 16);
 require ("PARAMETER_REFRESH " ^ label) (refresh ground k l bindings);
 require ("REJECT_WRONG_REFRESH_COORDINATE " ^ label) (not(refresh ground k l wrong));
 require ("REJECT_CHANGED_RAW_GROUND " ^ label) (not(refresh changed_ground k l bindings));
 require ("REJECT_OVERLAPPING_REFRESH_BOUNDS " ^ label) (not(refresh ground k (nat 5) bindings));
 require ("REJECT_SHORT_PREFIX " ^ label) (not(refresh ground (nat 2) l bindings));
 if null ground then require ("REJECT_MISSING_PARAMETER_MAP " ^ label)
  (not(refresh ground k l (List.filter(fn(v,_)=>v<>target_parameter)bindings)))
 else require ("REMOVE_REDUNDANT_IDENTITY_MAP " ^ label)
  (#2 mapped=target andalso refresh ground k l (List.filter(fn(v,_)=>v<>target_parameter)bindings));
 require ("EMPTY_FAILURE_SUCCESSOR " ^ label) (null(List.nth(states,16)))
 end;
val _=List.app check ["0","47"];
val _=print "CONDITIONED_EQUALITY_FIXTURES_PASSED_SPLIT_CONTRACTS_OPEN\n";
