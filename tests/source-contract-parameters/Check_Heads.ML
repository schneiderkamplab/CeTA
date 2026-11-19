(* Fixture checks discharge syntax/coverage only; runtime premises stay explicit. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-parameter-heads/Head_Check.ML";
structure W = Head_Check;
fun read_file path = let val s=TextIO.openIn path val text=TextIO.inputAll s
 in TextIO.closeIn s; text end;
fun input s = map (fn c => W.Chr(IntInf.fromInt(Char.ord c))) (String.explode s);
fun output cs = String.implode(map(fn W.Chr n => Char.chr(IntInf.toInt n)) cs);
fun nat n = W.Nat(IntInf.fromInt n);
val directory = valOf(OS.Process.getEnv "OBSERVER_XML_DIRECTORY");
fun decode parser name = case parser(input(read_file(directory ^ "/" ^ name))) of
 W.Sumbot(W.Inr x)=>x | W.Sumbot(W.Inl e)=>raise Fail(name ^ ": " ^ output e);
fun require name b = if b then print(name ^ " PASS\n") else raise Fail name;
fun check (region,row,copy) = let
 val (nds,(states,(contexts,(frees,(functors,(_, (out,arity))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val (p,q)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 val action=valOf(List.nth(actions,row))
 val (call,gs,c)=case action of
  W.LPPFCut(W.LPCRResolution(a,gs,W.Nat c,_,_,_,_,_,_,_,_,_,_,_,_,_),_,_)=>(a,gs,IntInf.toInt c)
  | _=>raise Fail "expected resolution action"
 val head= #1(List.nth(p,c))
 val label=region ^ ":" ^ Int.toString row
 fun source_check ss = W.lpp_check_functor_source_action (fn _=>[]) (nat 10000) p q nds ss contexts frees functors
  (List.nth(nds,row)) (List.nth(frees,row)) (List.nth(states,row))
  (List.nth(contexts,row)) (List.nth(functors,row)) out arity action
 val _=require ("SOURCE_HEAD_ROW " ^ label) (source_check states)
 val _=require ("REJECT_MISSING_SUCCESSOR_STATES " ^ label) (not(source_check []))
 in if copy then let
  val (pred,nil_symbol,n)=case head of W.Fun(pred,[W.Fun(nil_symbol,[]),W.Var n,W.Var m])=>
   if n=m then (pred,nil_symbol,n) else raise Fail "not a repeated parameter"
   | _=>raise Fail "not a copy head"
  in
  require ("COPY_HEAD " ^ label) (W.test_copy_head head);
  require ("REJECT_NONREPEATED_PARAMETER " ^ label)
   (not(W.test_copy_head(W.Fun(pred,[W.Fun(nil_symbol,[]),W.Var n,W.Var(n @ input "_changed")]))));
  require ("REJECT_NONEMPTY_FIRST_HEAD_ARGUMENT " ^ label)
   (not(W.test_copy_head(W.Fun(pred,[W.Fun(nil_symbol,[W.Var n]),W.Var n,W.Var n]))))
  end
 else let
  val (pred,args)=case call of W.Fun(f,args)=>(f,args) | _=>raise Fail "call"
  val heads=case head of W.Fun(_,hs)=>hs | _=>raise Fail "head"
  val bindings=ListPair.mapEq(fn(W.Var x,t)=>(x,t) | _=>raise Fail "variable head expected")(heads,args)
  val output_var=case List.nth(args,2) of W.Var x=>x | _=>raise Fail "output"
  fun run fs bs = W.test_matching_outputs fs call gs head bs
  val wrong=case bindings of (v,_)::tail=>(v,W.Fun(pred,[]))::tail | _=>raise Fail "bindings"
  in
  require ("MATCHING_OUTPUT_COVERAGE " ^ label) (run [output_var] bindings);
  require ("REJECT_WRONG_MATCH " ^ label) (not(run [output_var] wrong));
  require ("REJECT_MISSING_BINDING " ^ label) (not(run [output_var] (tl bindings)));
  require ("REJECT_UNCOVERED_OUTPUT " ^ label) (not(run [input "__uncovered_output"] bindings));
  require ("CONTINUATION_ONLY_OUTPUT_COVERAGE " ^ label)
   (W.test_matching_outputs [input "__uncovered_output"] call
    [W.LPCAtom(W.Var(input "__uncovered_output"))] head bindings)
  end
 end;
val _=List.app check [("0",2,false),("0",3,false),("47",2,false),("47",3,false),("0",22,true),("35",2,true)];
val _=print "PARAMETER_HEAD_FIXTURES_PASSED_FULL_FAMILY_OPEN\n";
