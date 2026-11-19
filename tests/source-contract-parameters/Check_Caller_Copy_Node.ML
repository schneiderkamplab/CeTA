(* Local successor checks; no complete observer-family or Split acceptance. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-caller-copy-node/Caller_Copy_Node_Check.ML";
structure W = Caller_Copy_Node_Check;
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
 val (c,k,l,yes)=case action of
  W.LPPFCut(W.LPCRResolution(_,_,W.Nat c,_,_,_,k,l,_,_,_,_,_,_,yes,_),_,_)=>(IntInf.toInt c,k,l,yes)
  | _=>raise Fail "expected resolution action"
 val (head,body)=List.nth(p,c)
 val head_args=case head of W.Fun(_,xs)=>xs | _=>raise Fail "expected head"
 val bindings=W.lpcl_bindings yes
 val j=integer(W.lpcl_target yes)
 val (goals,payload)=case List.nth(states,j) of (W.LPCGoals gs,ps)::_=>(gs,ps) | _=>raise Fail "successor"
 val target_parameter=if kind="recursive" then List.nth(call_args goals,1) else List.nth(payload,1)
 val target_output=if kind="recursive" then List.nth(call_args goals,2) else List.nth(payload,2)
 val label=region ^ ":" ^ Int.toString row ^ "->" ^ Int.toString j
 fun coord source target bs = W.test_clause_coordinate l source target bs
 val parameter=List.nth(head_args,1)
 val pv=variable target_parameter
 val source_ok=W.lpp_check_functor_source_action (fn _=>[]) (nat 10000) p q nds states contexts frees functors
  (List.nth(nds,row)) (List.nth(frees,row)) (List.nth(states,row))
  (List.nth(contexts,row)) (List.nth(functors,row)) out arity action
 val _=require ("SOURCE_ROW " ^ label) source_ok
 val _=require ("PARAMETER_CLAUSE_COORDINATE " ^ label) (coord parameter target_parameter bindings)
 val _=require ("REJECT_WRONG_CLAUSE_PREFIX " ^ label)
  (not(W.test_clause_coordinate (nat(integer l+1)) parameter target_parameter bindings))
 val _=require ("REJECT_ACTIVE_PREFIX_AS_CLAUSE " ^ label)
  (not(W.test_clause_coordinate k parameter target_parameter bindings))
 val _=require ("REJECT_MISSING_PARAMETER_BINDING " ^ label)
  (not(coord parameter target_parameter (List.filter(fn(v,_)=>v<>pv)bindings)))
 val _=require ("REJECT_STALE_PARAMETER_COORDINATE " ^ label)
  (not(coord parameter target_parameter (List.map(fn(v,t)=>if v=pv then (v,parameter) else (v,t))bindings)))
 val (pred,nil_symbol,n)=case head of W.Fun(pred,[W.Fun(nil_symbol,[]),W.Var n,W.Var m])=>
   if n=m then (pred,nil_symbol,n) else raise Fail "not repeated"
   | _=>raise Fail "not copy head"
 val _=require ("COPY_HEAD " ^ label) (W.test_copy_head head)
 val _=require ("REJECT_NONREPEATED_PARAMETER " ^ label)
  (not(W.test_copy_head(W.Fun(pred,[W.Fun(nil_symbol,[]),W.Var n,W.Var(n @ input "_changed")]))))
 val _=require ("REJECT_NONEMPTY_FIRST_HEAD_ARGUMENT " ^ label)
  (not(W.test_copy_head(W.Fun(pred,[W.Fun(nil_symbol,[W.Var n]),W.Var n,W.Var n]))))
 val _=require ("COPIED_OUTPUT_COORDINATE " ^ label) (coord (List.nth(head_args,2)) target_output bindings)
 val _=require ("REJECT_MISSING_OUTPUT_BINDING " ^ label)
  (not(coord (List.nth(head_args,2)) target_output (List.filter(fn(v,_)=>v<>variable target_output)bindings)))
 in () end;
val _=List.app check [("0",22,"copy"),("35",2,"copy")];
val _=require "CALLER_SLOT_COVERAGE" (W.test_leaf_slots [nat 0] [W.LPCAtom(W.Var(nat 0))]);
val _=require "REJECT_UNCOVERED_CALLER_SLOT" (not(W.test_leaf_slots [nat 0] [W.LPCAtom(W.Var(nat 1))]));
val _=print "CALLER_COPY_NODE_FIXTURES_PASSED_FULL_FAMILY_OPEN\n";
