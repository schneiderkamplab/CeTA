(* Local successor checks; no complete observer-family or Split acceptance. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-cons-node/Cons_Node_Check.ML";
structure W = Cons_Node_Check;
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
 val (pred,x,y,hs)=case head of W.Fun(pred,W.Fun(_,[W.Var x,W.Var y])::tail)=>(pred,x,y,map variable tail)
  | _=>raise Fail "cons head"
 val arity=case call of W.Fun(_,ts)=>length ts-1 | _=>raise Fail "call"
 fun head_check h n u v ws = W.test_cons_head pred h (nat n) u v ws
 val _=require ("LINEAR_CONS_HEAD " ^ label) (head_check head arity x y hs)
 val _=require ("REJECT_REPEATED_HEAD_VARIABLE " ^ label)
  (not(head_check (case head of W.Fun(p,W.Fun(c,_)::tail)=>W.Fun(p,W.Fun(c,[W.Var x,W.Var x])::tail) | _=>head) arity x x hs))
 val _=require ("REJECT_WRONG_HEAD_ARITY " ^ label) (not(head_check head (arity+1) x y hs))
 val target_tail=List.nth(call_args(tl goals),0)
 val _=require ("TAIL_COORDINATE " ^ label) (coord (W.Var y) target_tail bindings)
 val _=require ("REJECT_TAIL_MAP_TO_HEAD_ELEMENT " ^ label)
  (not(coord (W.Var y) (List.nth(call_args goals,0)) bindings))
 in let
  val fresh=variable(List.nth(call_args body,2))
  val ov=variable target_output
  fun fresh_check bs x target maps = W.test_body_output head bs l x target maps
  in
  require ("FRESH_HELPER_OUTPUT " ^ label) (fresh_check body fresh target_output bindings);
  require ("REJECT_HEAD_PARAMETER_AS_FRESH " ^ label)
   (not(fresh_check body (variable parameter) target_parameter bindings));
  require ("REJECT_MISSING_BODY_OCCURRENCE " ^ label) (not(fresh_check [] fresh target_output bindings));
  require ("REJECT_OUTPUT_MAP_TO_PARAMETER " ^ label)
   (not(fresh_check body fresh target_output
    (List.map(fn(v,t)=>if v=ov then (v,#2(valOf(List.find(fn(w,_)=>w=pv)bindings))) else (v,t))bindings)))
  end
 end;
val _=List.app check [("0",23,"recursive"),("35",3,"recursive")];
val _=require "CALLER_SLOT_COVERAGE" (W.test_leaf_slots [nat 0] [W.LPCAtom(W.Var(nat 0))]);
val _=require "REJECT_UNCOVERED_CALLER_SLOT" (not(W.test_leaf_slots [nat 0] [W.LPCAtom(W.Var(nat 1))]));
val _=print "CONS_NODE_FIXTURES_PASSED_FULL_FAMILY_OPEN\n";
