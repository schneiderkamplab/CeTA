(* Fixture replay only. The export is generated from Parameter_Export.thy. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-contract-development/Parameter_Check.ML";
structure W = Parameter_Check;
fun read_file path = let val s=TextIO.openIn path val text=TextIO.inputAll s
 in TextIO.closeIn s; text end;
fun input s = map (fn c => W.Chr(IntInf.fromInt(Char.ord c))) (String.explode s);
fun output cs = String.implode(map(fn W.Chr n => Char.chr(IntInf.toInt n)) cs);
val directory = valOf(OS.Process.getEnv "OBSERVER_XML_DIRECTORY");
fun decode parser name = case parser(input(read_file(directory ^ "/" ^ name))) of
 W.Sumbot(W.Inr x)=>x | W.Sumbot(W.Inl e)=>raise Fail(name ^ ": " ^ output e);
fun require name b = if b then print(name ^ " PASS\n") else raise Fail name;
fun goals ((W.LPCGoals gs,_)::_) = gs | goals _ = raise Fail "expected active goals";
fun call_args (W.LPCAtom(W.Fun(_,args))::_) = args
 | call_args _ = raise Fail "expected direct call";
fun equality [] = raise Fail "expected equality"
 | equality (W.LPCUnify(a,b)::_) = (a,b)
 | equality (_::gs) = equality gs;
fun entry (region,index) = let
 val (nds,(states,(contexts,(_,(_,(_,(_,_))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val args=call_args(goals(List.nth(states,index)))
 val parameter=List.nth(args,1)
 val ground=W.lpcn_ground(List.nth(nds,index))
 val context=List.nth(contexts,index)
 val label=region ^ ":" ^ Int.toString index
 in
 require ("ENTRY " ^ label) (W.test_parameter_entry ground context parameter);
 require ("MISSING_GROUND " ^ label) (not(W.test_parameter_entry [] ([],([],[])) parameter));
 require ("WRONG_ENTRY_COORDINATE " ^ label)
  (not(W.test_parameter_entry ground context (hd args)))
 end;
fun branch region = let
 val (_,(states,(_, (frees,(_,(_,(_,_))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val links=decode W.lpp_decode_separation_links ("links-" ^ region ^ ".xml")
 val (a,b)=equality(goals(List.nth(states,12)))
 val selected=case a of W.Var x=>x | _=>raise Fail "non-variable selected syntax"
 val (f,g,parameter)=case b of W.Fun(f,[W.Fun(g,[]),W.Var p])=>(f,g,p)
  | _=>raise Fail "unexpected parameter replacement"
 val p=W.Var parameter
 fun route (i,j) = let
  val edge=hd(List.nth(links,i))
  val bindings=W.lpcl_bindings edge
  val source=if i=5 then hd(call_args(goals(List.nth(states,i))))
   else #1(equality(goals(List.nth(states,i))))
  val target= #1(equality(goals(List.nth(states,j))))
  val label=region ^ ":" ^ Int.toString i ^ "->" ^ Int.toString j
  in
  require ("TARGET " ^ label) (W.lpcl_target edge=W.Nat(IntInf.fromInt j));
  require ("FREE_COORDINATE " ^ label) (W.test_parameter_coordinate source target bindings);
  require ("PARAMETER_COORDINATE " ^ label) (W.test_parameter_coordinate p p bindings);
  require ("WRONG_PARAMETER_MAP " ^ label)
   (not(W.test_parameter_coordinate p p [(parameter,a)]))
  end
 in
 require ("RETAINED_FREE_TABLE_EMPTY " ^ region) (null(List.nth(frees,12)));
 require ("MISSING_BRANCH_FREE_REJECTED " ^ region)
  (not(W.test_parameter_binding (List.nth(frees,12)) parameter f g a b));
 require ("BINDING_WITH_EXPLICIT_FREE_PREMISE " ^ region)
  (W.test_parameter_binding [selected] parameter f g a b);
 require ("WRONG_REPLACEMENT_PARAMETER " ^ region)
  (not(W.test_parameter_binding [selected] selected f g a b));
 List.app route [(5,8),(8,12)]
 end;
val _=List.app entry [("0",0),("35",7),("47",0)];
val _=List.app branch ["0","47"];
val _=print "SOURCE_PARAMETER_FIXTURES_PASSED_RETURN_CONTRACTS_OPEN\n";
