(* Local successor checks; no complete observer-family or Split acceptance. *)
nonfix before;
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-acquired-block-rows/Acquired_Block_Rows_Check.ML";
structure W = Acquired_Block_Rows_Check;
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
fun replace xs i x = ListPair.map (fn (j,y)=>if i=j then x else y)
 (List.tabulate(length xs,fn j=>j),xs);
fun check region = let
 val (nds,(states,(contexts,(frees,(functors,(seps,(out,arity))))))) =
  decode W.lpp_decode_separation_states ("states-" ^ region ^ ".xml")
 val actions=decode W.lpp_decode_separation_actions ("actions-" ^ region ^ ".xml")
 val witnesses=decode W.lpp_decode_separation_witnesses ("region-" ^ region ^ ".xml")
 val (p,q)=decode W.lpp_decode_separation_subject ("subject-" ^ region ^ ".xml")
 fun eq row sts sep act wit = W.lpp_check_observer_equality_row (fn _=>[]) (nat 10000)
  p q nds sts contexts frees functors sep (nat row) act wit
 fun equality row = let
  val action=List.nth(actions,row) val witness=List.nth(witnesses,row)
  val label=region ^ ":" ^ Int.toString row
  val _=require ("EQUALITY_SIMULATION_ROW " ^ label) (eq row states seps action witness)
  val _=require ("REJECT_MISSING_ACTION " ^ label) (not(eq row states seps NONE witness))
  val _=require ("REJECT_MISSING_WITNESS " ^ label) (not(eq row states seps action NONE))
  val _=require ("REJECT_WRONG_STATE " ^ label) (not(eq row (replace states row []) seps action witness))
  val _=require ("REJECT_ORDINARY_WITNESS " ^ label)
   (not(eq row states seps action (SOME W.LPPSOrdinaryAction)))
 in () end
 val _=List.app equality [10,13]
 val _=require ("REJECT_MISSING_REFLEXIVE_CONTEXT " ^ region)
  (not(W.lpp_check_observer_equality_row (fn _=>[]) (nat 10000)
   p q nds states (replace contexts 10 (List.nth(contexts,6))) frees functors seps
   (nat 10) (List.nth(actions,10)) (List.nth(witnesses,10))))
 val _=require ("REJECT_MISSING_RESIDUAL " ^ region)
  (not(W.lpp_check_observer_equality_row (fn _=>[]) (nat 10000)
   p [] nds states contexts frees functors seps
   (nat 13) (List.nth(actions,13)) (List.nth(witnesses,13))))
 val _=require ("REJECT_DROPPED_PAIR_SEPARATION " ^ region)
  (not(eq 13 states (replace seps 13 []) (List.nth(actions,13)) (List.nth(witnesses,13))))
 val _=require ("REJECT_DROPPED_EXIT_STATE " ^ region)
  (not(eq 13 (replace states 17 []) seps (List.nth(actions,13)) (List.nth(witnesses,13))))
 fun univ act wit = W.lpp_check_observer_univ_row (fn _=>[]) (nat 10000)
  p q nds states contexts frees functors seps out arity (nat 6) act wit
 val _=require ("UNIV_NORMALIZATION_AND_EXIT " ^ region) (univ (List.nth(actions,6)) (List.nth(witnesses,6)))
 val _=require ("REJECT_MISSING_UNIV_WITNESS " ^ region) (not(univ (List.nth(actions,6)) NONE))
 in () end;
val _ = List.app check ["0","47"];
val _ = print "ACQUIRED_BLOCK_ROWS_PASSED_FULL_BLOCK_ASSEMBLY_OPEN\n";
