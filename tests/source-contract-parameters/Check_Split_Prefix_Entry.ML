structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-split-prefix-entry/Split_Prefix_Entry_Check.ML";
structure W = Split_Prefix_Entry_Check;
fun input s = map (fn c => W.Chr(IntInf.fromInt(Char.ord c))) (String.explode s);
fun nat n = W.Nat(IntInf.fromInt n);
fun tokens c s = String.tokens (fn x=>x=c) s;
fun require label b = if b then print(label ^ " PASS\n") else raise Fail label;
fun read path = let val s=TextIO.openIn path val text=TextIO.inputAll s in TextIO.closeIn s; text end;
fun check line = let
 val (label,raw,roles,indices)=case tokens #"|" line of [a,b,c,d]=>(a,b,c,d) | _=>raise Fail "fixture"
 val payload=map (W.Var o input) (tokens #"," raw)
 val (h,t,c)=case map input(tokens #"," roles) of [a,b,c]=>(a,b,c) | _=>raise Fail "roles"
 val (hi,ti,ci)=case map (valOf o Int.fromString) (tokens #"," indices) of [a,b,c]=>(a,b,c) | _=>raise Fail "indices"
 fun run xs hidx tidx cidx=W.test_prefix_slots xs h t c (nat hidx) (nat tidx) (nat cidx)
 fun replace idx term=ListPair.map(fn(i,v)=>if i=idx then term else v)(List.tabulate(length payload,fn i=>i),payload)
 val _=require ("RETAINED_PREFIX " ^ label) (run payload hi ti ci)
 val _=List.app(fn idx=>require ("REJECT_WRONG_ROLE " ^ label)
   (not(run (replace idx (W.Var(input "wrong"))) hi ti ci))) [hi,ti,ci]
 val _=List.app(fn idx=>require ("REJECT_MISSING_ROLE " ^ label)
   (not(run (List.take(payload,idx) @ List.drop(payload,idx+1)) hi ti ci))) [hi,ti,ci]
 val _=require ("REJECT_OUT_OF_RANGE_HELPER " ^ label) (not(run payload (length payload) ti ci))
 val _=require ("REJECT_OUT_OF_RANGE_TAIL " ^ label) (not(run payload hi (length payload) ci))
 val _=require ("REJECT_OUT_OF_RANGE_CALLER " ^ label) (not(run payload hi ti (length payload)))
 val _=require ("REJECT_SWAPPED_HELPER_TAIL " ^ label) (not(run payload ti hi ci))
 val _=require ("REJECT_ALIASED_OUTPUTS " ^ label) (not(run payload hi ti hi))
 val _=require ("REJECT_FORGED_GROUND_CALLER " ^ label)
  (not(run (replace ci (W.Fun(W.LPCUser(input "forged"),[]))) hi ti ci))
 val _=require ("UNUSED_PAYLOAD_REMOVAL " ^ label)
  (run (payload @ [W.Var(input "unused")]) hi ti ci andalso run payload hi ti ci)
 val required=[List.nth(payload,hi),List.nth(payload,ti),List.nth(payload,ci)]
 val _=require ("ONLY_REQUIRED_COORDINATES " ^ label) (run required 0 1 2)
 in () end;
val _=List.app check(tokens #"\n" (read(valOf(OS.Process.getEnv "PREFIX_FIXTURES")))) ;
val _=print "SPLIT_PREFIX_ENTRY_FIXTURES_PASSED_RETURNS_OPEN\n";
