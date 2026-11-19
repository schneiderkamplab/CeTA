(* Coordinate evidence only: not acceptance of an actual boundary or Split. *)
structure Unsynchronized = struct datatype ref = datatype ref end;
use "target/source-recursive-entry-link/Recursive_Entry_Link_Check.ML";
structure W = Recursive_Entry_Link_Check;
fun input s = map (fn c => W.Chr(IntInf.fromInt(Char.ord c))) (String.explode s);
fun tokens c s = String.tokens (fn x=>x=c) s;
fun require label b = if b then print(label ^ " PASS\n") else raise Fail label;
fun read path = let val s=TextIO.openIn path val text=TextIO.inputAll s in TextIO.closeIn s; text end;
fun check line = let
 val (label,source,target,raw)=case tokens #"|" line of [a,b,c,d]=>(a,b,c,d) | _=>raise Fail "fixture"
 val src=map input(tokens #"," source)
 val dst=map input(tokens #"," target)
 val maps=map(fn s=>case tokens #":" s of [a,b]=>(input a,W.Var(input b)) | _=>raise Fail "binding") (tokens #"," raw)
 fun run target bindings=W.test_entry_transport src target bindings
 fun replace slot term = (slot,term)::List.filter(fn(v,_)=>v<>slot)maps
 val _=require ("RETAINED_COORDINATES " ^ label) (run dst maps)
 val _=List.app(fn slot=>require ("REJECT_CHANGED_COORDINATE " ^ label)
   (not(run dst (replace slot (W.Var(input "wrong"))))))dst
 val _=require ("REJECT_OUTPUT_ALIAS " ^ label)
   (not(run dst (replace (List.nth(dst,2)) (W.Var(List.nth(src,4))))))
 val _=require ("REJECT_GROWING_TAIL " ^ label)
   (not(run dst (replace (List.nth(dst,3)) (W.Fun(W.LPCUser(input "cons"),[W.Var(hd src),W.Var(List.nth(src,3))])))))
 val _=require ("REJECT_PARAMETER_WRAPPER " ^ label)
   (not(run dst (replace (List.nth(dst,1)) (W.Fun(W.LPCUser(input "wrap"),[W.Var(List.nth(src,1))])))))
 val _=require ("REJECT_INCOMPLETE_ROLES " ^ label) (not(run (tl dst) maps))
 (* Missing identity bindings are valid: the instance substitution defaults to identity. *)
 val _=require ("UNUSED_IDENTITY_REMOVAL " ^ label) (run dst [])
 val renamed=map(fn i=>input("renamed" ^ Int.toString i)) [0,1,2,3,4]
 val renamed_maps=ListPair.zip(renamed,map W.Var src)
 val _=require ("RENAMED_COORDINATES " ^ label) (run renamed renamed_maps)
 val _=List.app(fn slot=>require ("REJECT_MISSING_RENAMED_BINDING " ^ label)
   (not(run renamed (List.filter(fn(v,_)=>v<>slot)renamed_maps))))renamed
 in () end;
val _=List.app check (tokens #"\n" (read(valOf(OS.Process.getEnv "BOUNDARY_FIXTURES")))) ;
val _=print "RECURSIVE_ENTRY_LINK_FIXTURES_PASSED_BOUNDARIES_OPEN\n";
