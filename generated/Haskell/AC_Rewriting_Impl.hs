{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  AC_Rewriting_Impl(check_ext_trs, check_AC_same_as_E, check_only_C_theory,
                     check_size_preserving_trs, check_symmetric_AC_theory)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Uint;
import qualified Array;
import qualified IArray;
import qualified Uint32;
import qualified Uint64;
import qualified Data_Bits;
import qualified Bit_Shifts;
import qualified Str_Literal;
import qualified AC_Rewriting;
import qualified AC_Equivalence;
import qualified RTrancl;
import qualified Mapping;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified Sum_Type;
import qualified HOL;
import qualified Term_Rewriting;
import qualified Multiset;
import qualified Arith;

check_AC_rule ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Eq b) => (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
check_AC_rule lr =
  (case lr of {
    (l, r) ->
      (if Term_Rewriting.is_Var l then False
        else let {
               f = fst (Arith.the (Term_Rewriting.root l));
             } in Arith.set_eq (Term_Rewriting.funas_term l)
                    (Arith.insert (f, Arith.nat_of_integer (2 :: Integer))
                      Arith.bot_set) &&
                    Arith.set_eq (Term_Rewriting.funas_term r)
                      (Arith.insert (f, Arith.nat_of_integer (2 :: Integer))
                        Arith.bot_set) &&
                      Term_Rewriting.vars_term_ms l ==
                        Term_Rewriting.vars_term_ms r &&
                        Term_Rewriting.funs_term_ms l ==
                          Term_Rewriting.funs_term_ms r);
  });

check_ext_rule3 ::
  forall a b.
    (Eq a, Arith.Ceq b, Arith.Ccompare b,
      Eq b) => (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                 a -> Arith.Set b ->
                        (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                          Bool;
check_ext_rule3 (la, ra) f xb
  (Term_Rewriting.Fun ga
     [Term_Rewriting.Fun ha [Term_Rewriting.Var xa, l], Term_Rewriting.Var ya],
    Term_Rewriting.Fun g
      [Term_Rewriting.Fun h [Term_Rewriting.Var x, r], Term_Rewriting.Var y])
  = (la, (ra, (f, (f, (f, (f, (xa, ya))))))) ==
      (l, (r, (ga, (g, (ha, (h, (x, y))))))) &&
      not (x == y) && not (Arith.member x xb) && not (Arith.member y xb);
check_ext_rule3 uu uv uw (Term_Rewriting.Var vb, va) = False;
check_ext_rule3 uu uv uw (Term_Rewriting.Fun vb [], va) = False;
check_ext_rule3 uu uv uw
  (Term_Rewriting.Fun vb (Term_Rewriting.Var vf : ve), va) = False;
check_ext_rule3 uu uv uw
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf [] : ve), va) = False;
check_ext_rule3 uu uv uw
  (Term_Rewriting.Fun vb
     (Term_Rewriting.Fun vf (Term_Rewriting.Fun vj vk : vi) : ve),
    va)
  = False;
check_ext_rule3 uu uv uw
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf [vh] : ve), va) = False;
check_ext_rule3 uu uv uw
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf (vh : vj : vl : vm) : ve), va) =
  False;
check_ext_rule3 uu uv uw (Term_Rewriting.Fun vb [vd], va) = False;
check_ext_rule3 uu uv uw
  (Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh vi : vg), va) = False;
check_ext_rule3 uu uv uw (Term_Rewriting.Fun vb (vd : vf : vh : vi), va) =
  False;
check_ext_rule3 uu uv uw (v, Term_Rewriting.Var vb) = False;
check_ext_rule3 uu uv uw (v, Term_Rewriting.Fun vb []) = False;
check_ext_rule3 uu uv uw (v, Term_Rewriting.Fun vb (Term_Rewriting.Var vf : ve))
  = False;
check_ext_rule3 uu uv uw
  (v, Term_Rewriting.Fun vb (Term_Rewriting.Fun vf [] : ve)) = False;
check_ext_rule3 uu uv uw
  (v, Term_Rewriting.Fun vb
        (Term_Rewriting.Fun vf (Term_Rewriting.Fun vj vk : vi) : ve))
  = False;
check_ext_rule3 uu uv uw
  (v, Term_Rewriting.Fun vb (Term_Rewriting.Fun vf [vh] : ve)) = False;
check_ext_rule3 uu uv uw
  (v, Term_Rewriting.Fun vb (Term_Rewriting.Fun vf (vh : vj : vl : vm) : ve)) =
  False;
check_ext_rule3 uu uv uw (v, Term_Rewriting.Fun vb [vd]) = False;
check_ext_rule3 uu uv uw
  (v, Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh vi : vg)) = False;
check_ext_rule3 uu uv uw (v, Term_Rewriting.Fun vb (vd : vf : vh : vi)) = False;

check_ext_rule2 ::
  forall a b.
    (Eq a, Arith.Ceq b, Arith.Ccompare b,
      Eq b) => (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                 a -> Arith.Set b ->
                        (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                          Bool;
check_ext_rule2 (la, ra) f xb
  (Term_Rewriting.Fun ga [Term_Rewriting.Var xa, l],
    Term_Rewriting.Fun g [Term_Rewriting.Var x, r])
  = (la, (ra, (f, (f, xa)))) == (l, (r, (ga, (g, x)))) &&
      not (Arith.member xa xb);
check_ext_rule2 uu uv uw (Term_Rewriting.Var vb, va) = False;
check_ext_rule2 uu uv uw (Term_Rewriting.Fun vb [], va) = False;
check_ext_rule2 uu uv uw
  (Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve), va) = False;
check_ext_rule2 uu uv uw (Term_Rewriting.Fun vb [vd], va) = False;
check_ext_rule2 uu uv uw (Term_Rewriting.Fun vb (vd : vf : vh : vi), va) =
  False;
check_ext_rule2 uu uv uw (v, Term_Rewriting.Var vb) = False;
check_ext_rule2 uu uv uw (v, Term_Rewriting.Fun vb []) = False;
check_ext_rule2 uu uv uw
  (v, Term_Rewriting.Fun vb (Term_Rewriting.Fun vf vg : ve)) = False;
check_ext_rule2 uu uv uw (v, Term_Rewriting.Fun vb [vd]) = False;
check_ext_rule2 uu uv uw (v, Term_Rewriting.Fun vb (vd : vf : vh : vi)) = False;

check_ext_rule1 ::
  forall a b.
    (Eq a, Arith.Ceq b, Arith.Ccompare b,
      Eq b) => (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                 a -> Arith.Set b ->
                        (Term_Rewriting.Term a b, Term_Rewriting.Term a b) ->
                          Bool;
check_ext_rule1 (la, ra) f xb
  (Term_Rewriting.Fun ga [l, Term_Rewriting.Var xa],
    Term_Rewriting.Fun g [r, Term_Rewriting.Var x])
  = (la, (ra, (f, (f, xa)))) == (l, (r, (ga, (g, x)))) &&
      not (Arith.member xa xb);
check_ext_rule1 uu uv uw (Term_Rewriting.Var vb, va) = False;
check_ext_rule1 uu uv uw (Term_Rewriting.Fun vb [], va) = False;
check_ext_rule1 uu uv uw (Term_Rewriting.Fun vb [vd], va) = False;
check_ext_rule1 uu uv uw
  (Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh vi : vg), va) = False;
check_ext_rule1 uu uv uw (Term_Rewriting.Fun vb (vd : vf : vh : vi), va) =
  False;
check_ext_rule1 uu uv uw (v, Term_Rewriting.Var vb) = False;
check_ext_rule1 uu uv uw (v, Term_Rewriting.Fun vb []) = False;
check_ext_rule1 uu uv uw (v, Term_Rewriting.Fun vb [vd]) = False;
check_ext_rule1 uu uv uw
  (v, Term_Rewriting.Fun vb (vd : Term_Rewriting.Fun vh vi : vg)) = False;
check_ext_rule1 uu uv uw (v, Term_Rewriting.Fun vb (vd : vf : vh : vi)) = False;

check_ext_rule ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b) => [(Term_Rewriting.Term a b,
                              Term_Rewriting.Term a b)] ->
                             Arith.Set a ->
                               Arith.Set a ->
                                 (Term_Rewriting.Term a b,
                                   Term_Rewriting.Term a b) ->
                                   Bool;
check_ext_rule rext a c lr =
  (case lr of {
    (l, _) ->
      (if Term_Rewriting.is_Var l ||
            (not (Arith.equal_nat (Arith.size_list (Term_Rewriting.args l))
                   (Arith.nat_of_integer (2 :: Integer))) ||
              not (Arith.member (fst (Arith.the (Term_Rewriting.root l))) a))
        then True
        else let {
               f = fst (Arith.the (Term_Rewriting.root l));
               x = Term_Rewriting.vars_rule lr;
             } in any (check_ext_rule1 lr f x) rext &&
                    (if not (Arith.member f c)
                      then any (check_ext_rule2 lr f x) rext &&
                             any (check_ext_rule3 lr f x) rext
                      else True));
  });

check_ext_trs ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Arith.Ceq b, Arith.Ccompare b, Eq b,
      Arith.Set_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   [a] ->
                                     [a] ->
                                       [(Term_Rewriting.Term a b,
  Term_Rewriting.Term a b)] ->
 Sum_Type.Sum (String -> String) ();
check_ext_trs r a c rext =
  let {
    aa = Arith.set a;
    ca = Arith.set c;
  } in Error_Monad.catch_error
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ lr ->
               Check_Monad.check (check_ext_rule rext aa ca lr)
                 (((Term_Rewriting.showsl_lit
                      "could not find extended rules for rule l -> r:\n  " .
                     Term_Rewriting.showsl_rule lr) .
                    Term_Rewriting.showsl_lit
                      "\n  expecting rule f(l,x) -> f(r,x) for all A and AC symbols,\n") .
                   Term_Rewriting.showsl_lit
                     "and rules f(x,l) -> f(x,r) and f(f(x,l),y) -> f(f(x,r),y) for all A symbols"))
             r)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ x ->
           Sum_Type.Inl
             (Term_Rewriting.showsl_lit
                "could not ensure validity of AC-extended system\n" .
               x));

check_AC_theory ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Sum_Type.Sum (String -> String) ();
check_AC_theory e =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ lr ->
        Check_Monad.check (check_AC_rule lr)
          ((Term_Rewriting.showsl_lit "rule " . Term_Rewriting.showsl_rule lr) .
            Term_Rewriting.showsl_lit " violates AC-property"))
      e)
    (\ x -> Sum_Type.Inl (snd x));

check_E_reachable ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Term_Rewriting.Term a b ->
                                     Term_Rewriting.Term a b -> Bool;
check_E_reachable e s t =
  Arith.membera
    (RTrancl.mk_rtrancl_list Term_Rewriting.equal_term
      (Term_Rewriting.rewrite e) [s])
    t;

check_only_C_rule ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a,
      Eq b) => Arith.Set a ->
                 (Term_Rewriting.Term a b, Term_Rewriting.Term a b) -> Bool;
check_only_C_rule oc lr =
  (case lr of {
    (Term_Rewriting.Var _, _) -> True;
    (Term_Rewriting.Fun _ [], _) -> True;
    (Term_Rewriting.Fun _ [_], _) -> True;
    (Term_Rewriting.Fun f [s, t], r) ->
      (if Arith.member f oc
        then Term_Rewriting.equal_term r (Term_Rewriting.Fun f [t, s])
        else True);
    (Term_Rewriting.Fun _ (_ : _ : _ : _), _) -> True;
  });

check_AC_same_as_E ::
  forall a b.
    (Arith.Ccompare a, Eq a, Mapping.Mapping_impl a, Term_Rewriting.Showl a,
      Arith.Ceq b, Arith.Ccompare b, Eq b, Arith.Set_impl b,
      Term_Rewriting.Showl b) => a -> a ->
a -> [b] ->
       [b] ->
         [(Term_Rewriting.Term b a, Term_Rewriting.Term b a)] ->
           Sum_Type.Sum (String -> String) ();
check_AC_same_as_E x y z a c e =
  Error_Monad.catch_error
    (let {
       xa = Term_Rewriting.Var x;
       ya = Term_Rewriting.Var y;
       za = Term_Rewriting.Var z;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ f ->
                    Check_Monad.check
                      (check_E_reachable e (Term_Rewriting.Fun f [xa, ya])
                        (Term_Rewriting.Fun f [ya, xa]))
                      f)
                  c)
                (\ xb -> Sum_Type.Inl (snd xb)))
              (\ xb ->
                Sum_Type.Inl
                  ((Term_Rewriting.showsl_lit
                      "could not simulate C-rules for " .
                     Term_Rewriting.showsl xb) .
                    Term_Rewriting.showsl_lit " by E")))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ f ->
                        Check_Monad.check
                          (check_E_reachable e
                            (Term_Rewriting.Fun f
                              [xa, Term_Rewriting.Fun f [ya, za]])
                            (Term_Rewriting.Fun f
                              [Term_Rewriting.Fun f [xa, ya], za]))
                          f)
                      a)
                    (\ xb -> Sum_Type.Inl (snd xb)))
                  (\ xb ->
                    Sum_Type.Inl
                      ((Term_Rewriting.showsl_lit
                          "could not simulate A-rules for " .
                         Term_Rewriting.showsl xb) .
                        Term_Rewriting.showsl_lit " by E")))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.catch_error
                        (Error_Monad.forallM
                          (\ f ->
                            Check_Monad.check
                              (check_E_reachable e
                                (Term_Rewriting.Fun f
                                  [Term_Rewriting.Fun f [xa, ya], za])
                                (Term_Rewriting.Fun f
                                  [xa, Term_Rewriting.Fun f [ya, za]]))
                              f)
                          a)
                        (\ xb -> Sum_Type.Inl (snd xb)))
                      (\ xb ->
                        Sum_Type.Inl
                          ((Term_Rewriting.showsl_lit
                              "could not simulate A-rules for " .
                             Term_Rewriting.showsl xb) .
                            Term_Rewriting.showsl_lit " by E")))
                    (\ _ ->
                      Error_Monad.catch_error
                        (Error_Monad.catch_error
                          (Error_Monad.forallM
                            (\ (l, r) ->
                              Check_Monad.check
                                (AC_Equivalence.equal_acterm
                                  (AC_Equivalence.aocnf (Arith.set a)
                                    (Arith.set c) l)
                                  (AC_Equivalence.aocnf (Arith.set a)
                                    (Arith.set c) r))
                                (l, r))
                            e)
                          (\ xb -> Sum_Type.Inl (snd xb)))
                        (\ xb ->
                          Sum_Type.Inl
                            ((Term_Rewriting.showsl_lit "equation " .
                               Term_Rewriting.showsl_rule xb) .
                              Term_Rewriting.showsl_lit
                                " is not AC-equivalent"))))))
    (\ xa ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit
           "could not ensure that equations simulate AC-equivalence\n" .
          xa));

check_only_C_theory ::
  forall a b.
    (Arith.Ceq a, Arith.Ccompare a, Eq a, Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => Arith.Set a ->
                                   [(Term_Rewriting.Term a b,
                                      Term_Rewriting.Term a b)] ->
                                     Sum_Type.Sum (String -> String) ();
check_only_C_theory oc e =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ lr ->
        Check_Monad.check (check_only_C_rule oc lr)
          ((Term_Rewriting.showsl_lit "rule " . Term_Rewriting.showsl_rule lr) .
            Term_Rewriting.showsl_lit " violates only-C-property"))
      e)
    (\ x -> Sum_Type.Inl (snd x));

check_size_preserving_trs ::
  forall a b.
    (Term_Rewriting.Showl a, Eq b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Sum_Type.Sum (String -> String) ();
check_size_preserving_trs e =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (l, r) ->
          Check_Monad.check
            (Arith.equal_nat (AC_Rewriting.num_symbs l)
               (AC_Rewriting.num_symbs r) &&
              Term_Rewriting.vars_term_ms l == Term_Rewriting.vars_term_ms r)
            ((Term_Rewriting.showsl_lit "rule " .
               Term_Rewriting.showsl_rule (l, r)) .
              Term_Rewriting.showsl_lit " is not size preserving"))
        e)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Term_Rewriting.showsl_lit "TRS is not size-preserving\n" . x));

check_symmetric_AC_theory ::
  forall a b.
    (Arith.Cenum a, Arith.Ceq a, Arith.Ccompare a, Eq a, Arith.Set_impl a,
      Term_Rewriting.Showl a, Arith.Ccompare b, Eq b, Mapping.Mapping_impl b,
      Term_Rewriting.Showl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   Sum_Type.Sum (String -> String) ();
check_symmetric_AC_theory e =
  Error_Monad.bind (check_AC_theory e)
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (l, r) ->
              Check_Monad.check (check_E_reachable e r l)
                (((Term_Rewriting.showsl_lit "rhs " .
                    Term_Rewriting.showsl_terma r) .
                   Term_Rewriting.showsl_lit " does not rewrite to lhs ") .
                  Term_Rewriting.showsl_terma l))
            e)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            (Term_Rewriting.showsl_lit "theory is not symmetric\n" . x)));

}
