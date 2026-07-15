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
import qualified Mapping_Impl;
import qualified Trs;
import qualified Trs_Impl;
import qualified Error_Monad;
import qualified Check_Monad;
import qualified List;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Subterm_and_Context;
import qualified Product_Type;
import qualified Term_More;
import qualified Option;
import qualified HOL;
import qualified Term;
import qualified Set;
import qualified Arith;
import qualified Multiset;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;

check_AC_rule ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a,
      Eq b) => (Term.Term a b, Term.Term a b) -> Bool;
check_AC_rule lr =
  (case lr of {
    (l, r) ->
      (if Term.is_Var l then False
        else let {
               f = fst (Option.the (Term.root l));
             } in Collection_Eq.set_eq (Subterm_and_Context.funas_term l)
                    (Set.insert (f, Arith.nat_of_integer (2 :: Integer))
                      Set.bot_set) &&
                    Collection_Eq.set_eq (Subterm_and_Context.funas_term r)
                      (Set.insert (f, Arith.nat_of_integer (2 :: Integer))
                        Set.bot_set) &&
                      Term.vars_term_ms l == Term.vars_term_ms r &&
                        Term_More.funs_term_ms l == Term_More.funs_term_ms r);
  });

check_ext_rule3 ::
  forall a b.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b) => (Term.Term a b, Term.Term a b) ->
                 a -> Set.Set b -> (Term.Term a b, Term.Term a b) -> Bool;
check_ext_rule3 (la, ra) f xb
  (Term.Fun ga [Term.Fun ha [Term.Var xa, l], Term.Var ya],
    Term.Fun g [Term.Fun h [Term.Var x, r], Term.Var y])
  = (la, (ra, (f, (f, (f, (f, (xa, ya))))))) ==
      (l, (r, (ga, (g, (ha, (h, (x, y))))))) &&
      not (x == y) && not (Set.member x xb) && not (Set.member y xb);
check_ext_rule3 uu uv uw (Term.Var vb, va) = False;
check_ext_rule3 uu uv uw (Term.Fun vb [], va) = False;
check_ext_rule3 uu uv uw (Term.Fun vb (Term.Var vf : ve), va) = False;
check_ext_rule3 uu uv uw (Term.Fun vb (Term.Fun vf [] : ve), va) = False;
check_ext_rule3 uu uv uw
  (Term.Fun vb (Term.Fun vf (Term.Fun vj vk : vi) : ve), va) = False;
check_ext_rule3 uu uv uw (Term.Fun vb (Term.Fun vf [vh] : ve), va) = False;
check_ext_rule3 uu uv uw
  (Term.Fun vb (Term.Fun vf (vh : vj : vl : vm) : ve), va) = False;
check_ext_rule3 uu uv uw (Term.Fun vb [vd], va) = False;
check_ext_rule3 uu uv uw (Term.Fun vb (vd : Term.Fun vh vi : vg), va) = False;
check_ext_rule3 uu uv uw (Term.Fun vb (vd : vf : vh : vi), va) = False;
check_ext_rule3 uu uv uw (v, Term.Var vb) = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb []) = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb (Term.Var vf : ve)) = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb (Term.Fun vf [] : ve)) = False;
check_ext_rule3 uu uv uw
  (v, Term.Fun vb (Term.Fun vf (Term.Fun vj vk : vi) : ve)) = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb (Term.Fun vf [vh] : ve)) = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb (Term.Fun vf (vh : vj : vl : vm) : ve))
  = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb [vd]) = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb (vd : Term.Fun vh vi : vg)) = False;
check_ext_rule3 uu uv uw (v, Term.Fun vb (vd : vf : vh : vi)) = False;

check_ext_rule2 ::
  forall a b.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b) => (Term.Term a b, Term.Term a b) ->
                 a -> Set.Set b -> (Term.Term a b, Term.Term a b) -> Bool;
check_ext_rule2 (la, ra) f xb
  (Term.Fun ga [Term.Var xa, l], Term.Fun g [Term.Var x, r]) =
  (la, (ra, (f, (f, xa)))) == (l, (r, (ga, (g, x)))) && not (Set.member xa xb);
check_ext_rule2 uu uv uw (Term.Var vb, va) = False;
check_ext_rule2 uu uv uw (Term.Fun vb [], va) = False;
check_ext_rule2 uu uv uw (Term.Fun vb (Term.Fun vf vg : ve), va) = False;
check_ext_rule2 uu uv uw (Term.Fun vb [vd], va) = False;
check_ext_rule2 uu uv uw (Term.Fun vb (vd : vf : vh : vi), va) = False;
check_ext_rule2 uu uv uw (v, Term.Var vb) = False;
check_ext_rule2 uu uv uw (v, Term.Fun vb []) = False;
check_ext_rule2 uu uv uw (v, Term.Fun vb (Term.Fun vf vg : ve)) = False;
check_ext_rule2 uu uv uw (v, Term.Fun vb [vd]) = False;
check_ext_rule2 uu uv uw (v, Term.Fun vb (vd : vf : vh : vi)) = False;

check_ext_rule1 ::
  forall a b.
    (Eq a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b) => (Term.Term a b, Term.Term a b) ->
                 a -> Set.Set b -> (Term.Term a b, Term.Term a b) -> Bool;
check_ext_rule1 (la, ra) f xb
  (Term.Fun ga [l, Term.Var xa], Term.Fun g [r, Term.Var x]) =
  (la, (ra, (f, (f, xa)))) == (l, (r, (ga, (g, x)))) && not (Set.member xa xb);
check_ext_rule1 uu uv uw (Term.Var vb, va) = False;
check_ext_rule1 uu uv uw (Term.Fun vb [], va) = False;
check_ext_rule1 uu uv uw (Term.Fun vb [vd], va) = False;
check_ext_rule1 uu uv uw (Term.Fun vb (vd : Term.Fun vh vi : vg), va) = False;
check_ext_rule1 uu uv uw (Term.Fun vb (vd : vf : vh : vi), va) = False;
check_ext_rule1 uu uv uw (v, Term.Var vb) = False;
check_ext_rule1 uu uv uw (v, Term.Fun vb []) = False;
check_ext_rule1 uu uv uw (v, Term.Fun vb [vd]) = False;
check_ext_rule1 uu uv uw (v, Term.Fun vb (vd : Term.Fun vh vi : vg)) = False;
check_ext_rule1 uu uv uw (v, Term.Fun vb (vd : vf : vh : vi)) = False;

check_ext_rule ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => [(Term.Term a b, Term.Term a b)] ->
                                Set.Set a ->
                                  Set.Set a ->
                                    (Term.Term a b, Term.Term a b) -> Bool;
check_ext_rule rext a c lr =
  (case lr of {
    (l, _) ->
      (if Term.is_Var l ||
            (not (Arith.equal_nat (List.size_list (Term.args l))
                   (Arith.nat_of_integer (2 :: Integer))) ||
              not (Set.member (fst (Option.the (Term.root l))) a))
        then True
        else let {
               f = fst (Option.the (Term.root l));
               x = Trs.vars_rule lr;
             } in any (check_ext_rule1 lr f x) rext &&
                    (if not (Set.member f c)
                      then any (check_ext_rule2 lr f x) rext &&
                             any (check_ext_rule3 lr f x) rext
                      else True));
  });

check_ext_trs ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [a] ->
                                    [a] ->
                                      [(Term.Term a b, Term.Term a b)] ->
Sum_Type.Sum (String -> String) ();
check_ext_trs r a c rext =
  let {
    aa = List.set a;
    ca = List.set c;
  } in Error_Monad.catch_error
         (Error_Monad.catch_error
           (Error_Monad.forallM
             (\ lr ->
               Check_Monad.check (check_ext_rule rext aa ca lr)
                 (((Shows_Literal.showsl_lit
                      "could not find extended rules for rule l -> r:\n  " .
                     Trs_Impl.showsl_rule lr) .
                    Shows_Literal.showsl_lit
                      "\n  expecting rule f(l,x) -> f(r,x) for all A and AC symbols,\n") .
                   Shows_Literal.showsl_lit
                     "and rules f(x,l) -> f(x,r) and f(f(x,l),y) -> f(f(x,r),y) for all A symbols"))
             r)
           (\ x -> Sum_Type.Inl (snd x)))
         (\ x ->
           Sum_Type.Inl
             (Shows_Literal.showsl_lit
                "could not ensure validity of AC-extended system\n" .
               x));

check_AC_theory ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_AC_theory e =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ lr ->
        Check_Monad.check (check_AC_rule lr)
          ((Shows_Literal.showsl_lit "rule " . Trs_Impl.showsl_rule lr) .
            Shows_Literal.showsl_lit " violates AC-property"))
      e)
    (\ x -> Sum_Type.Inl (snd x));

check_E_reachable ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [(Term.Term a b, Term.Term a b)] ->
Term.Term a b -> Term.Term a b -> Bool;
check_E_reachable e s t =
  List.member (RTrancl.mk_rtrancl_list Term.equal_term (Trs_Impl.rewrite e) [s])
    t;

check_only_C_rule ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Eq b) => Set.Set a -> (Term.Term a b, Term.Term a b) -> Bool;
check_only_C_rule oc lr =
  (case lr of {
    (Term.Var _, _) -> True;
    (Term.Fun _ [], _) -> True;
    (Term.Fun _ [_], _) -> True;
    (Term.Fun f [s, t], r) ->
      (if Set.member f oc then Term.equal_term r (Term.Fun f [t, s]) else True);
    (Term.Fun _ (_ : _ : _ : _), _) -> True;
  });

check_AC_same_as_E ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a, Mapping_Impl.Mapping_impl a,
      Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => a -> a -> a ->
    [b] ->
      [b] ->
        [(Term.Term b a, Term.Term b a)] -> Sum_Type.Sum (String -> String) ();
check_AC_same_as_E x y z a c e =
  Error_Monad.catch_error
    (let {
       xa = Term.Var x;
       ya = Term.Var y;
       za = Term.Var z;
     } in Error_Monad.bind
            (Error_Monad.catch_error
              (Error_Monad.catch_error
                (Error_Monad.forallM
                  (\ f ->
                    Check_Monad.check
                      (check_E_reachable e (Term.Fun f [xa, ya])
                        (Term.Fun f [ya, xa]))
                      f)
                  c)
                (\ xb -> Sum_Type.Inl (snd xb)))
              (\ xb ->
                Sum_Type.Inl
                  ((Shows_Literal.showsl_lit "could not simulate C-rules for " .
                     Shows_Literal.showsl xb) .
                    Shows_Literal.showsl_lit " by E")))
            (\ _ ->
              Error_Monad.bind
                (Error_Monad.catch_error
                  (Error_Monad.catch_error
                    (Error_Monad.forallM
                      (\ f ->
                        Check_Monad.check
                          (check_E_reachable e
                            (Term.Fun f [xa, Term.Fun f [ya, za]])
                            (Term.Fun f [Term.Fun f [xa, ya], za]))
                          f)
                      a)
                    (\ xb -> Sum_Type.Inl (snd xb)))
                  (\ xb ->
                    Sum_Type.Inl
                      ((Shows_Literal.showsl_lit
                          "could not simulate A-rules for " .
                         Shows_Literal.showsl xb) .
                        Shows_Literal.showsl_lit " by E")))
                (\ _ ->
                  Error_Monad.bind
                    (Error_Monad.catch_error
                      (Error_Monad.catch_error
                        (Error_Monad.forallM
                          (\ f ->
                            Check_Monad.check
                              (check_E_reachable e
                                (Term.Fun f [Term.Fun f [xa, ya], za])
                                (Term.Fun f [xa, Term.Fun f [ya, za]]))
                              f)
                          a)
                        (\ xb -> Sum_Type.Inl (snd xb)))
                      (\ xb ->
                        Sum_Type.Inl
                          ((Shows_Literal.showsl_lit
                              "could not simulate A-rules for " .
                             Shows_Literal.showsl xb) .
                            Shows_Literal.showsl_lit " by E")))
                    (\ _ ->
                      Error_Monad.catch_error
                        (Error_Monad.catch_error
                          (Error_Monad.forallM
                            (\ (l, r) ->
                              Check_Monad.check
                                (AC_Equivalence.equal_acterm
                                  (AC_Equivalence.aocnf (List.set a)
                                    (List.set c) l)
                                  (AC_Equivalence.aocnf (List.set a)
                                    (List.set c) r))
                                (l, r))
                            e)
                          (\ xb -> Sum_Type.Inl (snd xb)))
                        (\ xb ->
                          Sum_Type.Inl
                            ((Shows_Literal.showsl_lit "equation " .
                               Trs_Impl.showsl_rule xb) .
                              Shows_Literal.showsl_lit
                                " is not AC-equivalent"))))))
    (\ xa ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "could not ensure that equations simulate AC-equivalence\n" .
          xa));

check_only_C_theory ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => Set.Set a ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    Sum_Type.Sum (String -> String) ();
check_only_C_theory oc e =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ lr ->
        Check_Monad.check (check_only_C_rule oc lr)
          ((Shows_Literal.showsl_lit "rule " . Trs_Impl.showsl_rule lr) .
            Shows_Literal.showsl_lit " violates only-C-property"))
      e)
    (\ x -> Sum_Type.Inl (snd x));

check_size_preserving_trs ::
  forall a b.
    (Shows_Literal.Showl a, Eq b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_size_preserving_trs e =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (l, r) ->
          Check_Monad.check
            (Arith.equal_nat (AC_Rewriting.num_symbs l)
               (AC_Rewriting.num_symbs r) &&
              Term.vars_term_ms l == Term.vars_term_ms r)
            ((Shows_Literal.showsl_lit "rule " . Trs_Impl.showsl_rule (l, r)) .
              Shows_Literal.showsl_lit " is not size preserving"))
        e)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit "TRS is not size-preserving\n" . x));

check_symmetric_AC_theory ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Eq b, Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) ();
check_symmetric_AC_theory e =
  Error_Monad.bind (check_AC_theory e)
    (\ _ ->
      Error_Monad.catch_error
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ (l, r) ->
              Check_Monad.check (check_E_reachable e r l)
                (((Shows_Literal.showsl_lit "rhs " . Term_More.showsl_terma r) .
                   Shows_Literal.showsl_lit " does not rewrite to lhs ") .
                  Term_More.showsl_terma l))
            e)
          (\ x -> Sum_Type.Inl (snd x)))
        (\ x ->
          Sum_Type.Inl
            (Shows_Literal.showsl_lit "theory is not symmetric\n" . x)));

}
