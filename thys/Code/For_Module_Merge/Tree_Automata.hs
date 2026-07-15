{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Tree_Automata(Ta_rule(..), equal_ta_rule, Ta_ext(..), r_sym, r_lhs_states,
                 r_rhs, ta_rules, ta_eps, ta_final, ta_syms, trim_ta, ta_empty,
                 ta_member, intersect_ta, r_root, closed_under_rewriting)
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
import qualified Option;
import qualified Phantom_Type;
import qualified Util;
import qualified Compare;
import qualified Relation;
import qualified Complete_Lattices;
import qualified Product_Type;
import qualified Cardinality;
import qualified Abstract_Rewriting_Impl;
import qualified HOL;
import qualified Term;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Container_Setup;
import qualified List;
import qualified Arith;
import qualified Set;

data Ta_rule a b = TA_rule b [a] a;

equal_ta_rule :: forall a b. (Eq a, Eq b) => Ta_rule a b -> Ta_rule a b -> Bool;
equal_ta_rule (TA_rule x1 x2 x3) (TA_rule y1 y2 y3) =
  x1 == y1 && x2 == y2 && x3 == y3;

instance (Eq a, Eq b) => Eq (Ta_rule a b) where {
  a == b = equal_ta_rule a b;
};

data Ta_ext a b c =
  Ta_ext (Set.Set a) (Set.Set (Ta_rule a b)) (Set.Set (a, a)) c;

r_sym :: forall a b. Ta_rule a b -> (b, Arith.Nat);
r_sym (TA_rule f qs q) = (f, List.size_list qs);

r_lhs_states :: forall a b. Ta_rule a b -> [a];
r_lhs_states (TA_rule x1 x2 x3) = x2;

r_rhs :: forall a b. Ta_rule a b -> a;
r_rhs (TA_rule x1 x2 x3) = x3;

ta_rules :: forall a b c. Ta_ext a b c -> Set.Set (Ta_rule a b);
ta_rules (Ta_ext ta_final ta_rules ta_eps more) = ta_rules;

ta_eps :: forall a b c. Ta_ext a b c -> Set.Set (a, a);
ta_eps (Ta_ext ta_final ta_rules ta_eps more) = ta_eps;

ta_res ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Collection_Order.Ccompare b,
      Eq b) => Ta_ext a b () -> Term.Term b a -> Set.Set a;
ta_res ta (Term.Var q) =
  let {
    a = Set.insert q Set.bot_set;
  } in Set.sup_set a (Abstract_Rewriting_Impl.compute_trancl a (ta_eps ta));
ta_res ta (Term.Fun f ts) =
  let {
    qs = map (ta_res ta) ts;
    g = (f, List.size_list ts);
    a = Set.image r_rhs
          (Set.filtera
            (\ r ->
              r_sym r == g &&
                all (\ qq -> Set.member (snd qq) (fst qq))
                  (zip qs (r_lhs_states r)))
            (ta_rules ta));
  } in Set.sup_set a (Abstract_Rewriting_Impl.compute_trancl a (ta_eps ta));

ta_final :: forall a b c. Ta_ext a b c -> Set.Set a;
ta_final (Ta_ext ta_final ta_rules ta_eps more) = ta_final;

r_states ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Set_Impl.Set_impl a) => Ta_rule a b -> Set.Set a;
r_states =
  (\ ta_rule -> Set.insert (r_rhs ta_rule) (List.set (r_lhs_states ta_rule)));

ta_states ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Eq b) => Ta_ext a b () -> Set.Set a;
ta_states ta =
  Set.sup_set
    (Set.sup_set (Complete_Lattices.sup_set (Set.image r_states (ta_rules ta)))
      (Complete_Lattices.sup_set
        (Set.image (\ (q, qa) -> Set.insert q (Set.insert qa Set.bot_set))
          (ta_eps ta))))
    (ta_final ta);

ta_syms ::
  forall a b.
    (Collection_Order.Ccompare a, Eq a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => Ta_ext a b () -> Set.Set (b, Arith.Nat);
ta_syms ta = Set.image r_sym (ta_rules ta);

prod_ta ::
  forall a b c.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b, Cardinality.Finite_UNIV c, Collection_Enum.Cenum c,
      Collection_Eq.Ceq c, Collection_Order.Cproper_interval c, Eq c,
      Set_Impl.Set_impl c) => Ta_ext a b () ->
                                Ta_ext c b () ->
                                  Set.Set (a, c) -> Ta_ext (a, c) b ();
prod_ta tA1 tA2 f =
  Ta_ext f
    (Set.image
      (\ (TA_rule fa qs1 q1, TA_rule _ qs2 q2) ->
        TA_rule fa (zip qs1 qs2) (q1, q2))
      (Complete_Lattices.sup_set
        (Set.image
          (\ fa ->
            Product_Type.product
              (Set.filtera (\ r -> r_sym r == fa) (ta_rules tA1))
              (Set.filtera (\ r -> r_sym r == fa) (ta_rules tA2)))
          (ta_syms tA1))))
    (Set.sup_set
      (Set.image (\ (a, b) -> (case a of {
                                (q, qa) -> (\ p -> ((q, p), (qa, p)));
                              })
                                b)
        (Product_Type.product (ta_eps tA1) (ta_states tA2)))
      (Set.image (\ (p, (q, qa)) -> ((p, q), (p, qa)))
        (Product_Type.product (ta_states tA1) (ta_eps tA2))))
    ();

productive_relation ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Eq b) => Ta_ext a b () -> Set.Set (a, a);
productive_relation ta =
  Set.sup_set (Set.image (\ (a, b) -> (b, a)) (ta_eps ta))
    (Complete_Lattices.sup_set
      (Set.image
        (\ r -> Set.image (\ a -> (r_rhs r, a)) (List.set (r_lhs_states r)))
        (ta_rules ta)));

ta_productive ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Eq b) => Ta_ext a b () -> Set.Set a;
ta_productive ta =
  let {
    a = ta_final ta;
  } in Set.sup_set a
         (Abstract_Rewriting_Impl.compute_trancl a (productive_relation ta));

reduced_TA ::
  forall a b c.
    (Collection_Order.Ccompare a, Eq a, Collection_Eq.Ceq b,
      Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => a -> Ta_ext b a c -> Set.Set b -> Ta_ext b a ();
reduced_TA f ta q =
  Ta_ext Set.bot_set
    (Set.sup_set
      (Set.image
        (\ (TA_rule fa qs a) ->
          TA_rule fa (filter (\ qa -> not (Set.member qa q)) qs) a)
        (Set.filtera (\ r -> not (Set.member (r_rhs r) q)) (ta_rules ta)))
      (Set.image (\ p -> TA_rule f [] (snd p))
        (Set.filtera (\ p -> Set.member (fst p) q && not (Set.member (snd p) q))
          (ta_eps ta))))
    (Set.filtera
      (\ p -> not (Set.member (fst p) q) && not (Set.member (snd p) q))
      (ta_eps ta))
    ();

new_reach ::
  forall a b c.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Eq a,
      Set_Impl.Set_impl a, Collection_Order.Ccompare b,
      Eq b) => Ta_ext a b c -> Set.Set a;
new_reach ta =
  Set.image r_rhs (Set.filtera (\ r -> null (r_lhs_states r)) (ta_rules ta));

ta_reachable ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Collection_Order.Ccompare b, HOL.Default b,
      Eq b) => Ta_ext a b () -> Set.Set a;
ta_reachable ta =
  let {
    q = new_reach ta;
  } in (if Set.less_eq_set q Set.bot_set then Set.bot_set
         else Set.sup_set q (ta_reachable (reduced_TA HOL.defaulta ta q)));

ta_restrict ::
  forall a b c.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Collection_Order.Ccompare b,
      Eq b) => Ta_ext a b c -> Set.Set a -> Ta_ext a b ();
ta_restrict ta q =
  Ta_ext (Set.inf_set (ta_final ta) q)
    (Set.filtera (\ r -> Set.less_eq_set (r_states r) q) (ta_rules ta))
    (Set.inf_set (ta_eps ta) (Product_Type.product q q)) ();

trim_ta ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, HOL.Default b,
      Eq b) => Ta_ext a b () -> Ta_ext a b ();
trim_ta ta =
  ta_restrict (ta_restrict ta (ta_reachable ta))
    (ta_productive (ta_restrict ta (ta_reachable ta)));

ta_empty ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Collection_Order.Ccompare b, HOL.Default b,
      Eq b) => Ta_ext a b () -> Bool;
ta_empty ta =
  Set.less_eq_set (Set.inf_set (ta_reachable ta) (ta_final ta)) Set.bot_set;

ta_match ::
  forall a b c.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Collection_Order.Ccompare b, Eq b,
      Collection_Eq.Ceq c,
      Collection_Order.Ccompare c) => Ta_ext a b () ->
Set.Set a -> Term.Term b c -> Set.Set a -> Set.Set [(c, a)];
ta_match ta qsig (Term.Var x) q =
  Set.image (\ qa -> [(x, qa)])
    (Set.filtera (\ qa -> Set.member qa qsig)
      (let {
         a = q;
       } in Set.sup_set a
              (Abstract_Rewriting_Impl.compute_trancl a
                (Relation.converse (ta_eps ta)))));
ta_match ta qsig (Term.Fun f ts) q =
  let {
    n = List.size_list ts;
    rls = Set.filtera
            (\ rule ->
              r_sym rule == (f, n) &&
                Set.bex
                  (let {
                     a = Set.insert (r_rhs rule) Set.bot_set;
                   } in Set.sup_set a
                          (Abstract_Rewriting_Impl.compute_trancl a
                            (ta_eps ta)))
                  (\ qa -> Set.member qa q))
            (ta_rules ta);
  } in Complete_Lattices.sup_set
         (Set.image
           (\ (TA_rule _ qs _) ->
             Set.image concat
               (List.listset
                 (map (\ (tsi, qsi) ->
                        ta_match ta qsig tsi (Set.insert qsi Set.bot_set))
                   (zip ts qs))))
           rls);

ta_matcha ::
  forall a b c.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Collection_Order.Ccompare b, Eq b,
      Collection_Eq.Ceq c,
      Collection_Order.Ccompare c) => Ta_ext a b () ->
Set.Set a -> Term.Term b c -> Set.Set [(c, a)];
ta_matcha ta q t = ta_match ta q t q;

adapt_vars :: forall a b c. Term.Term a b -> Term.Term a c;
adapt_vars (Term.Fun f ts) = Term.Fun f (map adapt_vars ts);

ta_member ::
  forall a b c.
    (Collection_Order.Ccompare a, Eq a, Collection_Enum.Cenum c,
      Collection_Eq.Ceq c, Collection_Order.Ccompare c, Eq c,
      Set_Impl.Set_impl c) => Term.Term a b -> Ta_ext c a () -> Bool;
ta_member t ta =
  Term.ground t &&
    not (Set.less_eq_set (Set.inf_set (ta_final ta) (ta_res ta (adapt_vars t)))
          Set.bot_set);

coherent_rule ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b,
      Eq b) => Set.Set (a, a) ->
                 Set.Set (Ta_rule a b) -> Ta_rule a b -> Set.Set (a, Maybe a);
coherent_rule rel rules (TA_rule f qs q) =
  List.foldr
    (Set.sup_set .
      (\ i ->
        let {
          qi = List.nth qs i;
          qi_s = Set.image snd (Set.filtera (\ qq -> fst qq == qi) rel);
          a = Complete_Lattices.sup_set
                (Set.image
                  (\ qia ->
                    let {
                      qsa = List.list_update qs i qia;
                      rls = Set.filtera
                              (\ (TA_rule g qsaa _) -> g == f && qsaa == qsa)
                              rules;
                    } in (if Set.less_eq_set rls
                               (Set_Impl.set_empty
                                 (Phantom_Type.of_phantom
                                   Container_Setup.set_impl_ta_rule))
                           then Set.insert Nothing Set.bot_set
                           else Set.image (Just . r_rhs) rls))
                  qi_s);
        } in Set.image (\ aa -> (q, aa)) a))
    (List.upt Arith.zero_nat (List.size_list qs)) Set.bot_set;

new_states ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b,
      Eq b) => Ta_ext a b () -> Set.Set (a, a) -> Set.Set (a, Maybe a);
new_states ta rel =
  let {
    rules = ta_rules ta;
  } in Complete_Lattices.sup_set (Set.image (coherent_rule rel rules) rules);

ta_rhs_states ::
  forall a b.
    (Collection_Enum.Cenum a, Collection_Eq.Ceq a, Collection_Order.Ccompare a,
      Eq a, Set_Impl.Set_impl a, Collection_Order.Ccompare b,
      Eq b) => Ta_ext a b () -> Set.Set a;
ta_rhs_states ta =
  let {
    a = Set.image r_rhs (ta_rules ta);
  } in Set.sup_set a (Abstract_Rewriting_Impl.compute_trancl a (ta_eps ta));

initial_rel ::
  forall a b c.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Set_Impl.Set_impl c) => Ta_ext a b () ->
                                Set.Set (Term.Term b c, Term.Term b c) ->
                                  Set.Set (a, Set.Set a);
initial_rel ta r =
  let {
    rhs = ta_rhs_states ta;
    match = ta_matcha ta rhs;
    analyze_rule =
      (\ (l, ra) ->
        let {
          _ = Term.vars_term l;
        } in Complete_Lattices.sup_set
               (Set.image
                 (\ sigma ->
                   let {
                     qr = ta_res ta
                            (Term.map_term (\ x -> x) (Util.fun_of sigma) ra);
                   } in Set.image (\ q -> (q, qr))
                          (ta_res ta
                            (Term.map_term (\ x -> x) (Util.fun_of sigma) l)))
                 (match l)));
  } in Complete_Lattices.sup_set (Set.image analyze_rule r);

intersect_ta ::
  forall a b c.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b, Cardinality.Finite_UNIV c, Collection_Enum.Cenum c,
      Collection_Eq.Ceq c, Collection_Order.Cproper_interval c, Eq c,
      Set_Impl.Set_impl c) => Ta_ext a b () ->
                                Ta_ext c b () -> Ta_ext (a, c) b ();
intersect_ta tA1 tA2 =
  prod_ta tA1 tA2 (Product_Type.product (ta_final tA1) (ta_final tA2));

r_root :: forall a b. Ta_rule a b -> b;
r_root (TA_rule x1 x2 x3) = x1;

initial_relation ::
  forall a b c.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Set_Impl.Set_impl c) => Ta_ext a b () ->
                                Set.Set (Term.Term b c, Term.Term b c) ->
                                  Maybe (Set.Set (a, a));
initial_relation ta r =
  let {
    q_qs = initial_rel ta r;
  } in (if Set.member Set.bot_set (Set.image snd q_qs) then Nothing
         else Just (Complete_Lattices.sup_set
                     (Set.image (\ (q, a) -> Set.image (\ aa -> (q, aa)) a)
                       q_qs)));

decide_coherent_compatible_main ::
  forall a b c.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Set_Impl.Set_impl c) => Ta_ext a b () ->
                                Set.Set (Term.Term b c, Term.Term b c) ->
                                  (Maybe (Set.Set (a, a)) ->
                                    Maybe (Set.Set (a, a))) ->
                                    Bool;
decide_coherent_compatible_main ta r normalizer =
  (case normalizer (initial_relation ta r) of {
    Nothing -> False;
    Just rel ->
      Set.less_eq_set (Relation.image rel (ta_final ta)) (ta_final ta);
  });

normalize_main ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b,
      Eq b) => Ta_ext a b () ->
                 Set.Set (a, a) -> Set.Set (a, a) -> Maybe (Set.Set (a, a));
normalize_main ta rel accu =
  let {
    new = new_states ta rel;
  } in (if Set.member Nothing (Set.image snd new) then Nothing
         else let {
                new_rel = Set.image (\ (x, y) -> (x, Option.the y)) new;
                new_accu = Set.sup_set accu rel;
                todo = Set.minus_set new_rel new_accu;
              } in (if Set.less_eq_set todo Set.bot_set then Just new_accu
                     else normalize_main ta todo new_accu));

normalize ::
  forall a b.
    (Cardinality.Finite_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b,
      Eq b) => Ta_ext a b () ->
                 Maybe (Set.Set (a, a)) -> Maybe (Set.Set (a, a));
normalize ta Nothing = Nothing;
normalize ta (Just rel) = normalize_main ta rel Set.bot_set;

decide_coherent_compatible ::
  forall a b c.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b, Collection_Eq.Ceq c,
      Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Set_Impl.Set_impl c) => Ta_ext a b () ->
                                Set.Set (Term.Term b c, Term.Term b c) -> Bool;
decide_coherent_compatible ta r =
  decide_coherent_compatible_main ta r (normalize ta);

closed_under_rewriting ::
  forall a b c.
    (Cardinality.Card_UNIV a, Collection_Enum.Cenum a, Collection_Eq.Ceq a,
      Collection_Order.Cproper_interval a, Eq a, Set_Impl.Set_impl a,
      Collection_Order.Ccompare b, Compare.Compare b, HOL.Default b, Eq b,
      Collection_Eq.Ceq c, Collection_Order.Ccompare c, Compare.Compare c, Eq c,
      Set_Impl.Set_impl c) => Ta_ext a b () ->
                                Set.Set (Term.Term b c, Term.Term b c) -> Bool;
closed_under_rewriting ta r = decide_coherent_compatible (trim_ta ta) r;

}
