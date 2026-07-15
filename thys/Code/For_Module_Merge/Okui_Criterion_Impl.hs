{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Okui_Criterion_Impl(Ll_rule, check_sim_cps_closed, check_sim_cps_closed_comm)
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
import qualified Rewrite_Relations_Impl;
import qualified Trs;
import qualified Check_Joins;
import qualified Compare;
import qualified Term_Impl;
import qualified Check_Monad;
import qualified Okui_Criterion;
import qualified Mgu_List;
import qualified Subterm_and_Context;
import qualified Position;
import qualified Sublist;
import qualified Error_Monad;
import qualified Trs_Impl;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Missing_List;
import qualified Mgu_generic;
import qualified HOL;
import qualified RenamingN;
import qualified Fresh;
import qualified Term_More;
import qualified Product_Type;
import qualified Option;
import qualified Matching;
import qualified List;
import qualified Mapping_Impl;
import qualified Collection_Order;
import qualified Sum_Type;
import qualified Shows_Literal;
import qualified Term;
import qualified Arith;

newtype Ll_rule b a = LL_Rule
  (Term.Term b a, (Term.Term b a, ([[Arith.Nat]], [a])));

ll_rule_tuple ::
  forall b a.
    Ll_rule b a -> (Term.Term b a, (Term.Term b a, ([[Arith.Nat]], [a])));
ll_rule_tuple (LL_Rule x) = x;

equal_ll_rule :: forall a b. (Eq a, Eq b) => Ll_rule a b -> Ll_rule a b -> Bool;
equal_ll_rule xa xc =
  (case ll_rule_tuple xa of {
    (l, (r, _)) ->
      (\ (la, (ra, _)) -> Term.equal_term l la && Term.equal_term r ra);
  })
    (ll_rule_tuple xc);

instance (Eq a, Eq b) => Eq (Ll_rule a b) where {
  a == b = equal_ll_rule a b;
};

newtype
  X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
    a b
  = Abs_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
  (Sum_Type.Sum String (Term.Term b a, (Term.Term b a, ([[Arith.Nat]], [a]))));

lhs :: forall a b. Ll_rule a b -> Term.Term a b;
lhs xa = fst (ll_rule_tuple xa);

rhs :: forall a b. Ll_rule a b -> Term.Term a b;
rhs xa = fst (snd (ll_rule_tuple xa));

var_rule_list :: forall a b. Ll_rule a b -> [b];
var_rule_list xa = snd (snd (snd (ll_rule_tuple xa)));

to_Pterm ::
  forall a b. Term.Term a b -> Term.Term (Sum_Type.Sum (Ll_rule a b) a) b;
to_Pterm (Term.Var x) = Term.Var x;
to_Pterm (Term.Fun f ts) = Term.Fun (Sum_Type.Inr f) (map to_Pterm ts);

join ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => Term.Term (Sum_Type.Sum (Ll_rule a b) a)
b ->
Term.Term (Sum_Type.Sum (Ll_rule a b) a) b ->
  Maybe (Term.Term (Sum_Type.Sum (Ll_rule a b) a) b);
join (Term.Var x) (Term.Var y) =
  (if x == y then Just (Term.Var x) else Nothing);
join (Term.Fun (Sum_Type.Inr f) asa) (Term.Fun (Sum_Type.Inr g) bs) =
  (if f == g && Arith.equal_nat (List.size_list asa) (List.size_list bs)
    then (case List.those (map (\ (a, b) -> join a b) (zip asa bs)) of {
           Nothing -> Nothing;
           Just xs -> Just (Term.Fun (Sum_Type.Inr f) xs);
         })
    else Nothing);
join (Term.Fun (Sum_Type.Inl alpha) asa) (Term.Fun (Sum_Type.Inl beta) bs) =
  (if equal_ll_rule alpha beta
    then (case List.those (map (\ (a, b) -> join a b) (zip asa bs)) of {
           Nothing -> Nothing;
           Just xs -> Just (Term.Fun (Sum_Type.Inl alpha) xs);
         })
    else Nothing);
join (Term.Fun (Sum_Type.Inl alpha) asa) (Term.Var v) =
  (case Matching.match (Term.Var v) (to_Pterm (lhs alpha)) of {
    Nothing -> Nothing;
    Just sigma ->
      (case List.those
              (map (\ (a, b) -> join a b)
                (zip asa (map sigma (var_rule_list alpha))))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term.Fun (Sum_Type.Inl alpha) asa) (Term.Fun (Sum_Type.Inr vb) va) =
  (case Matching.match (Term.Fun (Sum_Type.Inr vb) va) (to_Pterm (lhs alpha)) of
    {
    Nothing -> Nothing;
    Just sigma ->
      (case List.those
              (map (\ (a, b) -> join a b)
                (zip asa (map sigma (var_rule_list alpha))))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term.Var v) (Term.Fun (Sum_Type.Inl alpha) bs) =
  (case Matching.match (Term.Var v) (to_Pterm (lhs alpha)) of {
    Nothing -> Nothing;
    Just sigma ->
      (case List.those
              (map (\ (a, b) -> join a b)
                (zip (map sigma (var_rule_list alpha)) bs))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term.Fun (Sum_Type.Inr vb) va) (Term.Fun (Sum_Type.Inl alpha) bs) =
  (case Matching.match (Term.Fun (Sum_Type.Inr vb) va) (to_Pterm (lhs alpha)) of
    {
    Nothing -> Nothing;
    Just sigma ->
      (case List.those
              (map (\ (a, b) -> join a b)
                (zip (map sigma (var_rule_list alpha)) bs))
        of {
        Nothing -> Nothing;
        Just xs -> Just (Term.Fun (Sum_Type.Inl alpha) xs);
      });
  });
join (Term.Fun (Sum_Type.Inr vc) va) (Term.Var vb) = Nothing;
join (Term.Var vb) (Term.Fun (Sum_Type.Inr vc) va) = Nothing;

target ::
  forall a b.
    (Eq b) => Term.Term (Sum_Type.Sum (Ll_rule a b) a) b -> Term.Term a b;
target (Term.Var x) = Term.Var x;
target (Term.Fun (Sum_Type.Inr f) asa) = Term.Fun f (map target asa);
target (Term.Fun (Sum_Type.Inl alpha) asa) =
  Term.eval_term Term.Fun (rhs alpha)
    (Term_More.mk_subst Term.Var (zip (var_rule_list alpha) (map target asa)));

join_opt ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => Term.Term (Sum_Type.Sum (Ll_rule a b) a)
b ->
Maybe (Term.Term (Sum_Type.Sum (Ll_rule a b) a) b) ->
  Maybe (Term.Term (Sum_Type.Sum (Ll_rule a b) a) b);
join_opt a (Just b) = join a b;
join_opt uu Nothing = Nothing;

join_list ::
  forall a b.
    (Eq a, Collection_Order.Ccompare b, Eq b,
      Mapping_Impl.Mapping_impl b) => [Term.Term (Sum_Type.Sum (Ll_rule a b) a)
 b] ->
Maybe (Term.Term (Sum_Type.Sum (Ll_rule a b) a) b);
join_list [] = Nothing;
join_list [a] = Just a;
join_list (a : v : va) = join_opt a (join_list (v : va));

var_poss_list :: forall a b. Ll_rule a b -> [[Arith.Nat]];
var_poss_list xa = fst (snd (snd (ll_rule_tuple xa)));

in_funposs :: forall a b. [Arith.Nat] -> Term.Term a b -> Bool;
in_funposs (i : p) (Term.Fun f ts) =
  Arith.less_nat i (List.size_list ts) && in_funposs p (List.nth ts i);
in_funposs [] (Term.Fun uu uv) = True;
in_funposs p (Term.Var uw) = False;

compute_rp ::
  forall a b.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   Term.Term b a -> [[(Ll_rule b a, [Arith.Nat])]];
compute_rp ren r (Term.Var x) = [[]];
compute_rp ren r (Term.Fun f ts) =
  (map concat . Missing_List.concat_lists)
    (map (\ (x, y) ->
           map (map (Product_Type.map_prod id (\ a -> x : a)))
             (compute_rp ren r y))
      (zip (List.upt Arith.zero_nat (List.size_list ts)) ts)) ++
    concatMap
      (\ rule ->
        let {
          ps = filter (\ y -> not (null y)) (var_poss_list rule);
          rec = map (\ p ->
                      (if in_funposs p (Term.Fun f ts)
                        then map (map (Product_Type.map_prod id
(\ a -> p ++ a)))
                               (compute_rp ren r
                                 (Term_More.subt_at (Term.Fun f ts) p))
                        else [[]]))
                  ps;
        } in map (\ a -> (rule, []) : a)
               ((map concat . Missing_List.concat_lists) rec))
      (filter
        (\ rule ->
          not (Option.is_none
                (Mgu_generic.mgu_vd_list ren [(Term.Fun f ts, lhs rule)])))
        r);

rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                  a b ->
                                  Sum_Type.Sum String
                                    (Term.Term b a,
                                      (Term.Term b a, ([[Arith.Nat]], [a])));
rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
  (Abs_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
    x)
  = x;

sel21 ::
  forall b a.
    (Shows_Literal.Showl b,
      Shows_Literal.Showl a) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                  b a ->
                                  Ll_rule a b;
sel21 xa =
  LL_Rule
    (case rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
            xa
      of {
      Sum_Type.Inl _ -> ll_rule_tuple (error "undefined");
      Sum_Type.Inr x2 -> x2;
    });

sel11 ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                  a b ->
                                  String;
sel11 xa =
  (case rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
          xa
    of {
    Sum_Type.Inl x1 -> x1;
  });

dis1 ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                  a b ->
                                  Bool;
dis1 xa =
  (case rep_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
          xa
    of {
    Sum_Type.Inl _ -> True;
    Sum_Type.Inr _ -> False;
  });

rep_isom ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                  a b ->
                                  Sum_Type.Sum String (Ll_rule b a);
rep_isom x =
  (if dis1 x then Sum_Type.Inl (sel11 x) else Sum_Type.Inr (sel21 x));

to_ll_rule_intern ::
  forall a b c.
    (Collection_Eq.Ceq b, Collection_Order.Ccompare b, Eq b,
      Set_Impl.Set_impl b) => (Term.Term a b, Term.Term c b) ->
                                Sum_Type.Sum String
                                  (Term.Term a b,
                                    (Term.Term c b, ([[Arith.Nat]], [b])));
to_ll_rule_intern rule =
  let {
    xs = Term_More.vars_term_list (fst rule);
  } in Error_Monad.bind
         (Check_Monad.check (not (Term.is_Var (fst rule)))
           "variable left-hand side in rule")
         (\ _ ->
           Error_Monad.bind
             (Check_Monad.check (Term_More.linear_term (fst rule))
               "left-hand side is not linear ")
             (\ _ ->
               Error_Monad.bind
                 (Error_Monad.catch_error
                   (Check_Monad.check_subseteq
                     (Term_Impl.insert_vars_term (snd rule) []) xs)
                   (\ _ -> Sum_Type.Inl "free variable in right-hand side"))
                 (\ _ ->
                   Sum_Type.Inr
                     (fst rule,
                       (snd rule, (Term_Impl.var_poss_list (fst rule), xs))))));

to_ll_rule_lift_aux ::
  forall a b.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => (Term.Term a b, Term.Term a b) ->
                                  X_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
                                    b a;
to_ll_rule_lift_aux xa =
  Abs_x_showl_x_x_v_x_showl_x_x_f_ll_rule_literal_sum_x_x_x_showl_x_x_v_list_nat_list_list_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_x_showl_x_x_v_x_showl_x_x_f_term_prod_literal_sum
    (to_ll_rule_intern xa);

to_ll_rule_lift ::
  forall a b.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => (Term.Term a b, Term.Term a b) ->
                                  Sum_Type.Sum String (Ll_rule a b);
to_ll_rule_lift x = rep_isom (to_ll_rule_lift_aux x);

to_ll_rule ::
  forall a b.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => (Term.Term a b, Term.Term a b) ->
                                  Sum_Type.Sum (String -> String) (Ll_rule a b);
to_ll_rule rule =
  Error_Monad.catch_error (to_ll_rule_lift rule)
    (\ x ->
      Sum_Type.Inl
        (((Shows_Literal.showsl_lit "rule " . Trs_Impl.showsl_rule rule) .
           Shows_Literal.showsl_lit
             " is not a well-formed left-linear rule\n") .
          Shows_Literal.showsl_lit x));

sim_cp_non_root_of ::
  forall a b.
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 Ll_rule b a ->
                   [Arith.Nat] ->
                     Ll_rule b a ->
                       [(Ll_rule b a, [Arith.Nat])] ->
                         [(Term.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                            Term.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_non_root_of ren alpha q beta rdpA =
  let {
    rdp_A = (alpha, []) : rdpA;
    renamed_lhs_alpha_s =
      Okui_Criterion.rename_list ren (map (\ (alphaa, _) -> lhs alphaa) rdp_A);
    l = Subterm_and_Context.intp_actxt Term.Fun
          (Term_More.ctxt_of_pos_term q (List.hd renamed_lhs_alpha_s))
          (Term.map_term (\ x -> x) (RenamingN.rename_single ren) (lhs beta));
  } in (case Mgu_List.mgu_list
               (map (\ (x, y) -> (x, Term_More.subt_at l y))
                 (zip renamed_lhs_alpha_s (map snd rdp_A)))
         of {
         Nothing -> [];
         Just tau ->
           let {
             asa = map (\ (a, b) ->
                         (case a of {
                           (alpha_i, pi) ->
                             (\ i ->
                               Subterm_and_Context.intp_actxt Term.Fun
                                 (Term_More.ctxt_of_pos_term pi
                                   (to_Pterm (Term.eval_term Term.Fun l tau)))
                                 (Term.Fun (Sum_Type.Inl alpha_i)
                                   (map ((to_Pterm . tau) .
  Mgu_generic.rename_many ren i)
                                     (var_rule_list alpha_i))));
                         })
                           b)
                     (zip rdp_A
                       (List.upt Arith.zero_nat (List.size_list rdp_A)));
           } in (case join_list asa of {
                  Nothing -> [];
                  Just a ->
                    let {
                      b = Subterm_and_Context.intp_actxt Term.Fun
                            (Term_More.ctxt_of_pos_term q
                              (to_Pterm (Term.eval_term Term.Fun l tau)))
                            (Term.Fun (Sum_Type.Inl beta)
                              (map ((to_Pterm . tau) .
                                     RenamingN.rename_single ren)
                                (var_rule_list beta)));
                    } in [(a, b)];
                });
       });

non_root_rdps ::
  forall a b c d.
    (Fresh.Infinite a, Eq a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   Ll_rule c d ->
                     [Arith.Nat] ->
                       Term.Term b a -> [[(Ll_rule b a, [Arith.Nat])]];
non_root_rdps ren r alpha q ll =
  map concat
    (Missing_List.concat_lists
      (map (\ p ->
             (if Sublist.prefix q p && in_funposs (Position.pos_diff p q) ll
               then map (map (Product_Type.map_prod id (\ a -> p ++ a)))
                      (compute_rp ren r
                        (Term_More.subt_at ll (Position.pos_diff p q)))
               else [[]]))
        (var_poss_list alpha)));

non_root_sim_cps ::
  forall a b.
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   Ll_rule b a ->
                     [Arith.Nat] ->
                       Ll_rule b a ->
                         [(Term.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                            Term.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
non_root_sim_cps ren r alpha q beta =
  concatMap (sim_cp_non_root_of ren alpha q beta)
    (non_root_rdps ren r alpha q (lhs beta));

sim_cp_non_root_impl ::
  forall a b.
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] ->
                     [(Term.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_non_root_impl ren r s =
  concatMap
    (\ alpha ->
      concatMap
        (\ q ->
          concatMap (non_root_sim_cps ren r alpha q)
            (filter
              (\ beta ->
                not (Option.is_none
                      (Mgu_generic.mgu_vd_list ren
                        [(lhs beta, Term_More.subt_at (lhs alpha) q)])))
              s))
        (filter (\ y -> not (null y)) (Term_Impl.fun_poss_list (lhs alpha))))
    r;

sim_cp_root_of ::
  forall a b.
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 Ll_rule b a ->
                   [(Ll_rule b a, [Arith.Nat])] ->
                     [(Term.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_root_of ren rule rdp_A =
  let {
    l = Term.map_term (\ x -> x) (RenamingN.rename_single ren) (lhs rule);
    renamed_lhs_alpha_s =
      Okui_Criterion.rename_list ren (map (\ (alpha, _) -> lhs alpha) rdp_A);
  } in (case Mgu_List.mgu_list
               (map (\ (x, y) -> (x, Term_More.subt_at l y))
                 (zip renamed_lhs_alpha_s (map snd rdp_A)))
         of {
         Nothing -> [];
         Just tau ->
           let {
             asa = map (\ ((alpha_i, pi), y) ->
                         Subterm_and_Context.intp_actxt Term.Fun
                           (Term_More.ctxt_of_pos_term pi
                             (to_Pterm (Term.eval_term Term.Fun l tau)))
                           (Term.Fun (Sum_Type.Inl alpha_i)
                             (map ((to_Pterm . tau) .
                                    Mgu_generic.rename_many ren y)
                               (var_rule_list alpha_i))))
                     (zip rdp_A
                       (List.upt Arith.zero_nat (List.size_list rdp_A)));
           } in (case join_list asa of {
                  Nothing -> [];
                  Just a ->
                    let {
                      b = Term.Fun (Sum_Type.Inl rule)
                            (map ((to_Pterm . tau) .
                                   RenamingN.rename_single ren)
                              (var_rule_list rule));
                    } in [(a, b)];
                });
       });

sim_cp_root_impl ::
  forall a b.
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] ->
                     [(Term.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_root_impl ren r s =
  concatMap
    (\ rule ->
      concatMap (sim_cp_root_of ren rule)
        (filter (\ y -> not (null y)) (compute_rp ren r (lhs rule))))
    s;

sim_cp_impl ::
  forall a b.
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] ->
                     [(Term.Term (Sum_Type.Sum (Ll_rule b a) b) a,
                        Term.Term (Sum_Type.Sum (Ll_rule b a) b) a)];
sim_cp_impl ren r s = sim_cp_root_impl ren r s ++ sim_cp_non_root_impl ren r s;

to_ll_rules ::
  forall a b.
    (Shows_Literal.Showl a, Collection_Eq.Ceq b, Collection_Order.Ccompare b,
      Eq b, Set_Impl.Set_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  Sum_Type.Sum (String -> String) [Ll_rule a b];
to_ll_rules = Error_Monad.mapM to_ll_rule;

sim_cps_impl ::
  forall a b.
    (Collection_Order.Ccompare a, Fresh.Infinite a, Eq a,
      Mapping_Impl.Mapping_impl a,
      Eq b) => RenamingN.RenamingN a ->
                 [Ll_rule b a] ->
                   [Ll_rule b a] -> [(Term.Term b a, Term.Term b a)];
sim_cps_impl ren r s =
  map (Product_Type.map_prod target target) (sim_cp_impl ren r s);

check_sim_cps_equiv :: Bool;
check_sim_cps_equiv = False;

check_sim_cps_closed_joins ::
  forall a b.
    (Compare.Compare a, Eq a, Shows_Literal.Showl a,
      Collection_Order.Ccompare b, Compare.Compare b, Eq b,
      Mapping_Impl.Mapping_impl b,
      Shows_Literal.Showl b) => [(Term.Term a b, Term.Term a b)] ->
                                  [(Term.Term a b, Term.Term a b)] ->
                                    [(Term.Term a b, Term.Term a b)] ->
                                      Check_Joins.Cp_join_hints a b ->
Sum_Type.Sum (String -> String) ();
check_sim_cps_closed_joins r s scps (Check_Joins.CP_Auto n) =
  Error_Monad.catch_error
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ (sa, t) ->
          Check_Monad.check
            (Check_Joins.is_mstep_join r s
              (if Arith.equal_nat n Arith.zero_nat then Nothing else Just n) t
              sa)
            (((((Shows_Literal.showsl_lit "the simultaneous critical pair " .
                  Term_More.showsl_terma sa) .
                 Shows_Literal.showsl_lit " <-o- . -> ") .
                Term_More.showsl_terma t) .
               Shows_Literal.showsl_lit " is not almost closed within ") .
              (if Arith.equal_nat n Arith.zero_nat
                then Shows_Literal.showsl_lit " one multistep"
                else Shows_Literal.showsl_nat n .
                       Shows_Literal.showsl_lit " steps.")))
        scps)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ x ->
      Sum_Type.Inl
        (x . Shows_Literal.showsl_lit
               "\nhence the it could not shown that the sim.-crit pairs are closed\n"));
check_sim_cps_closed_joins r s scps (Check_Joins.CP_Sequences cps) =
  Error_Monad.bind
    (Error_Monad.catch_error
      (Error_Monad.forallM
        (\ scp ->
          Check_Monad.check
            (Term.equal_term (fst scp) (snd scp) ||
              any (\ cp ->
                    Trs.instance_rule scp
                      (Check_Joins.cp_left cp, Check_Joins.cp_right cp))
                cps)
            (Shows_Literal.showsl_lit "could not find critical pair " .
              Shows_Literal.showsl_prod scp))
        scps)
      (\ x -> Sum_Type.Inl (snd x)))
    (\ _ ->
      Error_Monad.bind
        (Error_Monad.catch_error
          (Error_Monad.forallM
            (\ scp ->
              Check_Monad.check
                (if check_sim_cps_equiv
                  then (if not (Term.equal_term (fst scp) (snd scp))
                         then any (Trs.instance_rule scp) scps else True)
                  else True)
                ((Shows_Literal.showsl_lit "pair " .
                   Shows_Literal.showsl_prod scp) .
                  Shows_Literal.showsl_lit
                    " is not a simultaneous critical pair"))
            (map (\ cp -> (Check_Joins.cp_left cp, Check_Joins.cp_right cp))
              cps))
          (\ x -> Sum_Type.Inl (snd x)))
        (\ _ ->
          Error_Monad.catch_error
            (Error_Monad.forallM
              (\ cp ->
                Error_Monad.catch_error
                  (Check_Joins.check_single_rsteps_join_sequence_gen
                    (Rewrite_Relations_Impl.is_mstep r) "" s ""
                    (Check_Joins.cp_right cp) (Check_Joins.cp_left cp)
                    (reverse (Check_Joins.cp_join cp)))
                  (\ x ->
                    Sum_Type.Inl
                      (((((Shows_Literal.showsl_lit
                             "problem with sim. crit pair " .
                            Term_More.showsl_terma (Check_Joins.cp_left cp)) .
                           Shows_Literal.showsl_lit " <-o- . -> ") .
                          Term_More.showsl_terma (Check_Joins.cp_right cp)) .
                         Shows_Literal.showsl_literal "\n") .
                        x)))
              cps)
            (\ x -> Sum_Type.Inl (snd x))));

check_sim_cps_closed ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare a,
      Fresh.Infinite a, Eq a, Mapping_Impl.Mapping_impl a, Set_Impl.Set_impl a,
      Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term.Term b a, Term.Term b a)] ->
                                    Check_Joins.Cp_join_hints b a ->
                                      Sum_Type.Sum (String -> String) ();
check_sim_cps_closed ren r infos =
  Error_Monad.catch_error
    (Error_Monad.bind (to_ll_rules r)
      (\ rules ->
        check_sim_cps_closed_joins r r (sim_cps_impl ren rules rules) infos))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem checking Okui\'s simultenous critical pair condition\n" .
          x));

check_sim_cps_closed_comm ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare a,
      Fresh.Infinite a, Eq a, Mapping_Impl.Mapping_impl a, Set_Impl.Set_impl a,
      Shows_Literal.Showl a, Compare.Compare b, Eq b,
      Shows_Literal.Showl b) => RenamingN.RenamingN a ->
                                  [(Term.Term b a, Term.Term b a)] ->
                                    [(Term.Term b a, Term.Term b a)] ->
                                      Check_Joins.Cp_join_hints b a ->
Sum_Type.Sum (String -> String) ();
check_sim_cps_closed_comm ren r s infos =
  Error_Monad.catch_error
    (Error_Monad.bind (to_ll_rules r)
      (\ rules ->
        Error_Monad.bind (to_ll_rules s)
          (\ srules ->
            check_sim_cps_closed_joins r s (sim_cps_impl ren rules srules)
              infos)))
    (\ x ->
      Sum_Type.Inl
        (Shows_Literal.showsl_lit
           "problem checking Okui\'s simultenous critical pair condition\n" .
          x));

}
