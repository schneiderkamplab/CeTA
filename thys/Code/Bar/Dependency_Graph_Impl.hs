{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Dependency_Graph_Impl(is_iedg_edge_dpp, dep_graph_proc, ac_dep_graph_proc)
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
import qualified Check_Monad;
import qualified Tcap_Dpp_Impl;
import qualified Graph;
import qualified Gtcap_Impl;
import qualified Error_Monad;
import qualified Multi_Map;
import qualified AC_Dependency_Pair_Problem_Spec;
import qualified Innermost_Usable_Rules_Impl;
import qualified Icap_Impl;
import qualified Icap;
import qualified HOL;
import qualified Dependency_Pair_Problem_Spec;
import qualified Sum_Type;
import qualified Term_Rewriting;
import qualified Mapping;
import qualified Compare;
import qualified Shows_Literal;
import qualified Arith;

graph_approx_rt_sym_main ::
  forall a b c.
    (Arith.Ccompare a,
      Eq a) => Multi_Map.Multimap (Maybe (a, Arith.Nat)) b ->
                 Term_Rewriting.Gctxt a c -> [b];
graph_approx_rt_sym_main m (Term_Rewriting.GCFun f ts) =
  Multi_Map.lookup m Nothing ++
    Multi_Map.lookup m (Just (f, Arith.size_list ts));
graph_approx_rt_sym_main m Term_Rewriting.GCHole = Multi_Map.values m;

graph_approx_rt_sym ::
  forall a b c d e f.
    (Arith.Ccompare a,
      Eq a) => Multi_Map.Multimap (Maybe (a, Arith.Nat)) b ->
                 (c, (d, (Term_Rewriting.Gctxt a e, f))) -> [b];
graph_approx_rt_sym m (uu, (uv, (ct, uw))) = graph_approx_rt_sym_main m ct;

is_iedg_edge_dpp ::
  forall a b.
    (Compare.Compare_order b, Eq b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Arith.Char] () ->
                                  a -> (Term_Rewriting.Term b [Arith.Char],
 Term_Rewriting.Term b [Arith.Char]) ->
 Term_Rewriting.Term b [Arith.Char] -> Bool;
is_iedg_edge_dpp i d =
  let {
    qnf = Dependency_Pair_Problem_Spec.is_QNF i d;
    ic = Icap_Impl.icap_impl_dpp_mv i d;
    _ = Dependency_Pair_Problem_Spec.rules i d;
    urules = Innermost_Usable_Rules_Impl.inn_usable_rules_pair i d;
  } in (\ (s, t) ->
         let {
           cst = ic [s] t;
           urls = Term_Rewriting.reverse_rules (urules (s, t));
           ica = Icap_Impl.icap_impl (Term_Rewriting.is_NF_terms []) urls;
         } in (\ u ->
                (case Icap.mgu_class cst u of {
                  Nothing -> False;
                  Just mu ->
                    qnf (Term_Rewriting.eval_term Term_Rewriting.Fun
                          (Term_Rewriting.map_term (\ x -> x)
                            (\ a -> Arith.char_0x78 : a) s)
                          mu) &&
                      qnf (Term_Rewriting.eval_term Term_Rewriting.Fun
                            (Term_Rewriting.map_term (\ x -> x)
                              (\ a -> Arith.char_0x79 : a) u)
                            mu);
                }) &&
                  let {
                    cu = ica [] u;
                  } in (case Icap.mgu_class cu t of {
                         Nothing -> False;
                         Just mu ->
                           qnf (Term_Rewriting.eval_term Term_Rewriting.Fun
                                 (Term_Rewriting.map_term (\ x -> x)
                                   (\ a -> Arith.char_0x79 : a) s)
                                 mu);
                       })));

check_dep_graph_proc ::
  forall a b c.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b,
      Eq b, Mapping.Mapping_impl b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Arith.Char] () ->
                                  a -> [(Maybe c,
  [(Term_Rewriting.Term b [Arith.Char],
     Term_Rewriting.Term b [Arith.Char])])] ->
 Sum_Type.Sum (String -> String) ();
check_dep_graph_proc i dpp dps =
  let {
    c = Tcap_Dpp_Impl.tcapRM_dpp i dpp;
    rc = Tcap_Dpp_Impl.reverse_tcapRM_dpp i dpp;
    iedg = is_iedg_edge_dpp i dpp;
    p = Dependency_Pair_Problem_Spec.pairs i dpp;
    r = Dependency_Pair_Problem_Spec.rules i dpp;
    f = Term_Rewriting.funas_trs_list r;
    gt_fun = Gtcap_Impl.mk_gt_fun r;
    rm = Dependency_Pair_Problem_Spec.rules_map i dpp;
    nlv = Dependency_Pair_Problem_Spec.rules_no_left_var i dpp;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Check_Monad.check_subseteq p (concatMap snd dps))
           (\ x ->
             Sum_Type.Inl
               ((Shows_Literal.showsl_lit "Dependency Pair " .
                  Term_Rewriting.showsl_rule x) .
                 Shows_Literal.showsl_lit " is missing in decomposition\n")))
         (\ _ ->
           Error_Monad.catch_error
             (Graph.check_graph_decomp (Shows_Literal.showsl_prod . fst)
               (Multi_Map.empty ((Term_Rewriting.root . fst) . fst))
               graph_approx_rt_sym Multi_Map.insert
               (\ (a, b) ->
                 (case a of {
                   (aa, ba) ->
                     (case aa of {
                       (_, t) ->
                         (\ (_, (ct, ict)) (ab, bb) ->
                           (case ab of {
                             (u, _) ->
                               (\ (cu, (_, _)) ->
                                 Term_Rewriting.matcha ct u &&
                                   Term_Rewriting.matcha cu t &&
                                     ict u &&
                                       not
 (Gtcap_Impl.nonreachable_gtcapRM f nlv (not (null r)) gt_fun rm t u));
                           })
                             bb);
                     })
                       ba;
                 })
                   b)
               (map (\ (real, cs) ->
                      (not (Arith.is_none real),
                        map (\ (s, t) -> ((s, t), (rc s, (c t, iedg (s, t)))))
                          cs))
                 dps))
             (\ x ->
               Sum_Type.Inl
                 ((Shows_Literal.showsl_lit
                     "our estimation (EDG*** + IEDG***) could not show that you have a valid decomposition " .
                    Shows_Literal.showsl_lit "due to the following reason\n") .
                   x)));

dep_graph_proc ::
  forall a b c.
    (Arith.Cenum b, Arith.Ceq b, Arith.Ccompare b, Compare.Compare_order b,
      Eq b, Mapping.Mapping_impl b, Arith.Set_impl b,
      Shows_Literal.Showl b) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a b
                                  [Arith.Char] () ->
                                  a -> [(Maybe c,
  [(Term_Rewriting.Term b [Arith.Char],
     Term_Rewriting.Term b [Arith.Char])])] ->
 Sum_Type.Sum (String -> String) [(c, a)];
dep_graph_proc i d dps =
  (case check_dep_graph_proc i d dps of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Arith.map_filter
          (\ x ->
            (if not (Arith.is_none (fst x))
              then Just (Arith.the (fst x),
                          Dependency_Pair_Problem_Spec.intersect_pairs i d
                            (snd x))
              else Nothing))
          dps);
  });

graph_approx_edg_rt_sym ::
  forall a b c d e.
    (Arith.Ccompare a,
      Eq a) => Multi_Map.Multimap (Maybe (a, Arith.Nat)) b ->
                 (c, (d, Term_Rewriting.Gctxt a e)) -> [b];
graph_approx_edg_rt_sym m (uu, (uv, ct)) = graph_approx_rt_sym_main m ct;

check_ac_dep_graph_proc ::
  forall a b c.
    (Arith.Ccompare b, Compare.Compare_order b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext a
                                  b [Arith.Char] () ->
                                  a -> [(Maybe c,
  [(Term_Rewriting.Term b [Arith.Char],
     Term_Rewriting.Term b [Arith.Char])])] ->
 Sum_Type.Sum (String -> String) ();
check_ac_dep_graph_proc i dpp dps =
  let {
    c = Tcap_Dpp_Impl.tcapRM_ac_dpp i dpp;
    rc = Tcap_Dpp_Impl.reverse_tcapRM_ac_dpp i dpp;
    p = AC_Dependency_Pair_Problem_Spec.pairs i dpp;
  } in Error_Monad.bind
         (Error_Monad.catch_error
           (Check_Monad.check_subseteq p (concatMap snd dps))
           (\ x ->
             Sum_Type.Inl
               (((Shows_Literal.showsl_lit "Dependency Pair " .
                   Term_Rewriting.showsl_rule x) .
                  Shows_Literal.showsl_lit " is missing in decomposition") .
                 Shows_Literal.showsl_literal "\n")))
         (\ _ ->
           Error_Monad.catch_error
             (Graph.check_graph_decomp (Shows_Literal.showsl_prod . fst)
               (Multi_Map.empty ((Term_Rewriting.root . fst) . fst))
               graph_approx_edg_rt_sym Multi_Map.insert
               (\ (a, b) ->
                 (case a of {
                   (aa, ba) ->
                     (case aa of {
                       (_, t) ->
                         (\ (_, ct) (ab, bb) ->
                           (case ab of {
                             (u, _) ->
                               (\ (cu, _) ->
                                 Term_Rewriting.matcha ct u &&
                                   Term_Rewriting.matcha cu t);
                           })
                             bb);
                     })
                       ba;
                 })
                   b)
               (map (\ (real, cs) ->
                      (not (Arith.is_none real),
                        map (\ (s, t) -> ((s, t), (rc s, c t))) cs))
                 dps))
             (\ x ->
               Sum_Type.Inl
                 (((Shows_Literal.showsl_lit
                      "our estimation (EDG***) could not show that you have a valid decomposition " .
                     Shows_Literal.showsl_lit "due to the following reason") .
                    Shows_Literal.showsl_literal "\n") .
                   x)));

ac_dep_graph_proc ::
  forall a b c.
    (Arith.Ccompare b, Compare.Compare_order b, Eq b, Mapping.Mapping_impl b,
      Shows_Literal.Showl b) => AC_Dependency_Pair_Problem_Spec.Ac_dpp_ops_ext a
                                  b [Arith.Char] () ->
                                  a -> [(Maybe c,
  [(Term_Rewriting.Term b [Arith.Char],
     Term_Rewriting.Term b [Arith.Char])])] ->
 Sum_Type.Sum (String -> String) [(c, a)];
ac_dep_graph_proc i d dps =
  (case check_ac_dep_graph_proc i d dps of {
    Sum_Type.Inl a -> Sum_Type.Inl a;
    Sum_Type.Inr _ ->
      Sum_Type.Inr
        (Arith.map_filter
          (\ x ->
            (if not (Arith.is_none (fst x))
              then Just (Arith.the (fst x),
                          AC_Dependency_Pair_Problem_Spec.intersect_pairs i d
                            (snd x))
              else Nothing))
          dps);
  });

}
