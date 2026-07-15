{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Semantic_Labeling_Carrier(ArithFun(..), Sl_inter(..), Sl_variant(..), rl_slm,
                             qmodel_cge, qsli_to_sl, sli_to_slm, semlab_fin_tt,
                             semlab_fin_proc)
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
import qualified Quasi_Order;
import qualified Map;
import qualified Show_Instances;
import qualified Showa;
import qualified Dependency_Pair_Problem_Spec;
import qualified Missing_List;
import qualified Termination_Problem_Spec;
import qualified Term_Rewriting;
import qualified Compare;
import qualified Mapping;
import qualified Labelings_Impl;
import qualified Pointwise_Extension;
import qualified Shows_Literal;
import qualified Check_Monad;
import qualified Error_Monad;
import qualified HOL;
import qualified Semantic_Labeling_Impl;
import qualified Sum_Type;
import qualified Labelings;
import qualified Arith;

data ArithFun = Arg Arith.Nat | Const Arith.Nat | Sum [ArithFun]
  | Max [ArithFun] | Min [ArithFun] | Prod [ArithFun]
  | IfEqual ArithFun ArithFun ArithFun ArithFun;

data Sl_inter a = SL_Inter Arith.Nat [((a, Arith.Nat), ArithFun)];

data Sl_variant a b = Rootlab (Maybe (a, Arith.Nat)) | Finitelab (Sl_inter a)
  | QuasiFinitelab (Sl_inter a) b;

rl_slm ::
  forall a b.
    (Eq a,
      Eq b) => Maybe (Labelings.Lab a b, Arith.Nat) ->
                 [(Labelings.Lab a b, Arith.Nat)] ->
                   [(Labelings.Lab a b, Arith.Nat)] ->
                     Sum_Type.Sum (String -> String)
                       (Semantic_Labeling_Impl.Slm_ops_ext (Labelings.Lab a b)
                         (Labelings.Lab a b)
                         (Sum_Type.Sum b [Labelings.Lab a b]) ());
rl_slm delt_opt pre_fs g =
  let {
    fs = (if Arith.is_none delt_opt then pre_fs
           else filter (\ f -> not (f == Arith.the delt_opt)) pre_fs);
  } in Error_Monad.bind
         (Check_Monad.check (not (null fs))
           (Shows_Literal.showsl_lit
             "root-labeling requires at least one function symbol in the signature\n"))
         (\ _ ->
           let {
             f = fst (Arith.hda fs);
           } in Sum_Type.Inr
                  (Semantic_Labeling_Impl.Slm_ops_ext (\ _ -> Sum_Type.Inr)
                    (\ ga cs ->
                      (if Arith.membera fs (ga, Arith.size_list cs) then ga
                        else f))
                    (map fst fs) f
                    (if Arith.is_none delt_opt then (\ _ -> Sum_Type.Inr)
                      else (\ _ gs ->
                             Sum_Type.Inr
                               (Arith.replicate (Arith.size_list gs)
                                 (fst (Arith.the delt_opt)))))
                    ()));

qmodel_L ::
  forall a b c d.
    (Eq a,
      Eq b) => [(Labelings.Lab a b, Arith.Nat)] ->
                 Labelings.Lab a b -> [c] -> Sum_Type.Sum [c] d;
qmodel_L sig =
  (\ f cs ->
    (if Arith.membera sig (f, Arith.size_list cs) then Sum_Type.Inl cs
      else Sum_Type.Inl []));

enum_vectors_nat :: forall a. [a] -> Arith.Nat -> [[a]];
enum_vectors_nat c n =
  (if Arith.equal_nat n Arith.zero_nat then [[]]
    else let {
           a = enum_vectors_nat c (Arith.minus_nat n Arith.one_nat);
         } in concatMap (\ vec -> map (\ ca -> ca : vec) c) a);

qmodel_LS_gen ::
  forall a b c.
    (Eq a) => [(a, Arith.Nat)] -> [b] -> a -> Arith.Nat -> [Sum_Type.Sum [b] c];
qmodel_LS_gen sig ls =
  (\ f n ->
    (if Arith.membera sig (f, n) then map Sum_Type.Inl (enum_vectors_nat ls n)
      else [Sum_Type.Inl []]));

qmodel_LS ::
  forall a b c.
    (Eq a, Eq b,
      Eq c) => [(a, Arith.Nat)] ->
                 [b] -> a -> Arith.Nat -> Sum_Type.Sum [b] c -> Bool;
qmodel_LS sig ls = (\ f n -> Arith.membera (qmodel_LS_gen sig ls f n));

qmodel_LSa ::
  forall a.
    Labelings.Lab a [Arith.Nat] ->
      Arith.Nat ->
        Sum_Type.Sum [Arith.Nat] [Labelings.Lab a [Arith.Nat]] -> Bool;
qmodel_LSa = (\ _ _ a -> (case a of {
                           Sum_Type.Inl _ -> True;
                           Sum_Type.Inr _ -> False;
                         }));

qmodel_cge :: Arith.Nat -> Arith.Nat -> Bool;
qmodel_cge = (\ x y -> Arith.less_eq_nat y x);

qmodel_lge ::
  forall a b c d.
    a -> b -> Sum_Type.Sum [Arith.Nat] c -> Sum_Type.Sum [Arith.Nat] d -> Bool;
qmodel_lge f n =
  (\ l r ->
    (case (l, r) of {
      (Sum_Type.Inl cs1, Sum_Type.Inl cs2) ->
        snd (Pointwise_Extension.pointwise_ext
              (\ x y -> (Arith.less_nat y x, Arith.less_eq_nat y x)) cs1 cs2);
      (Sum_Type.Inl _, Sum_Type.Inr _) -> False;
      (Sum_Type.Inr _, _) -> False;
    }));

take_default :: forall a. a -> [a] -> Arith.Nat -> a;
take_default def [] uu = def;
take_default uv (x : xs) i =
  (if Arith.equal_nat i Arith.zero_nat then x
    else take_default uv xs (Arith.minus_nat i Arith.one_nat));

eval_arithFun :: Arith.Nat -> [Arith.Nat] -> ArithFun -> Arith.Nat;
eval_arithFun c nats f = Arith.modulo_nat (eval_arithFun_unbound c nats f) c;

eval_arithFun_unbound :: Arith.Nat -> [Arith.Nat] -> ArithFun -> Arith.Nat;
eval_arithFun_unbound c nats (Arg i) = take_default Arith.zero_nat nats i;
eval_arithFun_unbound c nats (Const n) = n;
eval_arithFun_unbound c nats (Sum []) = Arith.zero_nat;
eval_arithFun_unbound c nats (Sum (f : fs)) =
  Arith.plus_nat (eval_arithFun c nats f) (eval_arithFun c nats (Sum fs));
eval_arithFun_unbound c nats (Prod []) = Arith.one_nat;
eval_arithFun_unbound c nats (Prod (f : fs)) =
  Arith.times_nat (eval_arithFun c nats f) (eval_arithFun c nats (Prod fs));
eval_arithFun_unbound c nats (Max [f]) = eval_arithFun c nats f;
eval_arithFun_unbound c nats (Max (f : v : va)) =
  Quasi_Order.max (eval_arithFun c nats f)
    (eval_arithFun c nats (Max (v : va)));
eval_arithFun_unbound c nats (Min [f]) = eval_arithFun c nats f;
eval_arithFun_unbound c nats (Min (f : v : va)) =
  Quasi_Order.min (eval_arithFun c nats f)
    (eval_arithFun c nats (Min (v : va)));
eval_arithFun_unbound c nats (IfEqual f1 f2 ft fe) =
  (if Arith.equal_nat (eval_arithFun c nats f1) (eval_arithFun c nats f2)
    then eval_arithFun c nats ft else eval_arithFun c nats fe);

qmodel_check_interpretation ::
  ArithFun -> Arith.Nat -> Arith.Nat -> Sum_Type.Sum (String -> String) ();
qmodel_check_interpretation f n c =
  let {
    ca = Arith.upt Arith.zero_nat (Arith.suc c);
    css = enum_vectors_nat ca n;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ cs ->
             Error_Monad.catch_error
               (Error_Monad.forallM
                 (\ i ->
                   Error_Monad.catch_error
                     (Error_Monad.forallM
                       (\ l ->
                         Check_Monad.check
                           (Arith.less_eq_nat (eval_arithFun (Arith.suc c) cs f)
                             (eval_arithFun (Arith.suc c)
                               (Arith.list_update cs i l) f))
                           ((Shows_Literal.showsl_lit "not monotone in " .
                              Shows_Literal.showsl_nat (Arith.suc i)) .
                             Shows_Literal.showsl_lit ". argument"))
                       (Arith.upt (Arith.nth cs i) (Arith.suc c)))
                     (\ x -> Sum_Type.Inl (snd x)))
                 (Arith.upt Arith.zero_nat n))
               (\ x -> Sum_Type.Inl (snd x)))
           css)
         (\ x -> Sum_Type.Inl (snd x));

qmodel_check_valid ::
  forall a.
    (Shows_Literal.Showl a) => Sl_inter a -> Sum_Type.Sum (String -> String) ();
qmodel_check_valid (SL_Inter c ls) =
  Error_Monad.catch_error
    (Error_Monad.forallM
      (\ (a, b) ->
        (case a of {
          (f, n) ->
            (\ g ->
              Error_Monad.catch_error (qmodel_check_interpretation g n c)
                (\ x ->
                  Sum_Type.Inl
                    (((Shows_Literal.showsl_lit
                         "problem in weak-monotonicity of interpretation of " .
                        Shows_Literal.showsl f) .
                       Shows_Literal.showsl_literal "\n") .
                      x)));
        })
          b)
      ls)
    (\ x -> Sum_Type.Inl (snd x));

get_largest_element :: forall a. Sl_inter a -> Arith.Nat;
get_largest_element (SL_Inter n uu) = n;

sl_inter_to_inter ::
  forall a. (Eq a) => Sl_inter a -> a -> [Arith.Nat] -> Arith.Nat;
sl_inter_to_inter (SL_Inter c ls) fl cs =
  (case Map.map_of ls (fl, Arith.size_list cs) of {
    Nothing -> Arith.zero_nat;
    Just a -> eval_arithFun (Arith.suc c) cs a;
  });

check_decr_present_aux_1 ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a (b, Arith.Nat),
                                    Term_Rewriting.Term a (b, Arith.Nat))] ->
                                   b -> a ->
  a -> Arith.Nat ->
         Sum_Type.Sum
           (Term_Rewriting.Term a (b, Arith.Nat),
             Term_Rewriting.Term a (b, Arith.Nat))
           ();
check_decr_present_aux_1 r v f1 f2 n =
  let {
    vs = map (\ na -> Term_Rewriting.Var (v, na)) (Arith.upt Arith.zero_nat n);
    rule = (Term_Rewriting.Fun f1 vs, Term_Rewriting.Fun f2 vs);
  } in Check_Monad.check
         (not (Arith.is_none
                (Arith.find (Term_Rewriting.instance_rule rule) r)))
         rule;

check_decr_present_aux_2 ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Term_Rewriting.Term a b,
                                    Term_Rewriting.Term a b)] ->
                                   b -> [(a, (a, Arith.Nat))] ->
  Sum_Type.Sum
    (Term_Rewriting.Term a (b, Arith.Nat), Term_Rewriting.Term a (b, Arith.Nat))
    ();
check_decr_present_aux_2 r v req =
  let {
    add_nats =
      Term_Rewriting.map_term (\ x -> x) (\ va -> (va, Arith.zero_nat));
    ra = map (\ (l, ra) -> (add_nats l, add_nats ra)) r;
  } in Error_Monad.catch_error
         (Error_Monad.forallM
           (\ (f1, (a, b)) -> check_decr_present_aux_1 ra v f1 a b) req)
         (\ x -> Sum_Type.Inl (snd x));

check_decr_present ::
  forall a b.
    (Eq a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(a, Arith.Nat)] ->
                                   (a -> [Arith.Nat] -> a) ->
                                     b -> Arith.Nat ->
    [(Term_Rewriting.Term a b, Term_Rewriting.Term a b)] ->
      Sum_Type.Sum
        (Term_Rewriting.Term a (b, Arith.Nat),
          Term_Rewriting.Term a (b, Arith.Nat))
        ();
check_decr_present sig l v c r =
  let {
    ca = Arith.upt Arith.zero_nat (Arith.suc c);
    ls = (\ (f, n) ->
           concatMap
             (\ cs ->
               concatMap
                 (\ i ->
                   let {
                     ci = Arith.nth cs i;
                   } in (if Arith.less_nat ci c
                          then [(l f (Arith.list_update cs i (Arith.suc ci)),
                                  (l f cs, n))]
                          else []))
                 (Arith.upt Arith.zero_nat n))
             (enum_vectors_nat ca n));
  } in check_decr_present_aux_2 r v (concatMap ls sig);

qmodel_check_decr ::
  forall a b.
    (Eq a, Shows_Literal.Showl a, Arith.Ccompare b, Eq b,
      Mapping.Mapping_impl b) => [(Labelings.Lab a [Arith.Nat], Arith.Nat)] ->
                                   b -> Arith.Nat ->
  [(Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) b,
     Term_Rewriting.Term (Labelings.Lab a [Arith.Nat]) b)] ->
    Sum_Type.Sum (String -> String) ();
qmodel_check_decr sig v c =
  (\ lR ->
    Error_Monad.catch_error (check_decr_present sig Labelings.Lab v c lR)
      (\ x ->
        Sum_Type.Inl
          (let {
             display =
               Term_Rewriting.map_term (\ xa -> xa)
                 (\ (_, n) ->
                   (Showa.shows_prec_list Arith.zero_nat [Arith.char_0x78] .
                     Show_Instances.shows_prec_nat Arith.zero_nat n)
                     []);
           } in (Shows_Literal.showsl_lit "decreasing rule " .
                  Term_Rewriting.showsl_rule
                    (display (fst x), display (snd x))) .
                  Shows_Literal.showsl_lit " missing")));

pointwise_lgen :: [Arith.Nat] -> [[Arith.Nat]];
pointwise_lgen ns =
  Missing_List.concat_lists
    (map (\ n -> Arith.upt Arith.zero_nat (Arith.suc n)) ns);

qmodel_lgen ::
  forall a. Sum_Type.Sum [Arith.Nat] a -> [Sum_Type.Sum [Arith.Nat] a];
qmodel_lgen l = (case l of {
                  Sum_Type.Inl ns -> map Sum_Type.Inl (pointwise_lgen ns);
                  Sum_Type.Inr _ -> [];
                });

qsli_to_sl_unsafe ::
  forall a b.
    (Arith.Ccompare a, Eq a, Mapping.Mapping_impl a, Eq b,
      Shows_Literal.Showl b) => a -> [(Labelings.Lab b [Arith.Nat],
Arith.Nat)] ->
                                       [(Labelings.Lab b [Arith.Nat],
  Arith.Nat)] ->
 Sl_inter (Labelings.Lab b [Arith.Nat]) ->
   Semantic_Labeling_Impl.Sl_ops_ext (Labelings.Lab b [Arith.Nat]) Arith.Nat
     (Sum_Type.Sum [Arith.Nat] [Labelings.Lab b [Arith.Nat]]) a ();
qsli_to_sl_unsafe v f g sli =
  let {
    c = get_largest_element sli;
    ca = Arith.upt Arith.zero_nat (Arith.suc c);
  } in Semantic_Labeling_Impl.Sl_ops_ext (qmodel_L f) (qmodel_LS f ca)
         (sl_inter_to_inter sli) ca c (qmodel_check_decr f v c) (qmodel_L g)
         qmodel_LSa qmodel_lgen (qmodel_LS_gen f ca) ();

qsli_to_sl ::
  forall a b.
    (Arith.Ccompare a, Eq a, Mapping.Mapping_impl a, Eq b,
      Shows_Literal.Showl b) => a -> [(Labelings.Lab b [Arith.Nat],
Arith.Nat)] ->
                                       [(Labelings.Lab b [Arith.Nat],
  Arith.Nat)] ->
 Sl_inter (Labelings.Lab b [Arith.Nat]) ->
   Sum_Type.Sum (String -> String)
     (Semantic_Labeling_Impl.Sl_ops_ext (Labelings.Lab b [Arith.Nat]) Arith.Nat
       (Sum_Type.Sum [Arith.Nat] [Labelings.Lab b [Arith.Nat]]) a ());
qsli_to_sl v f g sli =
  Error_Monad.bind (qmodel_check_valid sli)
    (\ _ -> Sum_Type.Inr (qsli_to_sl_unsafe v f g sli));

sli_to_slm ::
  forall a.
    (Eq a) => Sl_inter (Labelings.Lab a [Arith.Nat]) ->
                Semantic_Labeling_Impl.Slm_ops_ext (Labelings.Lab a [Arith.Nat])
                  Arith.Nat
                  (Sum_Type.Sum [Arith.Nat] [Labelings.Lab a [Arith.Nat]]) ();
sli_to_slm sli =
  let {
    c = get_largest_element sli;
  } in Semantic_Labeling_Impl.Slm_ops_ext (\ _ -> Sum_Type.Inl)
         (sl_inter_to_inter sli) (Arith.upt Arith.zero_nat (Arith.suc c)) c
         (\ _ -> Sum_Type.Inl) ();

semlab_fin_tt ::
  forall a b c.
    (Compare.Compare b, Eq b, Shows_Literal.Showl b, Arith.Ccompare c,
      Compare.Compare c, Eq c, Mapping.Mapping_impl c,
      Shows_Literal.Showl c) => Termination_Problem_Spec.Tp_ops_ext a
                                  (Labelings.Lab b [Arith.Nat]) c () ->
                                  Sl_variant (Labelings.Lab b [Arith.Nat]) c ->
                                    [Term_Rewriting.Term
                                       (Labelings.Lab b [Arith.Nat]) c] ->
                                      [(Term_Rewriting.Term
  (Labelings.Lab b [Arith.Nat]) c,
 Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) c)] ->
a -> Sum_Type.Sum (String -> String) a;
semlab_fin_tt j (Rootlab uu) =
  Semantic_Labeling_Impl.sem_lab_fin_tt
    (Semantic_Labeling_Impl.model_splitter Labelings.label_decomp)
    Labelings.label Labelings.label_decomp Labelings.equal_lab j
    (Semantic_Labeling_Impl.slm_gen_to_sl_gen (rl_slm Nothing));
semlab_fin_tt j (Finitelab sli) =
  Semantic_Labeling_Impl.sem_lab_fin_tt
    (Semantic_Labeling_Impl.model_splitter Labelings.label_decomp)
    Labelings.label Labelings.label_decomp Arith.equal_nat j
    (Semantic_Labeling_Impl.slm_gen_to_sl_gen
      (\ _ _ -> Sum_Type.Inr (sli_to_slm sli)));
semlab_fin_tt j (QuasiFinitelab sli v) =
  Semantic_Labeling_Impl.sem_lab_fin_tt
    (Semantic_Labeling_Impl.quasi_splitter Labelings.label_decomp)
    Labelings.label Labelings.label_decomp qmodel_cge j
    (\ f g -> qsli_to_sl v f g sli);

semlab_fin_proc ::
  forall a b c.
    (Compare.Compare b, Eq b, Shows_Literal.Showl b, Arith.Ceq c,
      Arith.Ccompare c, Compare.Compare c, Eq c, Mapping.Mapping_impl c,
      Arith.Set_impl c,
      Shows_Literal.Showl c) => Dependency_Pair_Problem_Spec.Dpp_ops_ext a
                                  (Labelings.Lab b [Arith.Nat]) c () ->
                                  Sl_variant (Labelings.Lab b [Arith.Nat]) c ->
                                    [(Term_Rewriting.Term
(Labelings.Lab b [Arith.Nat]) c,
                                       Term_Rewriting.Term
 (Labelings.Lab b [Arith.Nat]) c)] ->
                                      [Term_Rewriting.Term
 (Labelings.Lab b [Arith.Nat]) c] ->
[(Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) c,
   Term_Rewriting.Term (Labelings.Lab b [Arith.Nat]) c)] ->
  a -> Sum_Type.Sum (String -> String) a;
semlab_fin_proc j (Rootlab Nothing) =
  Semantic_Labeling_Impl.sem_lab_fin_proc Labelings.label Labelings.label_decomp
    j (Semantic_Labeling_Impl.slm_gen_to_sl_gen (rl_slm Nothing));
semlab_fin_proc j (Rootlab (Just d)) =
  Semantic_Labeling_Impl.sem_lab_fin_root_proc Labelings.label
    Labelings.label_decomp j
    (Semantic_Labeling_Impl.slm_gen_to_sl_gen (rl_slm (Just d)));
semlab_fin_proc j (Finitelab sli) =
  Semantic_Labeling_Impl.sem_lab_fin_proc Labelings.label Labelings.label_decomp
    j (Semantic_Labeling_Impl.slm_gen_to_sl_gen
        (\ _ _ -> Sum_Type.Inr (sli_to_slm sli)));
semlab_fin_proc j (QuasiFinitelab sli v) =
  Semantic_Labeling_Impl.sem_lab_fin_quasi_root_proc Labelings.label
    Labelings.label_decomp qmodel_cge qmodel_lge j
    (\ f g -> qsli_to_sl v f g sli);

}
