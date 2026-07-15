{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Argument_Filter(Filtered(..), comparator_filtered, Af_entry(..), Afs,
                   X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option,
                   default_af_entry, afs_of, af_term, af_rules, permutation_afs,
                   filtered_rel_impl, filtered_rel_impl_af)
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
import qualified Term_Order;
import qualified Option;
import qualified Term_Order_Impl;
import qualified Complexity;
import qualified Set_Interval;
import qualified Collection_Enum;
import qualified Check_Monad;
import qualified Map_Choice;
import qualified Compare_Order_Instances;
import qualified Compare_Instances;
import qualified Phantom_Type;
import qualified Term_More;
import qualified Error_Monad;
import qualified HOL;
import qualified Sum_Type;
import qualified List;
import qualified Trs;
import qualified Term;
import qualified Collection_Order;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Product_Type;
import qualified Set;
import qualified Arith;
import qualified Shows_Literal;
import qualified Quasi_Order;
import qualified Comparator;
import qualified Compare;
import qualified Orderings;

data Filtered a = FPair a Arith.Nat;

equal_filtered :: forall a. (Eq a) => Filtered a -> Filtered a -> Bool;
equal_filtered (FPair x1 x2) (FPair y1 y2) = x1 == y1 && Arith.equal_nat x2 y2;

instance (Eq a) => Eq (Filtered a) where {
  a == b = equal_filtered a b;
};

comparator_filtered ::
  forall a.
    (a -> a -> Comparator.Order) ->
      Filtered a -> Filtered a -> Comparator.Order;
comparator_filtered comp_f (FPair x xa) (FPair y ya) =
  (case comp_f x y of {
    Comparator.Eqa -> Comparator.comparator_of xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_filtered ::
  forall a. (Compare.Compare a) => Filtered a -> Filtered a -> Comparator.Order;
compare_filtered = comparator_filtered Compare.compare;

less_eq_filtered ::
  forall a. (Compare.Compare a) => Filtered a -> Filtered a -> Bool;
less_eq_filtered = Comparator.le_of_comp compare_filtered;

less_filtered ::
  forall a. (Compare.Compare a) => Filtered a -> Filtered a -> Bool;
less_filtered = Comparator.lt_of_comp compare_filtered;

instance (Compare.Compare a) => Orderings.Ord (Filtered a) where {
  less_eq = less_eq_filtered;
  less = less_filtered;
};

instance (Compare.Compare a) => Compare.Compare (Filtered a) where {
  compare = compare_filtered;
};

instance (Compare.Compare a) => Quasi_Order.Quasi_order (Filtered a) where {
};

instance (Compare.Compare a) => Quasi_Order.Weak_order (Filtered a) where {
};

instance (Compare.Compare a) => Orderings.Preorder (Filtered a) where {
};

instance (Compare.Compare a) => Orderings.Order (Filtered a) where {
};

instance (Compare.Compare a) => Orderings.Linorder (Filtered a) where {
};

filtered_fun :: forall a. Filtered a -> a;
filtered_fun (FPair f n) = f;

showsl_filtered ::
  forall a. (Shows_Literal.Showl a) => Filtered a -> String -> String;
showsl_filtered f = Shows_Literal.showsl (filtered_fun f);

showsl_list_filtered ::
  forall a. (Shows_Literal.Showl a) => [Filtered a] -> String -> String;
showsl_list_filtered xs = Shows_Literal.default_showsl_list showsl_filtered xs;

instance (Shows_Literal.Showl a) => Shows_Literal.Showl (Filtered a) where {
  showsl = showsl_filtered;
  showsl_list = showsl_list_filtered;
};

instance (Compare.Compare a) => Compare.Compare_order (Filtered a) where {
};

data Af_entry = Collapse Arith.Nat | AFList [Arith.Nat];

newtype Afs a = Abs_afs ((a, Arith.Nat) -> Af_entry, Set.Set (a, Arith.Nat));

newtype
  X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
    a
  = Abs_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
  (Maybe ((a, Arith.Nat) -> Af_entry, Set.Set (a, Arith.Nat)));

rep_afs ::
  forall a. Afs a -> ((a, Arith.Nat) -> Af_entry, Set.Set (a, Arith.Nat));
rep_afs (Abs_afs x) = x;

afs :: forall a. Afs a -> (a, Arith.Nat) -> Af_entry;
afs xa = fst (rep_afs xa);

afs_sym :: forall a. Afs a -> (a, Arith.Nat) -> [(Filtered a, Arith.Nat)];
afs_sym af (f, n) = (case afs af (f, n) of {
                      Collapse _ -> [];
                      AFList is -> [(FPair f n, List.size_list is)];
                    });

afs_sig :: forall a. Afs a -> [(a, Arith.Nat)] -> [(Filtered a, Arith.Nat)];
afs_sig af = concatMap (afs_sym af);

af_sig :: forall a. Afs a -> [(a, Arith.Nat)] -> [(a, Arith.Nat)];
af_sig af = map (Product_Type.map_prod filtered_fun id) . afs_sig af;

rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Maybe ((a, Arith.Nat) -> Af_entry,
   Set.Set (a, Arith.Nat));
rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
  (Abs_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
    x)
  = x;

sel21 ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Afs a;
sel21 xa =
  Abs_afs
    (case rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
            xa
      of {
      Nothing -> rep_afs (error "undefined");
      Just x2 -> x2;
    });

dis1 ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Bool;
dis1 xa =
  (case rep_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
          xa
    of {
    Nothing -> True;
    Just _ -> False;
  });

rep_isom ::
  forall a.
    (Compare.Compare_order a) => X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                   a ->
                                   Maybe (Afs a);
rep_isom x = (if dis1 x then Nothing else Just (sel21 x));

default_af_entry :: Arith.Nat -> Af_entry;
default_af_entry n = AFList (List.upt Arith.zero_nat n);

wf_af_entry :: Arith.Nat -> Af_entry -> Bool;
wf_af_entry n (Collapse i) = Arith.less_nat i n;
wf_af_entry n (AFList is) = all (\ i -> Arith.less_nat i n) is;

afs_of_aux ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare_order a,
      Set_Impl.Set_impl a) => [((a, Arith.Nat), Af_entry)] ->
                                X_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
                                  a;
afs_of_aux xa =
  Abs_x_compare_order_x_x_f_afs_option_x_x_nat_x_compare_order_x_x_f_prod_set_af_entry_nat_x_compare_order_x_x_f_prod_fun_prod_option
    (if all (\ ((_, n), e) -> wf_af_entry n e) xa
      then Just (Map_Choice.fun_of_map_fun (Map_Choice.ceta_map_of xa)
                   (\ fn -> default_af_entry (snd fn)),
                  List.set (map fst xa))
      else Nothing);

afs_of ::
  forall a.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare_order a,
      Set_Impl.Set_impl a) => [((a, Arith.Nat), Af_entry)] -> Maybe (Afs a);
afs_of x = rep_isom (afs_of_aux x);

apply_af_entry :: forall a b. a -> Af_entry -> [Term.Term a b] -> Term.Term a b;
apply_af_entry uu (Collapse i) ts = List.nth ts i;
apply_af_entry f (AFList is) ts = Term.Fun f (map (List.nth ts) is);

afs_term :: forall a b. Afs a -> Term.Term a b -> Term.Term (Filtered a) b;
afs_term pi (Term.Fun f ts) =
  let {
    l = List.size_list ts;
  } in apply_af_entry (FPair f l) (afs pi (f, l)) (map (afs_term pi) ts);
afs_term pi (Term.Var x) = Term.Var x;

afs_rule ::
  forall a b.
    Afs a ->
      (Term.Term a b, Term.Term a b) ->
        (Term.Term (Filtered a) b, Term.Term (Filtered a) b);
afs_rule pi lr = (afs_term pi (fst lr), afs_term pi (snd lr));

af_rule ::
  forall a b.
    Afs a -> (Term.Term a b, Term.Term a b) -> (Term.Term a b, Term.Term a b);
af_rule pi = (\ t -> Trs.map_funs_rule filtered_fun (afs_rule pi t));

af_term :: forall a b. Afs a -> Term.Term a b -> Term.Term a b;
af_term pi (Term.Fun f ts) =
  apply_af_entry f (afs pi (f, List.size_list ts)) (map (af_term pi) ts);
af_term pi (Term.Var x) = Term.Var x;

af_check ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (String -> String) ->
                                  Afs a ->
                                    ((Term.Term a b, Term.Term a b) ->
                                      Sum_Type.Sum (String -> String) ()) ->
                                      (Term.Term a b, Term.Term a b) ->
Sum_Type.Sum (String -> String) ();
af_check r pi g lr =
  let {
    pl = af_term pi (fst lr);
    pr = af_term pi (snd lr);
  } in Error_Monad.catch_error (g (pl, pr))
         (\ x ->
           Sum_Type.Inl
             (((((((((((((((Shows_Literal.showsl_literal "could not orient " .
                             Term_More.showsl_terma (fst lr)) .
                            Shows_Literal.showsl_literal " ") .
                           r) .
                          Shows_Literal.showsl_literal " ") .
                         Term_More.showsl_terma (snd lr)) .
                        Shows_Literal.showsl_literal "\npi( ") .
                       Term_More.showsl_terma (fst lr)) .
                      Shows_Literal.showsl_literal " ) = ") .
                     Term_More.showsl_terma pl) .
                    Shows_Literal.showsl_literal "\npi( ") .
                   Term_More.showsl_terma (snd lr)) .
                  Shows_Literal.showsl_literal " ) = ") .
                 Term_More.showsl_terma pr) .
                Shows_Literal.showsl_literal "\n") .
               x));

af_rules ::
  forall a b.
    Afs a ->
      [(Term.Term a b, Term.Term a b)] -> [(Term.Term a b, Term.Term a b)];
af_rules pi r = map (af_rule pi) r;

afs_syms :: forall a. Afs a -> Set.Set (a, Arith.Nat);
afs_syms xa = snd (rep_afs xa);

mono_af_entry :: Arith.Nat -> Af_entry -> Bool;
mono_af_entry n (Collapse i) = Arith.less_eq_nat n Arith.one_nat;
mono_af_entry n (AFList ids) =
  all (List.member ids) (List.upt Arith.zero_nat n);

mono_afs ::
  forall a. (Collection_Eq.Ceq a, Collection_Order.Ccompare a) => Afs a -> Bool;
mono_afs pi =
  Set.ball (afs_syms pi) (\ (f, n) -> mono_af_entry n (afs pi (f, n)));

afs_check ::
  forall a b.
    (Shows_Literal.Showl a,
      Shows_Literal.Showl b) => (String -> String) ->
                                  Afs a ->
                                    ((Term.Term (Filtered a) b,
                                       Term.Term (Filtered a) b) ->
                                      Sum_Type.Sum (String -> String) ()) ->
                                      (Term.Term a b, Term.Term a b) ->
Sum_Type.Sum (String -> String) ();
afs_check r pi g lr =
  let {
    pl = afs_term pi (fst lr);
    pr = afs_term pi (snd lr);
  } in Error_Monad.catch_error (g (pl, pr))
         (\ x ->
           Sum_Type.Inl
             (((((((((((((((Shows_Literal.showsl_literal "could not orient " .
                             Term_More.showsl_terma (fst lr)) .
                            Shows_Literal.showsl_literal " ") .
                           r) .
                          Shows_Literal.showsl_literal " ") .
                         Term_More.showsl_terma (snd lr)) .
                        Shows_Literal.showsl_literal "\npi( ") .
                       Term_More.showsl_terma (fst lr)) .
                      Shows_Literal.showsl_literal " ) = ") .
                     Term_More.showsl_terma pl) .
                    Shows_Literal.showsl_literal "\npi( ") .
                   Term_More.showsl_terma (snd lr)) .
                  Shows_Literal.showsl_literal " ) = ") .
                 Term_More.showsl_terma pr) .
                Shows_Literal.showsl_literal "\n") .
               x));

afs_to_af ::
  forall a.
    (Compare.Compare_order a) => Afs a -> (a, Arith.Nat) -> Set.Set Arith.Nat;
afs_to_af pi fn =
  (case afs pi fn of {
    Collapse j ->
      Set.insert j
        (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_nat));
    AFList a -> List.set a;
  });

showsl_afs ::
  forall a.
    (Shows_Literal.Showl a) => [((a, Arith.Nat), Af_entry)] -> String -> String;
showsl_afs af =
  List.foldr
    (\ (a, b) ->
      (case a of {
        (f, n) ->
          (\ e ->
            (((((Shows_Literal.showsl_literal "pi(" . Shows_Literal.showsl f) .
                 Shows_Literal.showsl_literal "/") .
                Shows_Literal.showsl_nat n) .
               Shows_Literal.showsl_literal ") = ") .
              (case e of {
                Collapse i -> Shows_Literal.showsl_nat (Arith.suc i);
                AFList ids -> Shows_Literal.showsl_list_nat (map Arith.suc ids);
              })) .
              Shows_Literal.showsl_literal "\n");
      })
        b)
    af;

afs_with_af ::
  forall a.
    (Compare.Compare_order a) => Afs a ->
                                   ((a, Arith.Nat) -> Set.Set Arith.Nat) ->
                                     (a, Arith.Nat) -> Set.Set Arith.Nat;
afs_with_af pia pi fn =
  (case afs pia fn of {
    Collapse j ->
      Set.insert j
        (Set_Impl.set_empty (Phantom_Type.of_phantom Set_Impl.set_impl_nat));
    AFList ids ->
      (if ids == List.upt Arith.zero_nat (snd fn) then pi fn else List.set ids);
  });

check_mono_afs ::
  forall a.
    (Collection_Eq.Ceq a,
      Collection_Order.Ccompare a) => Afs a ->
Sum_Type.Sum (String -> String) ();
check_mono_afs pi =
  Check_Monad.check (mono_afs pi)
    (Shows_Literal.showsl_literal "argument filter is not monotone");

permutation_afs ::
  forall a. (Collection_Eq.Ceq a, Collection_Order.Ccompare a) => Afs a -> Bool;
permutation_afs pi =
  Set.ball (afs_syms pi)
    (\ (f, n) ->
      (case afs pi (f, n) of {
        Collapse _ -> False;
        AFList xs ->
          Collection_Eq.set_eq (List.set xs)
            (Set_Interval.atLeastLessThan Arith.zero_nat n) &&
            List.distinct xs;
      }));

fpair_f :: forall a. Filtered a -> a;
fpair_f (FPair x1 x2) = x1;

filtered_rel_impl ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare_order a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [((a, Arith.Nat), Af_entry)] ->
                                  Term_Order_Impl.Rel_impl_ext (Filtered a) b
                                    () ->
                                    Term_Order_Impl.Rel_impl_ext a b ();
filtered_rel_impl pi rp =
  let {
    afso = afs_of pi;
    afs = Option.the afso;
    af = afs_to_af afs;
  } in Term_Order_Impl.Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (not (Option.is_none afso))
             (Shows_Literal.showsl_literal
               "invalid positions in argument filter"))
           (\ _ ->
             Error_Monad.bind (Term_Order_Impl.valid rp)
               (\ _ ->
                 Error_Monad.bind (Term_Order_Impl.top_refl rp)
                   (\ _ -> Term_Order_Impl.standard rp))))
         (Sum_Type.Inr ())
         (((Shows_Literal.showsl_literal "Argument Filter:\n" . showsl_afs pi) .
            Shows_Literal.showsl_literal "\n") .
           Term_Order_Impl.desc rp)
         (afs_check (Shows_Literal.showsl_literal ">") afs
           (Term_Order_Impl.s rp))
         (afs_check (Shows_Literal.showsl_literal ">=") afs
           (Term_Order_Impl.ns rp))
         (afs_check (Shows_Literal.showsl_literal ">=") afs
           (Term_Order_Impl.nst rp))
         af Term_Order.full_af (Term_Order_Impl.sn rp)
         (Term_Order_Impl.subst_s rp) (Term_Order_Impl.ce_compat rp)
         (Term_Order_Impl.co_rewr rp)
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit
             "top-mono with argument filter not yet supported"))
         (Sum_Type.Inr ()) Term_Order.empty_af
         (\ sig ->
           Error_Monad.bind (check_mono_afs afs)
             (\ _ -> Term_Order_Impl.mono rp (afs_sig afs sig)))
         (Option.map_option
           (\ fs -> map fst pi ++ map (\ (f, a) -> (fpair_f f, a)) fs)
           (Term_Order_Impl.not_wst rp))
         Nothing Term_Order_Impl.no_complexity_check ();

filtered_rel_impl_af ::
  forall a b.
    (Collection_Eq.Ceq a, Collection_Order.Ccompare a, Compare.Compare_order a,
      Set_Impl.Set_impl a, Shows_Literal.Showl a,
      Shows_Literal.Showl b) => [((a, Arith.Nat), Af_entry)] ->
                                  Term_Order_Impl.Rel_impl_ext a b () ->
                                    Term_Order_Impl.Rel_impl_ext a b ();
filtered_rel_impl_af pi rp =
  let {
    afso = afs_of pi;
    afs = Option.the afso;
    af = afs_with_af afs (Term_Order_Impl.af rp);
  } in Term_Order_Impl.Rel_impl_ext
         (Error_Monad.bind
           (Check_Monad.check (not (Option.is_none afso))
             (Shows_Literal.showsl_literal
               "invalid positions in argument filter"))
           (\ _ ->
             Error_Monad.bind (Term_Order_Impl.valid rp)
               (\ _ ->
                 Error_Monad.bind (Term_Order_Impl.top_refl rp)
                   (\ _ -> Term_Order_Impl.standard rp))))
         (Sum_Type.Inr ())
         (((Shows_Literal.showsl_literal "Argument Filter:\n" . showsl_afs pi) .
            Shows_Literal.showsl_literal "\n") .
           Term_Order_Impl.desc rp)
         (af_check (Shows_Literal.showsl_literal ">") afs
           (Term_Order_Impl.s rp))
         (af_check (Shows_Literal.showsl_literal ">=") afs
           (Term_Order_Impl.ns rp))
         (af_check (Shows_Literal.showsl_literal ">=") afs
           (Term_Order_Impl.nst rp))
         af Term_Order.full_af (Term_Order_Impl.sn rp)
         (Term_Order_Impl.subst_s rp) (Term_Order_Impl.ce_compat rp)
         (Term_Order_Impl.co_rewr rp)
         (Sum_Type.Inl
           (Shows_Literal.showsl_lit
             "top-mono with argument filter not yet supported"))
         (Sum_Type.Inr ()) Term_Order.empty_af
         (\ sig ->
           Error_Monad.bind (check_mono_afs afs)
             (\ _ -> Term_Order_Impl.mono rp (af_sig afs sig)))
         (Option.map_option (\ a -> map fst pi ++ a)
           (Term_Order_Impl.not_wst rp))
         Nothing Term_Order_Impl.no_complexity_check ();

}
