{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Reduction_Pair_Implementations(Redtriple_impl(..), get_rel_impl,
                                  default_rel_impl, get_non_inf_order)
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
import qualified Non_Inf_Order;
import qualified Non_Inf_Order_Impl;
import qualified Quasi_Order;
import qualified Linear_Poly_Order;
import qualified Poly_Order;
import qualified Ackbo_Impl;
import qualified RPO_More;
import qualified KBO_Impl;
import qualified CoWPO_Impl;
import qualified GWPO_Impl;
import qualified SPO_Impl;
import qualified Map_Choice;
import qualified WPO_Impl;
import qualified SCNP_Impl;
import qualified Error_Monad;
import qualified Linear_Poly_Complexity;
import qualified Ordered_Semiring;
import qualified Congruence;
import qualified Max_Polynomial_Impl;
import qualified Max_Monus_Impl;
import qualified IA_Checker;
import qualified Group;
import qualified Ring;
import qualified Sum_Type;
import qualified Compare;
import qualified Matrix_Poly;
import qualified Compare_Order_Instances;
import qualified Shows_Literal_Matrix;
import qualified Matrix_Carrier_Impl;
import qualified Show_Real;
import qualified Mapping;
import qualified List_Lexorder;
import qualified Complexity_Carrier;
import qualified Poly_Order_Neg;
import qualified NthRoot;
import qualified HOL;
import qualified List_Order_Implementations;
import qualified Matrix_Core_Order_Impl;
import qualified Max_Polynomial;
import qualified Max_Monus;
import qualified Polynomials;
import qualified WPO;
import qualified Matrix;
import qualified Term_Rewriting;
import qualified Arith;

data Redtriple_impl a = Int_carrier [((a, Arith.Nat), (Arith.Int, [Arith.Int]))]
  | Int_nl_carrier
      [((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Arith.Int)])]
  | Neg_Integer_Poly
      [((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Arith.Int)])]
  | Rat_carrier [((a, Arith.Nat), (Term_Rewriting.Rat, [Term_Rewriting.Rat]))]
  | Rat_nl_carrier Term_Rewriting.Rat
      [((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Term_Rewriting.Rat)])]
  | Real_carrier
      [((a, Arith.Nat), (Term_Rewriting.Real, [Term_Rewriting.Real]))]
  | Real_nl_carrier Term_Rewriting.Real
      [((a, Arith.Nat), [(Polynomials.Monom Arith.Nat, Term_Rewriting.Real)])]
  | Arctic_carrier
      [((a, Arith.Nat), (Term_Rewriting.Arctic, [Term_Rewriting.Arctic]))]
  | Arctic_rat_carrier
      [((a, Arith.Nat),
         (Term_Rewriting.Arctic_delta Term_Rewriting.Rat,
           [Term_Rewriting.Arctic_delta Term_Rewriting.Rat]))]
  | Int_mat_carrier Arith.Nat Arith.Nat
      [((a, Arith.Nat), (Matrix.Mat Arith.Int, [Matrix.Mat Arith.Int]))]
  | Rat_mat_carrier Arith.Nat Arith.Nat
      [((a, Arith.Nat),
         (Matrix.Mat Term_Rewriting.Rat, [Matrix.Mat Term_Rewriting.Rat]))]
  | Real_mat_carrier Arith.Nat Arith.Nat
      [((a, Arith.Nat),
         (Matrix.Mat Term_Rewriting.Real, [Matrix.Mat Term_Rewriting.Real]))]
  | Core_matrix (Matrix_Core_Order_Impl.Core_matrix_inter a Arith.Int)
  | Core_matrix_delta Term_Rewriting.Real
      (Matrix_Core_Order_Impl.Core_matrix_inter a Term_Rewriting.Real)
  | Arctic_mat_carrier Arith.Nat
      [((a, Arith.Nat),
         (Matrix.Mat Term_Rewriting.Arctic,
           [Matrix.Mat Term_Rewriting.Arctic]))]
  | Arctic_rat_mat_carrier Arith.Nat
      [((a, Arith.Nat),
         (Matrix.Mat (Term_Rewriting.Arctic_delta Term_Rewriting.Rat),
           [Matrix.Mat (Term_Rewriting.Arctic_delta Term_Rewriting.Rat)]))]
  | RPO [((a, Arith.Nat), (Arith.Nat, WPO.Order_tag))]
      [((a, Arith.Nat), Term_Rewriting.Af_entry)]
  | KBO ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
          Arith.Nat)
      [((a, Arith.Nat), Term_Rewriting.Af_entry)]
  | ACKBO ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Bool)))], Arith.Nat)
      [((a, Arith.Nat), Term_Rewriting.Af_entry)]
  | WPO [((a, Arith.Nat), (Arith.Nat, ([Arith.Nat], WPO.Order_tag)))]
      (Redtriple_impl a)
  | GWPO ([((a, Arith.Nat), Arith.Nat)], a -> a) (Redtriple_impl a)
  | MSPO (Redtriple_impl a)
  | COWPO [((a, Arith.Nat), (Arith.Nat, ([Arith.Nat], WPO.Order_tag)))]
      (Redtriple_impl a)
  | Max_poly
      [((a, Arith.Nat), Term_Rewriting.Term Max_Polynomial.Sig Arith.Nat)]
  | Max_monus [((a, Arith.Nat), Term_Rewriting.Term Max_Monus.Sig Arith.Nat)]
  | Filtered_Redtriple [((a, Arith.Nat), Term_Rewriting.Af_entry)]
      (Redtriple_impl a)
  | SCNP List_Order_Implementations.List_order_type
      [((a, Arith.Nat), [(Arith.Nat, Arith.Nat)])] (Redtriple_impl a);

sqrt_real :: Term_Rewriting.Real -> [Term_Rewriting.Real];
sqrt_real x =
  (if Term_Rewriting.less_eq_real Term_Rewriting.zero_real x
    then let {
           y = NthRoot.sqrt x;
         } in Arith.remdups [y, Term_Rewriting.uminus_real y]
    else []);

filter_prec_weight_ac_repr ::
  forall a.
    ((a, Arith.Nat) -> Term_Rewriting.Af_entry) ->
      ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Bool)))], Arith.Nat) ->
        ([((Term_Rewriting.Filtered a, Arith.Nat),
            (Arith.Nat, (Arith.Nat, Bool)))],
          Arith.Nat);
filter_prec_weight_ac_repr pi (prw, w0) =
  let {
    fprw = filter (\ (fn, _) -> (case pi fn of {
                                  Term_Rewriting.Collapse _ -> False;
                                  Term_Rewriting.AFList _ -> True;
                                }))
             prw;
    mprw =
      map (\ (a, b) ->
            (case a of {
              (f, n) ->
                (\ aa ->
                  ((Term_Rewriting.FPair f n,
                     (case pi (f, n) of {
                       Term_Rewriting.Collapse _ -> Arith.zero_nat;
                       Term_Rewriting.AFList ab -> Arith.size_list ab;
                     })),
                    aa));
            })
              b)
        fprw;
  } in (mprw, w0);

filter_prec_weight_repr ::
  forall a.
    ((a, Arith.Nat) -> Term_Rewriting.Af_entry) ->
      ([((a, Arith.Nat), (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
        Arith.Nat) ->
        ([((Term_Rewriting.Filtered a, Arith.Nat),
            (Arith.Nat, (Arith.Nat, Maybe [Arith.Nat])))],
          Arith.Nat);
filter_prec_weight_repr pi (prw, w0) =
  let {
    fprw = filter (\ (fn, _) -> (case pi fn of {
                                  Term_Rewriting.Collapse _ -> False;
                                  Term_Rewriting.AFList _ -> True;
                                }))
             prw;
    mprw =
      map (\ (a, b) ->
            (case a of {
              (f, n) ->
                (\ aa ->
                  ((Term_Rewriting.FPair f n,
                     (case pi (f, n) of {
                       Term_Rewriting.Collapse _ -> Arith.zero_nat;
                       Term_Rewriting.AFList ab -> Arith.size_list ab;
                     })),
                    aa));
            })
              b)
        fprw;
  } in (mprw, w0);

prec_repr_to_status ::
  forall a.
    (Compare.Compare_order a) => [((a, Arith.Nat),
                                    (Arith.Nat, WPO.Order_tag))] ->
                                   (Term_Rewriting.Filtered a, Arith.Nat) ->
                                     WPO.Order_tag;
prec_repr_to_status prs =
  let {
    m = Map_Choice.ceta_map_of prs;
  } in (\ (Term_Rewriting.FPair f a, _) -> (case m (f, a) of {
     Nothing -> WPO.Lex;
     Just aa -> snd aa;
   }));

prec_repr_to_pr ::
  forall a.
    (Compare.Compare_order a) => [((a, Arith.Nat),
                                    (Arith.Nat, WPO.Order_tag))] ->
                                   (Term_Rewriting.Filtered a, Arith.Nat) ->
                                     Arith.Nat;
prec_repr_to_pr prs =
  let {
    m = Map_Choice.ceta_map_of prs;
  } in (\ (Term_Rewriting.FPair f a, _) -> (case m (f, a) of {
     Nothing -> Arith.zero_nat;
     Just aa -> fst aa;
   }));

get_rel_impl ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Eq a,
      Arith.Set_impl a,
      Term_Rewriting.Showl a) => Redtriple_impl a ->
                                   Term_Rewriting.Rel_impl_ext a [Arith.Char]
                                     ();
get_rel_impl (Int_carrier i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.class_lpoly_order Arith.one_int Term_Rewriting.int_mono
      (\ x y -> Arith.less_int y x))
    (Sum_Type.Inr ()) i;
get_rel_impl (Neg_Integer_Poly i) =
  Poly_Order_Neg.create_negpoly_rel_impl
    (Error_Monad.bind (Poly_Order_Neg.check_poly_inter_list_neg i)
      (\ _ -> Sum_Type.Inr ()))
    Arith.zero_int (\ x y -> Arith.less_int y x) True i;
get_rel_impl (Int_nl_carrier i) =
  Poly_Order.create_nlpoly_rel_impl (Sum_Type.Inr ()) Arith.one_int
    (\ x y -> Arith.less_int y x) True True i;
get_rel_impl (Rat_carrier i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.class_lpoly_order Term_Rewriting.one_rat
      Term_Rewriting.delta_mono (\ x y -> Term_Rewriting.less_rat y x))
    (Matrix_Poly.check_def_pos Term_Rewriting.one_rat) i;
get_rel_impl (Rat_nl_carrier d i) =
  Poly_Order.create_nlpoly_rel_impl (Matrix_Poly.check_def_pos d) d
    (Term_Rewriting.delta_gt d)
    (Term_Rewriting.less_eq_rat Term_Rewriting.one_rat d) False i;
get_rel_impl (Real_carrier i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.class_lpoly_order Term_Rewriting.one_real
      Term_Rewriting.delta_mono (\ x y -> Term_Rewriting.less_real y x))
    (Matrix_Poly.check_def_pos Term_Rewriting.one_real) i;
get_rel_impl (Real_nl_carrier d i) =
  Poly_Order.create_nlpoly_rel_impl (Matrix_Poly.check_def_pos d) d
    (Term_Rewriting.delta_gt d)
    (Term_Rewriting.less_eq_real Term_Rewriting.one_real d) False i;
get_rel_impl (Arctic_carrier i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.class_arc_lpoly_order Term_Rewriting.one_arctic
      Term_Rewriting.pos_arctic (\ x y -> Term_Rewriting.less_arctic y x))
    (Sum_Type.Inr ()) i;
get_rel_impl (Arctic_rat_carrier i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.class_arc_lpoly_order Term_Rewriting.one_arctic_delta
      Term_Rewriting.pos_arctic_delta Term_Rewriting.weak_gt_arctic_delta)
    (Sum_Type.Inr ()) i;
get_rel_impl (Int_mat_carrier n sd i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.mat_lpoly_order n sd Arith.one_int Term_Rewriting.int_mono
      (\ x y -> Arith.less_int y x))
    (Matrix_Poly.check_dimensions n sd (Sum_Type.Inr ())) i;
get_rel_impl (Rat_mat_carrier n sd i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.mat_lpoly_order n sd Term_Rewriting.one_rat
      Term_Rewriting.delta_mono (\ x y -> Term_Rewriting.less_rat y x))
    (Matrix_Poly.check_dimensions n sd
      (Matrix_Poly.check_def_pos Term_Rewriting.one_rat))
    i;
get_rel_impl (Real_mat_carrier n sd i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.mat_lpoly_order n sd Term_Rewriting.one_real
      Term_Rewriting.delta_mono (\ x y -> Term_Rewriting.less_real y x))
    (Matrix_Poly.check_dimensions n sd
      (Matrix_Poly.check_def_pos Term_Rewriting.one_real))
    i;
get_rel_impl (Arctic_mat_carrier n i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.mat_arc_lpoly_order n Term_Rewriting.one_arctic
      Term_Rewriting.pos_arctic (\ x y -> Term_Rewriting.less_arctic y x))
    (Matrix_Poly.check_arc_dimension n) i;
get_rel_impl (Core_matrix mI) =
  Matrix_Core_Order_Impl.create_core_matrix_int mI;
get_rel_impl (Core_matrix_delta d mI) =
  Matrix_Core_Order_Impl.create_core_matrix_fract d mI;
get_rel_impl (Arctic_rat_mat_carrier n i) =
  Linear_Poly_Order.create_poly_rel_impl
    (Matrix_Poly.mat_arc_lpoly_order n Term_Rewriting.one_arctic_delta
      Term_Rewriting.pos_arctic_delta Term_Rewriting.weak_gt_arctic_delta)
    (Matrix_Poly.check_arc_dimension n) i;
get_rel_impl (Max_poly alist) =
  Max_Polynomial_Impl.max_poly_rel_impl
    (Max_Polynomial_Impl.Max_Poly_Impl IA_Checker.BB_Solver alist);
get_rel_impl (Max_monus alist) =
  Max_Monus_Impl.max_monus_rel_impl
    (Max_Monus_Impl.Max_Monus_Impl IA_Checker.BB_Solver alist);
get_rel_impl (RPO prec_tau pi) =
  Term_Rewriting.filtered_rel_impl pi
    (RPO_More.create_RPO_rel_impl
      (\ pr -> (prec_repr_to_pr pr, prec_repr_to_status pr)) prec_tau);
get_rel_impl (KBO precw pi) =
  Term_Rewriting.filtered_rel_impl pi
    (KBO_Impl.create_KBO_rel_impl
      (filter_prec_weight_repr
        (Map_Choice.fun_of_map_fun (Map_Choice.ceta_map_of pi)
          (\ fn -> Term_Rewriting.default_af_entry (snd fn))))
      precw);
get_rel_impl (ACKBO precw pi) =
  Term_Rewriting.filtered_rel_impl pi
    (Ackbo_Impl.create_ACKBO_rel_impl
      (filter_prec_weight_ac_repr
        (Map_Choice.fun_of_map_fun (Map_Choice.ceta_map_of pi)
          (\ fn -> Term_Rewriting.default_af_entry (snd fn))))
      precw);
get_rel_impl (WPO params rp) = WPO_Impl.wpo_rel_impl (get_rel_impl rp) params;
get_rel_impl (GWPO params rp) =
  GWPO_Impl.gwpo_rel_impl (get_rel_impl rp) params;
get_rel_impl (MSPO rp) = SPO_Impl.mspo_rel_impl (get_rel_impl rp);
get_rel_impl (COWPO params rp) =
  CoWPO_Impl.cowpo_rel_impl (get_rel_impl rp) params;
get_rel_impl (Filtered_Redtriple alist rp) =
  Term_Rewriting.filtered_rel_impl_af alist (get_rel_impl rp);
get_rel_impl (SCNP typea af rp) =
  SCNP_Impl.generate_scnp_rp
    (List_Order_Implementations.list_ext (SCNP_Impl.scnp_arity af) typea)
    (Term_Rewriting.showsl_lit (List_Order_Implementations.list_ext_name typea))
    af (get_rel_impl rp);

default_rel_impl ::
  forall a.
    (Arith.Ceq a, Arith.Ccompare a, Compare.Compare_order a, Eq a,
      Arith.Set_impl a,
      Term_Rewriting.Showl a) => Term_Rewriting.Rel_impl_type a [Arith.Char]
                                   (Redtriple_impl a);
default_rel_impl = Term_Rewriting.Abs_rel_impl_type get_rel_impl;

faulty_non_inf_order ::
  forall a b c.
    (Term_Rewriting.Showl b,
      Term_Rewriting.Showl c) => String ->
                                   a -> Non_Inf_Order_Impl.Non_inf_order_ext b c
  ();
faulty_non_inf_order s f =
  Non_Inf_Order_Impl.Non_inf_order_ext
    (Sum_Type.Inl (Term_Rewriting.showsl_lit s)) (\ _ -> Sum_Type.Inr ())
    (\ _ -> Sum_Type.Inr ()) (\ _ _ -> Non_Inf_Order.Wild) id ();

get_non_inf_order ::
  forall a b.
    (Compare.Compare_order a, Eq a, Term_Rewriting.Showl a, Eq b,
      Quasi_Order.Linorder b,
      Term_Rewriting.Showl b) => Redtriple_impl a ->
                                   [(a, Arith.Nat)] ->
                                     Non_Inf_Order_Impl.Non_inf_order_ext a b
                                       ();
get_non_inf_order (Int_nl_carrier i) =
  Poly_Order.create_nlpoly_non_inf_order (Sum_Type.Inr ()) Arith.one_int
    (\ x y -> Arith.less_int y x) True True Term_Rewriting.sqrt_int i;
get_non_inf_order (Rat_nl_carrier d i) =
  Poly_Order.create_nlpoly_non_inf_order (Matrix_Poly.check_def_pos d) d
    (Term_Rewriting.delta_gt d)
    (Term_Rewriting.less_eq_rat Term_Rewriting.one_rat d) False
    Term_Rewriting.sqrt_rat i;
get_non_inf_order (Real_nl_carrier d i) =
  Poly_Order.create_nlpoly_non_inf_order (Matrix_Poly.check_def_pos d) d
    (Term_Rewriting.delta_gt d)
    (Term_Rewriting.less_eq_real Term_Rewriting.one_real d) False sqrt_real i;
get_non_inf_order (Int_carrier v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Neg_Integer_Poly v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Rat_carrier v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Real_carrier v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Arctic_carrier v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Arctic_rat_carrier v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Int_mat_carrier v va vb) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Rat_mat_carrier v va vb) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Real_mat_carrier v va vb) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Core_matrix v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Core_matrix_delta v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Arctic_mat_carrier v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Arctic_rat_mat_carrier v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (RPO v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (KBO v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (ACKBO v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (WPO v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (GWPO v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (MSPO v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (COWPO v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Max_poly v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Max_monus v) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (Filtered_Redtriple v va) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";
get_non_inf_order (SCNP v va vb) =
  faulty_non_inf_order
    "only integers, rationals and reals are supported for non-inf orders";

}
