{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Container_Setup(set_impl_rat, set_impl_term, set_impl_ta_rule, set_impl_ty)
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
import qualified Tree_Automata_Autoref_Setup;
import qualified Ground_Context_Impl;
import qualified Option;
import qualified Labelings_Impl;
import qualified Term_Impl;
import qualified Formula;
import qualified Compare_Instances;
import qualified Integer_Arithmetic;
import qualified Forbidden_Patterns;
import qualified Subterm_and_Context;
import qualified Cooperation_Program;
import qualified Linear_Polynomial;
import qualified Argument_Filter;
import qualified SN_Order_Carrier;
import qualified Multihole_Context;
import qualified Tree_Automata;
import qualified Ground_Context;
import qualified QDelta;
import qualified Arith;
import qualified Labelings;
import qualified Mapping_Impl;
import qualified LTS;
import qualified Simplex;
import qualified Cardinality;
import qualified Term;
import qualified Real;
import qualified Collection_Order;
import qualified Collection_Enum;
import qualified Phantom_Type;
import qualified Set_Impl;
import qualified Collection_Eq;
import qualified Comparator;
import qualified Rat;
import qualified Compare;

compare_rat :: Rat.Rat -> Rat.Rat -> Comparator.Order;
compare_rat = Comparator.comparator_of;

instance Compare.Compare Rat.Rat where {
  compare = compare_rat;
};

ceq_rat :: Maybe (Rat.Rat -> Rat.Rat -> Bool);
ceq_rat = Just Rat.equal_rat;

instance Collection_Eq.Ceq Rat.Rat where {
  ceq = ceq_rat;
};

set_impl_rat :: Phantom_Type.Phantom Rat.Rat Set_Impl.Set_impla;
set_impl_rat = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl Rat.Rat where {
  set_impl = set_impl_rat;
};

cEnum_rat ::
  Maybe ([Rat.Rat], ((Rat.Rat -> Bool) -> Bool, (Rat.Rat -> Bool) -> Bool));
cEnum_rat = Nothing;

instance Collection_Enum.Cenum Rat.Rat where {
  cEnum = cEnum_rat;
};

ccompare_rat :: Maybe (Rat.Rat -> Rat.Rat -> Comparator.Order);
ccompare_rat = Just compare_rat;

instance Collection_Order.Ccompare Rat.Rat where {
  ccompare = ccompare_rat;
};

ceq_real :: Maybe (Real.Real -> Real.Real -> Bool);
ceq_real = Just Real.equal_real;

instance Collection_Eq.Ceq Real.Real where {
  ceq = ceq_real;
};

set_impl_real :: Phantom_Type.Phantom Real.Real Set_Impl.Set_impla;
set_impl_real = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl Real.Real where {
  set_impl = set_impl_real;
};

cEnum_real ::
  Maybe ([Real.Real],
          ((Real.Real -> Bool) -> Bool, (Real.Real -> Bool) -> Bool));
cEnum_real = Nothing;

instance Collection_Enum.Cenum Real.Real where {
  cEnum = cEnum_real;
};

compare_real :: Real.Real -> Real.Real -> Comparator.Order;
compare_real = Comparator.comparator_of;

ccompare_real :: Maybe (Real.Real -> Real.Real -> Comparator.Order);
ccompare_real = Just compare_real;

instance Collection_Order.Ccompare Real.Real where {
  ccompare = ccompare_real;
};

ceq_term ::
  forall a b. (Eq a, Eq b) => Maybe (Term.Term a b -> Term.Term a b -> Bool);
ceq_term = Just Term.equal_term;

instance (Eq a, Eq b) => Collection_Eq.Ceq (Term.Term a b) where {
  ceq = ceq_term;
};

set_impl_term ::
  forall a b. Phantom_Type.Phantom (Term.Term a b) Set_Impl.Set_impla;
set_impl_term = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Term.Term a b) where {
  set_impl = set_impl_term;
};

cEnum_term ::
  forall a b.
    Maybe ([Term.Term a b],
            ((Term.Term a b -> Bool) -> Bool, (Term.Term a b -> Bool) -> Bool));
cEnum_term = Nothing;

instance Collection_Enum.Cenum (Term.Term a b) where {
  cEnum = cEnum_term;
};

finite_UNIV_term :: forall a b. Phantom_Type.Phantom (Term.Term a b) Bool;
finite_UNIV_term = Phantom_Type.Phantom False;

instance Cardinality.Finite_UNIV (Term.Term a b) where {
  finite_UNIV = finite_UNIV_term;
};

ccompare_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Term.Term a b ->
                                    Term.Term a b -> Comparator.Order);
ccompare_term = Just Term_Impl.compare_term;

instance (Compare.Compare a,
           Compare.Compare b) => Collection_Order.Ccompare (Term.Term a
                     b) where {
  ccompare = ccompare_term;
};

cproper_interval_term ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Term.Term a b) ->
                              Maybe (Term.Term a b) -> Bool;
cproper_interval_term = (\ _ _ -> False);

instance (Compare.Compare a,
           Compare.Compare b) => Collection_Order.Cproper_interval (Term.Term a
                             b) where {
  cproper_interval = cproper_interval_term;
};

ceq_atom ::
  forall a. (Eq a) => Maybe (Simplex.Atom a -> Simplex.Atom a -> Bool);
ceq_atom = Just Simplex.equal_atom;

instance (Eq a) => Collection_Eq.Ceq (Simplex.Atom a) where {
  ceq = ceq_atom;
};

set_impl_atom ::
  forall a. Phantom_Type.Phantom (Simplex.Atom a) Set_Impl.Set_impla;
set_impl_atom = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Simplex.Atom a) where {
  set_impl = set_impl_atom;
};

comparator_atom ::
  forall a.
    (a -> a -> Comparator.Order) ->
      Simplex.Atom a -> Simplex.Atom a -> Comparator.Order;
comparator_atom comp_a (Simplex.Leq x xa) (Simplex.Leq y ya) =
  (case Comparator.comparator_of x y of {
    Comparator.Eqa -> comp_a xa ya;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });
comparator_atom comp_a (Simplex.Leq x xa) (Simplex.Geq yb yc) = Comparator.Lt;
comparator_atom comp_a (Simplex.Geq x xa) (Simplex.Leq y ya) = Comparator.Gt;
comparator_atom comp_a (Simplex.Geq x xa) (Simplex.Geq yb yc) =
  (case Comparator.comparator_of x yb of {
    Comparator.Eqa -> comp_a xa yc;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

ccompare_atom ::
  forall a.
    (Collection_Order.Ccompare a) => Maybe (Simplex.Atom a ->
     Simplex.Atom a -> Comparator.Order);
ccompare_atom = (case Collection_Order.ccompare of {
                  Nothing -> Nothing;
                  Just comp_a -> Just (comparator_atom comp_a);
                });

instance (Collection_Order.Ccompare a) => Collection_Order.Ccompare (Simplex.Atom
                              a) where {
  ccompare = ccompare_atom;
};

ccompare_trans_var ::
  forall a.
    (Collection_Order.Ccompare a) => Maybe (LTS.Trans_var a ->
     LTS.Trans_var a -> Comparator.Order);
ccompare_trans_var = (case Collection_Order.ccompare of {
                       Nothing -> Nothing;
                       Just comp_v -> Just (LTS.comparator_trans_var comp_v);
                     });

instance (Collection_Order.Ccompare a) => Collection_Order.Ccompare (LTS.Trans_var
                              a) where {
  ccompare = ccompare_trans_var;
};

mapping_impl_trans_var ::
  forall a. Phantom_Type.Phantom (LTS.Trans_var a) Mapping_Impl.Mapping_impla;
mapping_impl_trans_var = Phantom_Type.Phantom Mapping_Impl.Mapping_RBT;

instance Mapping_Impl.Mapping_impl (LTS.Trans_var a) where {
  mapping_impl = mapping_impl_trans_var;
};

ceq_lab ::
  forall a b.
    (Eq a, Eq b) => Maybe (Labelings.Lab a b -> Labelings.Lab a b -> Bool);
ceq_lab = Just Labelings.equal_lab;

instance (Eq a, Eq b) => Collection_Eq.Ceq (Labelings.Lab a b) where {
  ceq = ceq_lab;
};

set_impl_lab ::
  forall a b. Phantom_Type.Phantom (Labelings.Lab a b) Set_Impl.Set_impla;
set_impl_lab = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Labelings.Lab a b) where {
  set_impl = set_impl_lab;
};

finite_UNIV_lab :: forall a b. Phantom_Type.Phantom (Labelings.Lab a b) Bool;
finite_UNIV_lab = Phantom_Type.Phantom False;

card_UNIV_lab :: forall a b. Phantom_Type.Phantom (Labelings.Lab a b) Arith.Nat;
card_UNIV_lab = Phantom_Type.Phantom Arith.zero_nat;

instance Cardinality.Finite_UNIV (Labelings.Lab a b) where {
  finite_UNIV = finite_UNIV_lab;
};

instance Cardinality.Card_UNIV (Labelings.Lab a b) where {
  card_UNIV = card_UNIV_lab;
};

cEnum_lab ::
  forall a b.
    Maybe ([Labelings.Lab a b],
            ((Labelings.Lab a b -> Bool) -> Bool,
              (Labelings.Lab a b -> Bool) -> Bool));
cEnum_lab = Nothing;

instance Collection_Enum.Cenum (Labelings.Lab a b) where {
  cEnum = cEnum_lab;
};

ccompare_lab ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Labelings.Lab a b ->
                                    Labelings.Lab a b -> Comparator.Order);
ccompare_lab = Just Labelings_Impl.compare_lab;

instance (Compare.Compare a,
           Compare.Compare b) => Collection_Order.Ccompare (Labelings.Lab a
                     b) where {
  ccompare = ccompare_lab;
};

mapping_impl_lab ::
  forall a b.
    Phantom_Type.Phantom (Labelings.Lab a b) Mapping_Impl.Mapping_impla;
mapping_impl_lab = Phantom_Type.Phantom Mapping_Impl.Mapping_RBT;

instance Mapping_Impl.Mapping_impl (Labelings.Lab a b) where {
  mapping_impl = mapping_impl_lab;
};

cproper_interval_lab ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Labelings.Lab a b) ->
                              Maybe (Labelings.Lab a b) -> Bool;
cproper_interval_lab = (\ _ _ -> False);

instance (Compare.Compare a,
           Compare.Compare b) => Collection_Order.Cproper_interval (Labelings.Lab
                             a b) where {
  cproper_interval = cproper_interval_lab;
};

ccompare_QDelta :: Maybe (QDelta.QDelta -> QDelta.QDelta -> Comparator.Order);
ccompare_QDelta = Just Comparator.comparator_of;

instance Collection_Order.Ccompare QDelta.QDelta where {
  ccompare = ccompare_QDelta;
};

ceq_transition_rule ::
  forall a b c d.
    (Eq a, Eq b, Eq c,
      Eq d) => Maybe (LTS.Transition_rule a b c d ->
                       LTS.Transition_rule a b c d -> Bool);
ceq_transition_rule = Just LTS.equal_transition_rule;

instance (Eq a, Eq b, Eq c,
           Eq d) => Collection_Eq.Ceq (LTS.Transition_rule a b c d) where {
  ceq = ceq_transition_rule;
};

set_impl_transition_rule ::
  forall a b c d.
    Phantom_Type.Phantom (LTS.Transition_rule a b c d) Set_Impl.Set_impla;
set_impl_transition_rule = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (LTS.Transition_rule a b c d) where {
  set_impl = set_impl_transition_rule;
};

comparator_formula ::
  forall a.
    (a -> a -> Comparator.Order) ->
      Formula.Formula a -> Formula.Formula a -> Comparator.Order;
comparator_formula comp_a (Formula.Atom x) (Formula.Atom y) = comp_a x y;
comparator_formula comp_a (Formula.Atom x) (Formula.NegAtom ya) = Comparator.Lt;
comparator_formula comp_a (Formula.Atom x) (Formula.Conjunction yb) =
  Comparator.Lt;
comparator_formula comp_a (Formula.Atom x) (Formula.Disjunction yc) =
  Comparator.Lt;
comparator_formula comp_a (Formula.NegAtom x) (Formula.Atom y) = Comparator.Gt;
comparator_formula comp_a (Formula.NegAtom x) (Formula.NegAtom ya) =
  comp_a x ya;
comparator_formula comp_a (Formula.NegAtom x) (Formula.Conjunction yb) =
  Comparator.Lt;
comparator_formula comp_a (Formula.NegAtom x) (Formula.Disjunction yc) =
  Comparator.Lt;
comparator_formula comp_a (Formula.Conjunction x) (Formula.Atom y) =
  Comparator.Gt;
comparator_formula comp_a (Formula.Conjunction x) (Formula.NegAtom ya) =
  Comparator.Gt;
comparator_formula comp_a (Formula.Conjunction x) (Formula.Conjunction yb) =
  Compare_Instances.comparator_list (comparator_formula comp_a) x yb;
comparator_formula comp_a (Formula.Conjunction x) (Formula.Disjunction yc) =
  Comparator.Lt;
comparator_formula comp_a (Formula.Disjunction x) (Formula.Atom y) =
  Comparator.Gt;
comparator_formula comp_a (Formula.Disjunction x) (Formula.NegAtom ya) =
  Comparator.Gt;
comparator_formula comp_a (Formula.Disjunction x) (Formula.Conjunction yb) =
  Comparator.Gt;
comparator_formula comp_a (Formula.Disjunction x) (Formula.Disjunction yc) =
  Compare_Instances.comparator_list (comparator_formula comp_a) x yc;

comparator_transition_rule ::
  forall a b c d.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        (c -> c -> Comparator.Order) ->
          (d -> d -> Comparator.Order) ->
            LTS.Transition_rule a b c d ->
              LTS.Transition_rule a b c d -> Comparator.Order;
comparator_transition_rule comp_f comp_v comp_t comp_l (LTS.Transition x xa xb)
  (LTS.Transition y ya yb) =
  (case comp_l x y of {
    Comparator.Eqa ->
      (case comp_l xa ya of {
        Comparator.Eqa ->
          comparator_formula
            (Term_Impl.comparator_term comp_f
              (Compare_Instances.comparator_prod
                (LTS.comparator_trans_var comp_v) comp_t))
            xb yb;
        Comparator.Lt -> Comparator.Lt;
        Comparator.Gt -> Comparator.Gt;
      });
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

ccompare_transition_rule ::
  forall a b c d.
    (Collection_Order.Ccompare a, Collection_Order.Ccompare b,
      Collection_Order.Ccompare c,
      Collection_Order.Ccompare d) => Maybe (LTS.Transition_rule a b c d ->
      LTS.Transition_rule a b c d -> Comparator.Order);
ccompare_transition_rule =
  (case Collection_Order.ccompare of {
    Nothing -> Nothing;
    Just comp_f ->
      (case Collection_Order.ccompare of {
        Nothing -> Nothing;
        Just comp_v ->
          (case Collection_Order.ccompare of {
            Nothing -> Nothing;
            Just comp_t ->
              (case Collection_Order.ccompare of {
                Nothing -> Nothing;
                Just comp_l ->
                  Just (comparator_transition_rule comp_f comp_v comp_t comp_l);
              });
          });
      });
  });

instance (Collection_Order.Ccompare a, Collection_Order.Ccompare b,
           Collection_Order.Ccompare c,
           Collection_Order.Ccompare d) => Collection_Order.Ccompare (LTS.Transition_rule
                               a b c d) where {
  ccompare = ccompare_transition_rule;
};

ceq_gctxt ::
  forall a b.
    (Eq a) => Maybe (Ground_Context.Gctxt a b ->
                      Ground_Context.Gctxt a b -> Bool);
ceq_gctxt = Just Ground_Context.equal_gctxt;

instance (Eq a) => Collection_Eq.Ceq (Ground_Context.Gctxt a b) where {
  ceq = ceq_gctxt;
};

set_impl_gctxt ::
  forall a b.
    Phantom_Type.Phantom (Ground_Context.Gctxt a b) Set_Impl.Set_impla;
set_impl_gctxt = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Ground_Context.Gctxt a b) where {
  set_impl = set_impl_gctxt;
};

ccompare_gctxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Ground_Context.Gctxt a b ->
                                    Ground_Context.Gctxt a b ->
                                      Comparator.Order);
ccompare_gctxt = Just Ground_Context_Impl.compare_gctxt;

instance (Compare.Compare a,
           Compare.Compare b) => Collection_Order.Ccompare (Ground_Context.Gctxt
                     a b) where {
  ccompare = ccompare_gctxt;
};

ceq_ta_rule ::
  forall a b.
    (Eq a,
      Eq b) => Maybe (Tree_Automata.Ta_rule a b ->
                       Tree_Automata.Ta_rule a b -> Bool);
ceq_ta_rule = Just Tree_Automata.equal_ta_rule;

instance (Eq a, Eq b) => Collection_Eq.Ceq (Tree_Automata.Ta_rule a b) where {
  ceq = ceq_ta_rule;
};

set_impl_ta_rule ::
  forall a b.
    Phantom_Type.Phantom (Tree_Automata.Ta_rule a b) Set_Impl.Set_impla;
set_impl_ta_rule = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Tree_Automata.Ta_rule a b) where {
  set_impl = set_impl_ta_rule;
};

cEnum_ta_rule ::
  forall a b.
    Maybe ([Tree_Automata.Ta_rule a b],
            ((Tree_Automata.Ta_rule a b -> Bool) -> Bool,
              (Tree_Automata.Ta_rule a b -> Bool) -> Bool));
cEnum_ta_rule = Nothing;

instance Collection_Enum.Cenum (Tree_Automata.Ta_rule a b) where {
  cEnum = cEnum_ta_rule;
};

finite_UNIV_ta_rule ::
  forall a b. Phantom_Type.Phantom (Tree_Automata.Ta_rule a b) Bool;
finite_UNIV_ta_rule = Phantom_Type.Phantom False;

instance Cardinality.Finite_UNIV (Tree_Automata.Ta_rule a b) where {
  finite_UNIV = finite_UNIV_ta_rule;
};

ccompare_ta_rule ::
  forall a b.
    (Collection_Order.Ccompare a,
      Collection_Order.Ccompare b) => Maybe (Tree_Automata.Ta_rule a b ->
      Tree_Automata.Ta_rule a b -> Comparator.Order);
ccompare_ta_rule =
  (case Collection_Order.ccompare of {
    Nothing -> Nothing;
    Just comp_q ->
      (case Collection_Order.ccompare of {
        Nothing -> Nothing;
        Just comp_f ->
          Just (Tree_Automata_Autoref_Setup.comparator_ta_rule comp_q comp_f);
      });
  });

instance (Collection_Order.Ccompare a,
           Collection_Order.Ccompare b) => Collection_Order.Ccompare (Tree_Automata.Ta_rule
                               a b) where {
  ccompare = ccompare_ta_rule;
};

cproper_interval_ta_rule ::
  forall a b.
    (Collection_Order.Ccompare a,
      Collection_Order.Ccompare b) => Maybe (Tree_Automata.Ta_rule a b) ->
Maybe (Tree_Automata.Ta_rule a b) -> Bool;
cproper_interval_ta_rule = (\ _ _ -> False);

instance (Collection_Order.Ccompare a,
           Collection_Order.Ccompare b) => Collection_Order.Cproper_interval (Tree_Automata.Ta_rule
                                       a b) where {
  cproper_interval = cproper_interval_ta_rule;
};

ceq_mctxt ::
  forall a b.
    (Eq a,
      Eq b) => Maybe (Multihole_Context.Mctxt a b ->
                       Multihole_Context.Mctxt a b -> Bool);
ceq_mctxt = Just Multihole_Context.equal_mctxt;

instance (Eq a, Eq b) => Collection_Eq.Ceq (Multihole_Context.Mctxt a b) where {
  ceq = ceq_mctxt;
};

set_impl_mctxt ::
  forall a b.
    Phantom_Type.Phantom (Multihole_Context.Mctxt a b) Set_Impl.Set_impla;
set_impl_mctxt = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Multihole_Context.Mctxt a b) where {
  set_impl = set_impl_mctxt;
};

comparator_mctxt ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Multihole_Context.Mctxt a b ->
          Multihole_Context.Mctxt a b -> Comparator.Order;
comparator_mctxt comp_f comp_v (Multihole_Context.MVar x)
  (Multihole_Context.MVar y) = comp_v x y;
comparator_mctxt comp_f comp_v (Multihole_Context.MVar x)
  Multihole_Context.MHole = Comparator.Lt;
comparator_mctxt comp_f comp_v (Multihole_Context.MVar x)
  (Multihole_Context.MFun ya yb) = Comparator.Lt;
comparator_mctxt comp_f comp_v Multihole_Context.MHole
  (Multihole_Context.MVar y) = Comparator.Gt;
comparator_mctxt comp_f comp_v Multihole_Context.MHole Multihole_Context.MHole =
  Comparator.Eqa;
comparator_mctxt comp_f comp_v Multihole_Context.MHole
  (Multihole_Context.MFun ya yb) = Comparator.Lt;
comparator_mctxt comp_f comp_v (Multihole_Context.MFun x xa)
  (Multihole_Context.MVar y) = Comparator.Gt;
comparator_mctxt comp_f comp_v (Multihole_Context.MFun x xa)
  Multihole_Context.MHole = Comparator.Gt;
comparator_mctxt comp_f comp_v (Multihole_Context.MFun x xa)
  (Multihole_Context.MFun ya yb) =
  (case comp_f x ya of {
    Comparator.Eqa ->
      Compare_Instances.comparator_list (comparator_mctxt comp_f comp_v) xa yb;
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_mctxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Multihole_Context.Mctxt a b ->
                              Multihole_Context.Mctxt a b -> Comparator.Order;
compare_mctxt = comparator_mctxt Compare.compare Compare.compare;

ccompare_mctxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Multihole_Context.Mctxt a b ->
                                    Multihole_Context.Mctxt a b ->
                                      Comparator.Order);
ccompare_mctxt = Just compare_mctxt;

instance (Compare.Compare a,
           Compare.Compare b) => Collection_Order.Ccompare (Multihole_Context.Mctxt
                     a b) where {
  ccompare = ccompare_mctxt;
};

ceq_arctic ::
  Maybe (SN_Order_Carrier.Arctic -> SN_Order_Carrier.Arctic -> Bool);
ceq_arctic = Just SN_Order_Carrier.equal_arctic;

instance Collection_Eq.Ceq SN_Order_Carrier.Arctic where {
  ceq = ceq_arctic;
};

set_impl_arctic ::
  Phantom_Type.Phantom SN_Order_Carrier.Arctic Set_Impl.Set_impla;
set_impl_arctic = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl SN_Order_Carrier.Arctic where {
  set_impl = set_impl_arctic;
};

cEnum_arctic ::
  Maybe ([SN_Order_Carrier.Arctic],
          ((SN_Order_Carrier.Arctic -> Bool) -> Bool,
            (SN_Order_Carrier.Arctic -> Bool) -> Bool));
cEnum_arctic = Nothing;

instance Collection_Enum.Cenum SN_Order_Carrier.Arctic where {
  cEnum = cEnum_arctic;
};

comparator_arctic ::
  SN_Order_Carrier.Arctic -> SN_Order_Carrier.Arctic -> Comparator.Order;
comparator_arctic SN_Order_Carrier.MinInfty SN_Order_Carrier.MinInfty =
  Comparator.Eqa;
comparator_arctic SN_Order_Carrier.MinInfty (SN_Order_Carrier.Num_arc y) =
  Comparator.Lt;
comparator_arctic (SN_Order_Carrier.Num_arc x) SN_Order_Carrier.MinInfty =
  Comparator.Gt;
comparator_arctic (SN_Order_Carrier.Num_arc x) (SN_Order_Carrier.Num_arc y) =
  Comparator.comparator_of x y;

compare_arctic ::
  SN_Order_Carrier.Arctic -> SN_Order_Carrier.Arctic -> Comparator.Order;
compare_arctic = comparator_arctic;

ccompare_arctic ::
  Maybe (SN_Order_Carrier.Arctic ->
          SN_Order_Carrier.Arctic -> Comparator.Order);
ccompare_arctic = Just compare_arctic;

instance Collection_Order.Ccompare SN_Order_Carrier.Arctic where {
  ccompare = ccompare_arctic;
};

equality_filtered ::
  forall a.
    (a -> a -> Bool) ->
      Argument_Filter.Filtered a -> Argument_Filter.Filtered a -> Bool;
equality_filtered eq_f (Argument_Filter.FPair x xa) (Argument_Filter.FPair y ya)
  = eq_f x y && Arith.equal_nat xa ya;

ceq_filtered ::
  forall a.
    (Collection_Eq.Ceq a) => Maybe (Argument_Filter.Filtered a ->
                                     Argument_Filter.Filtered a -> Bool);
ceq_filtered = (case Collection_Eq.ceq of {
                 Nothing -> Nothing;
                 Just eq_f -> Just (equality_filtered eq_f);
               });

instance (Collection_Eq.Ceq a) => Collection_Eq.Ceq (Argument_Filter.Filtered
              a) where {
  ceq = ceq_filtered;
};

set_impl_filtered ::
  forall a.
    (Set_Impl.Set_impl a) => Phantom_Type.Phantom (Argument_Filter.Filtered a)
                               Set_Impl.Set_impla;
set_impl_filtered =
  Phantom_Type.Phantom
    (Phantom_Type.of_phantom
      (Set_Impl.set_impl :: Phantom_Type.Phantom a Set_Impl.Set_impla));

instance (Set_Impl.Set_impl a) => Set_Impl.Set_impl (Argument_Filter.Filtered
              a) where {
  set_impl = set_impl_filtered;
};

ccompare_filtered ::
  forall a.
    (Collection_Order.Ccompare a) => Maybe (Argument_Filter.Filtered a ->
     Argument_Filter.Filtered a -> Comparator.Order);
ccompare_filtered =
  (case Collection_Order.ccompare of {
    Nothing -> Nothing;
    Just comp_f -> Just (Argument_Filter.comparator_filtered comp_f);
  });

instance (Collection_Order.Ccompare a) => Collection_Order.Ccompare (Argument_Filter.Filtered
                              a) where {
  ccompare = ccompare_filtered;
};

cEnum_l_poly ::
  forall a b.
    Maybe ([Linear_Polynomial.L_poly a b],
            ((Linear_Polynomial.L_poly a b -> Bool) -> Bool,
              (Linear_Polynomial.L_poly a b -> Bool) -> Bool));
cEnum_l_poly = Nothing;

instance Collection_Enum.Cenum (Linear_Polynomial.L_poly a b) where {
  cEnum = cEnum_l_poly;
};

ceq_sharp ::
  forall a.
    (Eq a) => Maybe (Cooperation_Program.Sharp a ->
                      Cooperation_Program.Sharp a -> Bool);
ceq_sharp = Just Cooperation_Program.equal_sharp;

instance (Eq a) => Collection_Eq.Ceq (Cooperation_Program.Sharp a) where {
  ceq = ceq_sharp;
};

set_impl_sharp ::
  forall a.
    Phantom_Type.Phantom (Cooperation_Program.Sharp a) Set_Impl.Set_impla;
set_impl_sharp = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Cooperation_Program.Sharp a) where {
  set_impl = set_impl_sharp;
};

cEnum_sharp ::
  forall a.
    Maybe ([Cooperation_Program.Sharp a],
            ((Cooperation_Program.Sharp a -> Bool) -> Bool,
              (Cooperation_Program.Sharp a -> Bool) -> Bool));
cEnum_sharp = Nothing;

instance Collection_Enum.Cenum (Cooperation_Program.Sharp a) where {
  cEnum = cEnum_sharp;
};

ccompare_sharp ::
  forall a.
    (Collection_Order.Ccompare a) => Maybe (Cooperation_Program.Sharp a ->
     Cooperation_Program.Sharp a -> Comparator.Order);
ccompare_sharp =
  (case Collection_Order.ccompare of {
    Nothing -> Nothing;
    Just comp_l -> Just (Cooperation_Program.comparator_sharp comp_l);
  });

instance (Collection_Order.Ccompare a) => Collection_Order.Ccompare (Cooperation_Program.Sharp
                              a) where {
  ccompare = ccompare_sharp;
};

mapping_impl_sharp ::
  forall a.
    Phantom_Type.Phantom (Cooperation_Program.Sharp a)
      Mapping_Impl.Mapping_impla;
mapping_impl_sharp = Phantom_Type.Phantom Mapping_Impl.Mapping_RBT;

instance Mapping_Impl.Mapping_impl (Cooperation_Program.Sharp a) where {
  mapping_impl = mapping_impl_sharp;
};

ceq_actxt ::
  forall a b.
    (Eq a,
      Eq b) => Maybe (Subterm_and_Context.Actxt a b ->
                       Subterm_and_Context.Actxt a b -> Bool);
ceq_actxt = Just Subterm_and_Context.equal_actxt;

instance (Eq a,
           Eq b) => Collection_Eq.Ceq (Subterm_and_Context.Actxt a b) where {
  ceq = ceq_actxt;
};

set_impl_actxt ::
  forall a b.
    Phantom_Type.Phantom (Subterm_and_Context.Actxt a b) Set_Impl.Set_impla;
set_impl_actxt = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (Subterm_and_Context.Actxt a b) where {
  set_impl = set_impl_actxt;
};

comparator_actxt ::
  forall a b.
    (a -> a -> Comparator.Order) ->
      (b -> b -> Comparator.Order) ->
        Subterm_and_Context.Actxt a b ->
          Subterm_and_Context.Actxt a b -> Comparator.Order;
comparator_actxt comp_f comp_a Subterm_and_Context.Hole Subterm_and_Context.Hole
  = Comparator.Eqa;
comparator_actxt comp_f comp_a Subterm_and_Context.Hole
  (Subterm_and_Context.More y ya yb yc) = Comparator.Lt;
comparator_actxt comp_f comp_a (Subterm_and_Context.More x xa xb xc)
  Subterm_and_Context.Hole = Comparator.Gt;
comparator_actxt comp_f comp_a (Subterm_and_Context.More x xa xb xc)
  (Subterm_and_Context.More y ya yb yc) =
  (case comp_f x y of {
    Comparator.Eqa ->
      (case Compare_Instances.comparator_list comp_a xa ya of {
        Comparator.Eqa ->
          (case comparator_actxt comp_f comp_a xb yb of {
            Comparator.Eqa -> Compare_Instances.comparator_list comp_a xc yc;
            Comparator.Lt -> Comparator.Lt;
            Comparator.Gt -> Comparator.Gt;
          });
        Comparator.Lt -> Comparator.Lt;
        Comparator.Gt -> Comparator.Gt;
      });
    Comparator.Lt -> Comparator.Lt;
    Comparator.Gt -> Comparator.Gt;
  });

compare_actxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Subterm_and_Context.Actxt a b ->
                              Subterm_and_Context.Actxt a b -> Comparator.Order;
compare_actxt = comparator_actxt Compare.compare Compare.compare;

ccompare_actxt ::
  forall a b.
    (Compare.Compare a,
      Compare.Compare b) => Maybe (Subterm_and_Context.Actxt a b ->
                                    Subterm_and_Context.Actxt a b ->
                                      Comparator.Order);
ccompare_actxt = Just compare_actxt;

instance (Compare.Compare a,
           Compare.Compare b) => Collection_Order.Ccompare (Subterm_and_Context.Actxt
                     a b) where {
  ccompare = ccompare_actxt;
};

ceq_location ::
  Maybe (Forbidden_Patterns.Location -> Forbidden_Patterns.Location -> Bool);
ceq_location = Just Forbidden_Patterns.equal_location;

instance Collection_Eq.Ceq Forbidden_Patterns.Location where {
  ceq = ceq_location;
};

set_impl_location ::
  Phantom_Type.Phantom Forbidden_Patterns.Location Set_Impl.Set_impla;
set_impl_location = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl Forbidden_Patterns.Location where {
  set_impl = set_impl_location;
};

comparator_location ::
  Forbidden_Patterns.Location ->
    Forbidden_Patterns.Location -> Comparator.Order;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.H = Comparator.Eqa;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.A = Comparator.Lt;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.B = Comparator.Lt;
comparator_location Forbidden_Patterns.H Forbidden_Patterns.R = Comparator.Lt;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.H = Comparator.Gt;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.A = Comparator.Eqa;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.B = Comparator.Lt;
comparator_location Forbidden_Patterns.A Forbidden_Patterns.R = Comparator.Lt;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.H = Comparator.Gt;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.A = Comparator.Gt;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.B = Comparator.Eqa;
comparator_location Forbidden_Patterns.B Forbidden_Patterns.R = Comparator.Lt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.H = Comparator.Gt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.A = Comparator.Gt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.B = Comparator.Gt;
comparator_location Forbidden_Patterns.R Forbidden_Patterns.R = Comparator.Eqa;

compare_location ::
  Forbidden_Patterns.Location ->
    Forbidden_Patterns.Location -> Comparator.Order;
compare_location = comparator_location;

ccompare_location ::
  Maybe (Forbidden_Patterns.Location ->
          Forbidden_Patterns.Location -> Comparator.Order);
ccompare_location = Just compare_location;

instance Collection_Order.Ccompare Forbidden_Patterns.Location where {
  ccompare = ccompare_location;
};

ceq_arctic_delta ::
  forall a.
    (Eq a) => Maybe (SN_Order_Carrier.Arctic_delta a ->
                      SN_Order_Carrier.Arctic_delta a -> Bool);
ceq_arctic_delta = Just SN_Order_Carrier.equal_arctic_delta;

instance (Eq a) => Collection_Eq.Ceq (SN_Order_Carrier.Arctic_delta a) where {
  ceq = ceq_arctic_delta;
};

set_impl_arctic_delta ::
  forall a.
    Phantom_Type.Phantom (SN_Order_Carrier.Arctic_delta a) Set_Impl.Set_impla;
set_impl_arctic_delta = Phantom_Type.Phantom Set_Impl.Set_RBT;

instance Set_Impl.Set_impl (SN_Order_Carrier.Arctic_delta a) where {
  set_impl = set_impl_arctic_delta;
};

cEnum_arctic_delta ::
  forall a.
    Maybe ([SN_Order_Carrier.Arctic_delta a],
            ((SN_Order_Carrier.Arctic_delta a -> Bool) -> Bool,
              (SN_Order_Carrier.Arctic_delta a -> Bool) -> Bool));
cEnum_arctic_delta = Nothing;

instance Collection_Enum.Cenum (SN_Order_Carrier.Arctic_delta a) where {
  cEnum = cEnum_arctic_delta;
};

comparator_arctic_delta ::
  forall a.
    (a -> a -> Comparator.Order) ->
      SN_Order_Carrier.Arctic_delta a ->
        SN_Order_Carrier.Arctic_delta a -> Comparator.Order;
comparator_arctic_delta comp_a SN_Order_Carrier.MinInfty_delta
  SN_Order_Carrier.MinInfty_delta = Comparator.Eqa;
comparator_arctic_delta comp_a SN_Order_Carrier.MinInfty_delta
  (SN_Order_Carrier.Num_arc_delta y) = Comparator.Lt;
comparator_arctic_delta comp_a (SN_Order_Carrier.Num_arc_delta x)
  SN_Order_Carrier.MinInfty_delta = Comparator.Gt;
comparator_arctic_delta comp_a (SN_Order_Carrier.Num_arc_delta x)
  (SN_Order_Carrier.Num_arc_delta y) = comp_a x y;

compare_arctic_delta ::
  forall a.
    (Compare.Compare a) => SN_Order_Carrier.Arctic_delta a ->
                             SN_Order_Carrier.Arctic_delta a ->
                               Comparator.Order;
compare_arctic_delta = comparator_arctic_delta Compare.compare;

ccompare_arctic_delta ::
  forall a.
    (Compare.Compare a) => Maybe (SN_Order_Carrier.Arctic_delta a ->
                                   SN_Order_Carrier.Arctic_delta a ->
                                     Comparator.Order);
ccompare_arctic_delta = Just compare_arctic_delta;

instance (Compare.Compare a) => Collection_Order.Ccompare (SN_Order_Carrier.Arctic_delta
                    a) where {
  ccompare = ccompare_arctic_delta;
};

ceq_ty :: Maybe (Integer_Arithmetic.Ty -> Integer_Arithmetic.Ty -> Bool);
ceq_ty = Just Integer_Arithmetic.equal_ty;

instance Collection_Eq.Ceq Integer_Arithmetic.Ty where {
  ceq = ceq_ty;
};

comparator_ty ::
  Integer_Arithmetic.Ty -> Integer_Arithmetic.Ty -> Comparator.Order;
comparator_ty Integer_Arithmetic.BoolT Integer_Arithmetic.BoolT =
  Comparator.Eqa;
comparator_ty Integer_Arithmetic.BoolT Integer_Arithmetic.IntT = Comparator.Lt;
comparator_ty Integer_Arithmetic.IntT Integer_Arithmetic.BoolT = Comparator.Gt;
comparator_ty Integer_Arithmetic.IntT Integer_Arithmetic.IntT = Comparator.Eqa;

ccompare_ty ::
  Maybe (Integer_Arithmetic.Ty -> Integer_Arithmetic.Ty -> Comparator.Order);
ccompare_ty = Just comparator_ty;

instance Collection_Order.Ccompare Integer_Arithmetic.Ty where {
  ccompare = ccompare_ty;
};

comparator_sig ::
  Integer_Arithmetic.Sig -> Integer_Arithmetic.Sig -> Comparator.Order;
comparator_sig Integer_Arithmetic.LessF Integer_Arithmetic.LessF =
  Comparator.Eqa;
comparator_sig Integer_Arithmetic.LessF Integer_Arithmetic.LeF = Comparator.Lt;
comparator_sig Integer_Arithmetic.LessF (Integer_Arithmetic.SumF y) =
  Comparator.Lt;
comparator_sig Integer_Arithmetic.LessF (Integer_Arithmetic.ConstF ya) =
  Comparator.Lt;
comparator_sig Integer_Arithmetic.LessF (Integer_Arithmetic.ProdF yb) =
  Comparator.Lt;
comparator_sig Integer_Arithmetic.LessF Integer_Arithmetic.EqF = Comparator.Lt;
comparator_sig Integer_Arithmetic.LeF Integer_Arithmetic.LessF = Comparator.Gt;
comparator_sig Integer_Arithmetic.LeF Integer_Arithmetic.LeF = Comparator.Eqa;
comparator_sig Integer_Arithmetic.LeF (Integer_Arithmetic.SumF y) =
  Comparator.Lt;
comparator_sig Integer_Arithmetic.LeF (Integer_Arithmetic.ConstF ya) =
  Comparator.Lt;
comparator_sig Integer_Arithmetic.LeF (Integer_Arithmetic.ProdF yb) =
  Comparator.Lt;
comparator_sig Integer_Arithmetic.LeF Integer_Arithmetic.EqF = Comparator.Lt;
comparator_sig (Integer_Arithmetic.SumF x) Integer_Arithmetic.LessF =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.SumF x) Integer_Arithmetic.LeF =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.SumF x) (Integer_Arithmetic.SumF y) =
  Comparator.comparator_of x y;
comparator_sig (Integer_Arithmetic.SumF x) (Integer_Arithmetic.ConstF ya) =
  Comparator.Lt;
comparator_sig (Integer_Arithmetic.SumF x) (Integer_Arithmetic.ProdF yb) =
  Comparator.Lt;
comparator_sig (Integer_Arithmetic.SumF x) Integer_Arithmetic.EqF =
  Comparator.Lt;
comparator_sig (Integer_Arithmetic.ConstF x) Integer_Arithmetic.LessF =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.ConstF x) Integer_Arithmetic.LeF =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.ConstF x) (Integer_Arithmetic.SumF y) =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.ConstF x) (Integer_Arithmetic.ConstF ya) =
  Comparator.comparator_of x ya;
comparator_sig (Integer_Arithmetic.ConstF x) (Integer_Arithmetic.ProdF yb) =
  Comparator.Lt;
comparator_sig (Integer_Arithmetic.ConstF x) Integer_Arithmetic.EqF =
  Comparator.Lt;
comparator_sig (Integer_Arithmetic.ProdF x) Integer_Arithmetic.LessF =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.ProdF x) Integer_Arithmetic.LeF =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.ProdF x) (Integer_Arithmetic.SumF y) =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.ProdF x) (Integer_Arithmetic.ConstF ya) =
  Comparator.Gt;
comparator_sig (Integer_Arithmetic.ProdF x) (Integer_Arithmetic.ProdF yb) =
  Comparator.comparator_of x yb;
comparator_sig (Integer_Arithmetic.ProdF x) Integer_Arithmetic.EqF =
  Comparator.Lt;
comparator_sig Integer_Arithmetic.EqF Integer_Arithmetic.LessF = Comparator.Gt;
comparator_sig Integer_Arithmetic.EqF Integer_Arithmetic.LeF = Comparator.Gt;
comparator_sig Integer_Arithmetic.EqF (Integer_Arithmetic.SumF y) =
  Comparator.Gt;
comparator_sig Integer_Arithmetic.EqF (Integer_Arithmetic.ConstF ya) =
  Comparator.Gt;
comparator_sig Integer_Arithmetic.EqF (Integer_Arithmetic.ProdF yb) =
  Comparator.Gt;
comparator_sig Integer_Arithmetic.EqF Integer_Arithmetic.EqF = Comparator.Eqa;

ccompare_sig ::
  Maybe (Integer_Arithmetic.Sig -> Integer_Arithmetic.Sig -> Comparator.Order);
ccompare_sig = Just comparator_sig;

instance Collection_Order.Ccompare Integer_Arithmetic.Sig where {
  ccompare = ccompare_sig;
};

set_impl_ty :: Phantom_Type.Phantom Integer_Arithmetic.Ty Set_Impl.Set_impla;
set_impl_ty = Phantom_Type.Phantom Set_Impl.Set_RBT;

}
