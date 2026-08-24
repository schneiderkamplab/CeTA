(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Guarded_List_Measure
  imports CSR_Checker_Extensions.CSR_Minimal_CSDP_Proofs
begin

text \<open>
  Semantic ranks for the common membership-guarded list pattern used by
  context-sensitive specifications.  The three mutually recursive sorts are
  kept semantic: the same constructor may build a finite list or a possibly
  infinite list depending on the demanded result sort.  Every recursive call
  is on a proper syntactic subterm, so the rank is executable and independent
  of a particular benchmark spelling.
\<close>

datatype csr_guard_sort = Guard_Nat | Guard_List | Guard_IList

datatype ('v) csr_guard_form = Guard_Form
  "('v \<times> csr_guard_sort) list"
  "('v \<times> csr_guard_sort) list"
  nat

text \<open>
  Administrative symbols produced by the standard conditional-rule
  compilation are erased to the constructor expression they resume.  This
  makes the semantic rank stable across U11/U21/U31 steps without assigning
  an ad-hoc value to a guard term.
\<close>

fun csr_guard_erase_admin ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
   'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v) term"
where
  "csr_guard_erase_admin u11 u21 u31 su len ni co ta (Var x) = Var x"
| "csr_guard_erase_admin u11 u21 u31 su len ni co ta (Fun f ts) =
    (if f = u11 \<and> length ts = 2 then
       Fun su [Fun len [csr_guard_erase_admin u11 u21 u31 su len ni co ta (ts ! 1)]]
     else if f = u21 \<and> length ts = 1 then Fun ni []
     else if f = u31 \<and> length ts = 4 then
       Fun co
         [csr_guard_erase_admin u11 u21 u31 su len ni co ta (ts ! 3),
          Fun ta
            [csr_guard_erase_admin u11 u21 u31 su len ni co ta (ts ! 2),
             csr_guard_erase_admin u11 u21 u31 su len ni co ta (ts ! 1)]]
     else Fun f (map (csr_guard_erase_admin u11 u21 u31 su len ni co ta) ts))"

lemma csr_guard_erase_admin_subst:
  "csr_guard_erase_admin u11 u21 u31 su len ni co ta (t \<cdot> \<sigma>) =
    csr_guard_erase_admin u11 u21 u31 su len ni co ta t \<cdot>
      (\<lambda>x. csr_guard_erase_admin u11 u21 u31 su len ni co ta (\<sigma> x))"
proof (induction t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  then show ?case by (simp split: if_splits)
qed

lemma csr_guard_erase_admin_u11:
  assumes distinct: "distinct [u11,u21,u31,su,len,ni,co,ta]"
  shows "csr_guard_erase_admin u11 u21 u31 su len ni co ta
      (Fun u11 [q,l]) =
    csr_guard_erase_admin u11 u21 u31 su len ni co ta
      (Fun su [Fun len [l]])"
  using distinct by (simp; fastforce)

lemma csr_guard_erase_admin_u21:
  assumes distinct: "distinct [u11,u21,u31,su,len,ni,co,ta]"
  shows "csr_guard_erase_admin u11 u21 u31 su len ni co ta
      (Fun u21 [q]) =
    csr_guard_erase_admin u11 u21 u31 su len ni co ta (Fun ni [])"
  using distinct by (simp; fastforce)

lemma csr_guard_erase_admin_u31:
  assumes distinct: "distinct [u11,u21,u31,su,len,ni,co,ta]"
  shows "csr_guard_erase_admin u11 u21 u31 su len ni co ta
      (Fun u31 [q,il,m,n]) =
    csr_guard_erase_admin u11 u21 u31 su len ni co ta
      (Fun co [n, Fun ta [m,il]])"
  using distinct by (simp; fastforce)

fun csr_guard_form_requirements where
  "csr_guard_form_requirements (Guard_Form req cs c) = req"

fun csr_guard_form_coefficients where
  "csr_guard_form_coefficients (Guard_Form req cs c) = cs"

fun csr_guard_form_constant where
  "csr_guard_form_constant (Guard_Form req cs c) = c"

text \<open>
  A symbolic form contains, in order, the variable-sort requirements needed
  for definedness, the variables occurring with coefficient one in the rank,
  and the natural constant.  Repetition represents larger coefficients.  The
  distinction between requirements and coefficients matters for constructor
  heads: a list element must be a natural although its numerical value does
  not contribute to list length.
\<close>

fun csr_guard_symbolic_rank ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
   'f \<Rightarrow> 'f \<Rightarrow> csr_guard_sort \<Rightarrow>
   ('f,'v) term \<Rightarrow> 'v csr_guard_form option"
where
  "csr_guard_symbolic_rank z su len ni co ta zs A (Var x) =
    Some (Guard_Form [(x,A)] [(x,A)] 0)"
| "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (Fun f ts) =
    (if f = z \<and> ts = [] then Some (Guard_Form [] [] 0)
     else if f = su \<and> length ts = 1 then
       (case csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some (Guard_Form req cs c) \<Rightarrow>
            Some (Guard_Form req cs (Suc c)))
     else if f = len \<and> length ts = 1 then
       csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 0)
     else None)"
| "csr_guard_symbolic_rank z su len ni co ta zs Guard_List (Fun f ts) =
    (if f = ni \<and> ts = [] then Some (Guard_Form [] [] 0)
     else if f = co \<and> length ts = 2 then
       (case (csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0),
              csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 1)) of
          (Some (Guard_Form reqn coeffn cn),
           Some (Guard_Form reql coeffl cl)) \<Rightarrow>
             Some (Guard_Form (reqn @ reql) coeffl (Suc cl))
        | _ \<Rightarrow> None)
     else if f = ta \<and> length ts = 2 then
       (case (csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0),
              csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (ts ! 1)) of
          (Some (Guard_Form reqn coeffn cn),
           Some (Guard_Form reqi coeffi ci)) \<Rightarrow>
             Some (Guard_Form (reqn @ reqi) coeffn cn)
        | _ \<Rightarrow> None)
     else None)"
| "csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (Fun f ts) =
    (if f = zs \<and> ts = [] then Some (Guard_Form [] [] 0)
     else if f = co \<and> length ts = 2 then
       (case (csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0),
              csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (ts ! 1)) of
          (Some (Guard_Form reqn coeffn cn),
           Some (Guard_Form reqi coeffi ci)) \<Rightarrow>
             Some (Guard_Form (reqn @ reqi) [] 0)
        | _ \<Rightarrow> None)
     else if f = ni \<and> ts = [] then Some (Guard_Form [] [] 0)
     else if f = ta \<and> length ts = 2 then
       (case (csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0),
              csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (ts ! 1)) of
          (Some (Guard_Form reqn coeffn cn),
           Some (Guard_Form reqi coeffi ci)) \<Rightarrow>
             Some (Guard_Form (reqn @ reqi) [] 0)
        | _ \<Rightarrow> None)
     else None)"

fun csr_guard_rank ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
   'f \<Rightarrow> 'f \<Rightarrow> csr_guard_sort \<Rightarrow>
   ('f,'v) term \<Rightarrow> nat option"
where
  "csr_guard_rank z su len ni co ta zs Guard_Nat (Var x) = None"
| "csr_guard_rank z su len ni co ta zs Guard_Nat (Fun f ts) =
    (if f = z \<and> ts = [] then Some 0
     else if f = su \<and> length ts = 1 then
       map_option Suc
         (csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0))
     else if f = len \<and> length ts = 1 then
       csr_guard_rank z su len ni co ta zs Guard_List (ts ! 0)
     else None)"
| "csr_guard_rank z su len ni co ta zs Guard_List (Var x) = None"
| "csr_guard_rank z su len ni co ta zs Guard_List (Fun f ts) =
    (if f = ni \<and> ts = [] then Some 0
     else if f = co \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow> map_option Suc
            (csr_guard_rank z su len ni co ta zs Guard_List (ts ! 1)))
     else if f = ta \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow>
            (case csr_guard_rank z su len ni co ta zs Guard_IList (ts ! 1) of
               None \<Rightarrow> None
             | Some m \<Rightarrow> Some n))
     else None)"
| "csr_guard_rank z su len ni co ta zs Guard_IList (Var x) = None"
| "csr_guard_rank z su len ni co ta zs Guard_IList (Fun f ts) =
    (if f = zs \<and> ts = [] then Some 0
     else if f = co \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow>
            (case csr_guard_rank z su len ni co ta zs Guard_IList (ts ! 1) of
               None \<Rightarrow> None
             | Some m \<Rightarrow> Some 0))
     else if f = ni \<and> ts = [] then Some 0
     else if f = ta \<and> length ts = 2 then
       (case csr_guard_rank z su len ni co ta zs Guard_Nat (ts ! 0) of
          None \<Rightarrow> None
        | Some n \<Rightarrow>
            (case csr_guard_rank z su len ni co ta zs Guard_IList (ts ! 1) of
               None \<Rightarrow> None
             | Some m \<Rightarrow> Some 0))
     else None)"

definition csr_guard_erased_rank where
  "csr_guard_erased_rank u11 u21 u31 z su len ni co ta zs A t =
    csr_guard_rank z su len ni co ta zs A
      (csr_guard_erase_admin u11 u21 u31 su len ni co ta t)"

definition csr_guard_erased_symbolic_rank where
  "csr_guard_erased_symbolic_rank u11 u21 u31 z su len ni co ta zs A t =
    csr_guard_symbolic_rank z su len ni co ta zs A
      (csr_guard_erase_admin u11 u21 u31 su len ni co ta t)"

fun csr_guard_form_value ::
  "(('v \<times> csr_guard_sort) \<Rightarrow> nat) \<Rightarrow>
   'v csr_guard_form \<Rightarrow> nat"
where
  "csr_guard_form_value \<rho> (Guard_Form req cs c) =
    c + sum_list (map \<rho> cs)"

definition csr_guard_requirements_realized where
  "csr_guard_requirements_realized z su len ni co ta zs \<sigma> \<rho> req \<longleftrightarrow>
    (\<forall>x A. (x,A) \<in> set req \<longrightarrow>
      csr_guard_rank z su len ni co ta zs A (\<sigma> x) = Some (\<rho> (x,A)))"

lemma csr_guard_requirements_realized_append [simp]:
  "csr_guard_requirements_realized z su len ni co ta zs \<sigma> \<rho> (xs @ ys) \<longleftrightarrow>
    csr_guard_requirements_realized z su len ni co ta zs \<sigma> \<rho> xs \<and>
    csr_guard_requirements_realized z su len ni co ta zs \<sigma> \<rho> ys"
  unfolding csr_guard_requirements_realized_def by auto

lemma csr_guard_symbolic_rank_Var_sound:
  assumes form:
    "csr_guard_symbolic_rank z su len ni co ta zs A (Var x) = Some F"
    and realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements F)"
  shows "csr_guard_rank z su len ni co ta zs A (Var x \<cdot> \<sigma>) =
    Some (csr_guard_form_value \<rho> F)"
  using form realized
  unfolding csr_guard_requirements_realized_def by auto

lemma csr_guard_symbolic_rank_sound:
  assumes distinct: "distinct [z,su,len,ni,co,ta,zs]"
    and symbolic:
    "csr_guard_symbolic_rank z su len ni co ta zs A t = Some F"
    and realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements F)"
  shows "csr_guard_rank z su len ni co ta zs A (t \<cdot> \<sigma>) =
    Some (csr_guard_form_value \<rho> F)"
  using symbolic realized
proof (induction t arbitrary: A F)
  case (Var x)
  then show ?case
    unfolding csr_guard_requirements_realized_def by auto
next
  case (Fun f ts)
  show ?case
  proof (cases A)
    case Guard_Nat
    have symbolic':
      "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (Fun f ts) = Some F"
      using Fun.prems(1) Guard_Nat by simp
    consider
        (zero) "f = z" "ts = []" "F = Guard_Form [] [] 0"
      | (succ) req cs c where
          "f = su" "length ts = 1"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0) =
             Some (Guard_Form req cs c)"
          "F = Guard_Form req cs (Suc c)"
      | (length) "f = len" "length ts = 1"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 0) = Some F"
      using symbolic'
      by (auto simp: csr_guard_symbolic_rank.simps
          split: if_splits option.splits csr_guard_form.splits)
    then show ?thesis
    proof cases
      case zero
      then show ?thesis unfolding Guard_Nat by simp
    next
      case (succ req cs c)
      have mem: "ts ! 0 \<in> set ts" using succ(2) by simp
      have realized_child: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> req"
        using Fun.prems(2) succ(4) by simp
      have child: "csr_guard_rank z su len ni co ta zs Guard_Nat
          (ts ! 0 \<cdot> \<sigma>) = Some (c + sum_list (map \<rho> cs))"
        using Fun.IH[OF mem succ(3)] realized_child by simp
      show ?thesis unfolding Guard_Nat using succ child distinct by simp
    next
      case length
      have mem: "ts ! 0 \<in> set ts" using length(2) by simp
      have child: "csr_guard_rank z su len ni co ta zs Guard_List
          (ts ! 0 \<cdot> \<sigma>) = Some (csr_guard_form_value \<rho> F)"
        using Fun.IH[OF mem length(3)] Fun.prems(2) by simp
      show ?thesis unfolding Guard_Nat using length child distinct by fastforce
    qed
  next
    case Guard_List
    have symbolic':
      "csr_guard_symbolic_rank z su len ni co ta zs Guard_List (Fun f ts) = Some F"
      using Fun.prems(1) Guard_List by simp
    consider
        (nil) "f = ni" "ts = []" "F = Guard_Form [] [] 0"
      | (cons) reqn coeffn cn reql coeffl cl where
          "f = co" "length ts = 2"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0) =
             Some (Guard_Form reqn coeffn cn)"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 1) =
             Some (Guard_Form reql coeffl cl)"
          "F = Guard_Form (reqn @ reql) coeffl (Suc cl)"
      | (take) reqn coeffn cn reqi coeffi ci where
          "f = ta" "length ts = 2"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0) =
             Some (Guard_Form reqn coeffn cn)"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (ts ! 1) =
             Some (Guard_Form reqi coeffi ci)"
          "F = Guard_Form (reqn @ reqi) coeffn cn"
      using symbolic'
      by (auto simp: csr_guard_symbolic_rank.simps
          split: if_splits option.splits csr_guard_form.splits prod.splits)
    then show ?thesis
    proof cases
      case nil
      then show ?thesis unfolding Guard_List by simp
    next
      case (cons reqn coeffn cn reql coeffl cl)
      have mem0: "ts ! 0 \<in> set ts" and mem1: "ts ! 1 \<in> set ts"
        using cons(2) by auto
      have realized_n: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reqn"
        and realized_l: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reql"
        using Fun.prems(2) cons(5) by simp_all
      have child_n: "csr_guard_rank z su len ni co ta zs Guard_Nat
          (ts ! 0 \<cdot> \<sigma>) = Some (cn + sum_list (map \<rho> coeffn))"
        using Fun.IH[OF mem0 cons(3)] realized_n by simp
      have child_l: "csr_guard_rank z su len ni co ta zs Guard_List
          (ts ! 1 \<cdot> \<sigma>) = Some (cl + sum_list (map \<rho> coeffl))"
        using Fun.IH[OF mem1 cons(4)] realized_l by simp
      show ?thesis unfolding Guard_List using cons child_n child_l distinct by fastforce
    next
      case (take reqn coeffn cn reqi coeffi ci)
      have mem0: "ts ! 0 \<in> set ts" and mem1: "ts ! 1 \<in> set ts"
        using take(2) by auto
      have realized_n: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reqn"
        and realized_i: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reqi"
        using Fun.prems(2) take(5) by simp_all
      have child_n: "csr_guard_rank z su len ni co ta zs Guard_Nat
          (ts ! 0 \<cdot> \<sigma>) = Some (cn + sum_list (map \<rho> coeffn))"
        using Fun.IH[OF mem0 take(3)] realized_n by simp
      have child_i: "csr_guard_rank z su len ni co ta zs Guard_IList
          (ts ! 1 \<cdot> \<sigma>) = Some (ci + sum_list (map \<rho> coeffi))"
        using Fun.IH[OF mem1 take(4)] realized_i by simp
      show ?thesis unfolding Guard_List using take child_n child_i distinct by fastforce
    qed
  next
    case Guard_IList
    have symbolic':
      "csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (Fun f ts) = Some F"
      using Fun.prems(1) Guard_IList by simp
    consider
        (zeros) "f = zs" "ts = []" "F = Guard_Form [] [] 0"
      | (cons) reqn coeffn cn reqi coeffi ci where
          "f = co" "length ts = 2"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0) =
             Some (Guard_Form reqn coeffn cn)"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (ts ! 1) =
             Some (Guard_Form reqi coeffi ci)"
          "F = Guard_Form (reqn @ reqi) [] 0"
      | (nil) "f = ni" "ts = []" "F = Guard_Form [] [] 0"
      | (take) reqn coeffn cn reqi coeffi ci where
          "f = ta" "length ts = 2"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0) =
             Some (Guard_Form reqn coeffn cn)"
          "csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (ts ! 1) =
             Some (Guard_Form reqi coeffi ci)"
          "F = Guard_Form (reqn @ reqi) [] 0"
      using symbolic'
      by (auto simp: csr_guard_symbolic_rank.simps
          split: if_splits option.splits csr_guard_form.splits prod.splits)
    then show ?thesis
    proof cases
      case zeros
      then show ?thesis unfolding Guard_IList by simp
    next
      case (cons reqn coeffn cn reqi coeffi ci)
      have mem0: "ts ! 0 \<in> set ts" and mem1: "ts ! 1 \<in> set ts"
        using cons(2) by auto
      have realized_n: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reqn"
        and realized_i: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reqi"
        using Fun.prems(2) cons(5) by simp_all
      have child_n: "\<exists>n. csr_guard_rank z su len ni co ta zs Guard_Nat
          (ts ! 0 \<cdot> \<sigma>) = Some n"
        using Fun.IH[OF mem0 cons(3)] realized_n by fastforce
      have child_i: "\<exists>n. csr_guard_rank z su len ni co ta zs Guard_IList
          (ts ! 1 \<cdot> \<sigma>) = Some n"
        using Fun.IH[OF mem1 cons(4)] realized_i by fastforce
      show ?thesis unfolding Guard_IList using cons child_n child_i distinct by fastforce
    next
      case nil
      then show ?thesis unfolding Guard_IList using distinct by simp
    next
      case (take reqn coeffn cn reqi coeffi ci)
      have mem0: "ts ! 0 \<in> set ts" and mem1: "ts ! 1 \<in> set ts"
        using take(2) by auto
      have realized_n: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reqn"
        and realized_i: "csr_guard_requirements_realized
          z su len ni co ta zs \<sigma> \<rho> reqi"
        using Fun.prems(2) take(5) by simp_all
      have child_n: "\<exists>n. csr_guard_rank z su len ni co ta zs Guard_Nat
          (ts ! 0 \<cdot> \<sigma>) = Some n"
        using Fun.IH[OF mem0 take(3)] realized_n by fastforce
      have child_i: "\<exists>n. csr_guard_rank z su len ni co ta zs Guard_IList
          (ts ! 1 \<cdot> \<sigma>) = Some n"
        using Fun.IH[OF mem1 take(4)] realized_i by fastforce
      show ?thesis unfolding Guard_IList using take child_n child_i distinct by fastforce
    qed
  qed
qed

lemma csr_guard_erased_symbolic_rank_sound:
  assumes distinct: "distinct [z,su,len,ni,co,ta,zs]"
    and symbolic:
      "csr_guard_erased_symbolic_rank u11 u21 u31 z su len ni co ta zs A t =
        Some F"
    and realized: "csr_guard_requirements_realized z su len ni co ta zs
      (\<lambda>x. csr_guard_erase_admin u11 u21 u31 su len ni co ta (\<sigma> x))
      \<rho> (csr_guard_form_requirements F)"
  shows "csr_guard_erased_rank u11 u21 u31 z su len ni co ta zs A (t \<cdot> \<sigma>) =
    Some (csr_guard_form_value \<rho> F)"
proof -
  have symbolic': "csr_guard_symbolic_rank z su len ni co ta zs A
      (csr_guard_erase_admin u11 u21 u31 su len ni co ta t) = Some F"
    using symbolic unfolding csr_guard_erased_symbolic_rank_def .
  have sound: "csr_guard_rank z su len ni co ta zs A
      (csr_guard_erase_admin u11 u21 u31 su len ni co ta t \<cdot>
        (\<lambda>x. csr_guard_erase_admin u11 u21 u31 su len ni co ta (\<sigma> x))) =
      Some (csr_guard_form_value \<rho> F)"
    by (rule csr_guard_symbolic_rank_sound[OF distinct symbolic' realized])
  show ?thesis
    unfolding csr_guard_erased_rank_def csr_guard_erase_admin_subst
    by (rule sound)
qed

fun csr_guard_coefficients_le where
  "csr_guard_coefficients_le [] ys = True"
| "csr_guard_coefficients_le (x # xs) ys =
    (x \<in> set ys \<and> csr_guard_coefficients_le xs (remove1 x ys))"

lemma csr_guard_coefficients_le_sum:
  fixes \<rho> :: "'a \<Rightarrow> nat"
  assumes "csr_guard_coefficients_le xs ys"
  shows "sum_list (map \<rho> xs) \<le> sum_list (map \<rho> ys)"
  using assms
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then have x: "x \<in> set ys"
    and rest: "csr_guard_coefficients_le xs (remove1 x ys)"
    by simp_all
  have ih: "sum_list (map \<rho> xs) \<le>
      sum_list (map \<rho> (remove1 x ys))"
    by (rule Cons.IH[OF rest])
  have decompose: "sum_list (map \<rho> ys) =
      \<rho> x + sum_list (map \<rho> (remove1 x ys))"
    by (rule sum_list_map_remove1[OF x])
  show ?case using ih decompose by simp
qed

fun csr_guard_form_ge where
  "csr_guard_form_ge (Guard_Form req_l cs_l c_l)
      (Guard_Form req_r cs_r c_r) =
    (set req_r \<subseteq> set req_l \<and>
     csr_guard_coefficients_le cs_r cs_l \<and> c_r \<le> c_l)"

fun csr_guard_form_gt where
  "csr_guard_form_gt (Guard_Form req_l cs_l c_l)
      (Guard_Form req_r cs_r c_r) =
    (set req_r \<subseteq> set req_l \<and>
     csr_guard_coefficients_le cs_r cs_l \<and> c_r < c_l)"

lemma csr_guard_requirements_realized_mono:
  assumes realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> req_l"
    and subset: "set req_r \<subseteq> set req_l"
  shows "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> req_r"
  using realized subset unfolding csr_guard_requirements_realized_def by auto

lemma csr_guard_form_ge_value:
  assumes "csr_guard_form_ge F G"
  shows "csr_guard_form_value \<rho> F \<ge> csr_guard_form_value \<rho> G"
proof (cases F; cases G)
  fix req_l cs_l c_l req_r cs_r c_r
  assume F: "F = Guard_Form req_l cs_l c_l"
    and G: "G = Guard_Form req_r cs_r c_r"
  have constants: "c_r \<le> c_l" and coefficients:
      "csr_guard_coefficients_le cs_r cs_l"
    using assms unfolding F G by simp_all
  have sums: "sum_list (map \<rho> cs_r) \<le> sum_list (map \<rho> cs_l)"
    by (rule csr_guard_coefficients_le_sum[OF coefficients])
  show ?thesis unfolding F G using add_le_mono[OF constants sums] by simp
qed

lemma csr_guard_form_gt_value:
  assumes "csr_guard_form_gt F G"
  shows "csr_guard_form_value \<rho> F > csr_guard_form_value \<rho> G"
proof (cases F; cases G)
  fix req_l cs_l c_l req_r cs_r c_r
  assume F: "F = Guard_Form req_l cs_l c_l"
    and G: "G = Guard_Form req_r cs_r c_r"
  have constants: "c_r < c_l" and coefficients:
      "csr_guard_coefficients_le cs_r cs_l"
    using assms unfolding F G by simp_all
  have sums: "sum_list (map \<rho> cs_r) \<le> sum_list (map \<rho> cs_l)"
    by (rule csr_guard_coefficients_le_sum[OF coefficients])
  show ?thesis unfolding F G using add_less_le_mono[OF constants sums] by simp
qed

lemma csr_guard_symbolic_rank_ge_sound:
  assumes distinct: "distinct [z,su,len,ni,co,ta,zs]"
    and lhs: "csr_guard_symbolic_rank z su len ni co ta zs A l = Some F"
    and rhs: "csr_guard_symbolic_rank z su len ni co ta zs A r = Some G"
    and orient: "csr_guard_form_ge F G"
    and realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements F)"
  obtains m n where
    "csr_guard_rank z su len ni co ta zs A (l \<cdot> \<sigma>) = Some m"
    "csr_guard_rank z su len ni co ta zs A (r \<cdot> \<sigma>) = Some n"
    "m \<ge> n"
proof
  have req_subset: "set (csr_guard_form_requirements G) \<subseteq>
      set (csr_guard_form_requirements F)"
    using orient by (cases F; cases G) simp
  have realized_r: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements G)"
    by (rule csr_guard_requirements_realized_mono[OF realized req_subset])
  show "csr_guard_rank z su len ni co ta zs A (l \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> F)"
    by (rule csr_guard_symbolic_rank_sound[OF distinct lhs realized])
  show "csr_guard_rank z su len ni co ta zs A (r \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> G)"
    by (rule csr_guard_symbolic_rank_sound[OF distinct rhs realized_r])
  show "csr_guard_form_value \<rho> F \<ge> csr_guard_form_value \<rho> G"
    by (rule csr_guard_form_ge_value[OF orient])
qed

lemma csr_guard_symbolic_rank_gt_sound:
  assumes distinct: "distinct [z,su,len,ni,co,ta,zs]"
    and lhs: "csr_guard_symbolic_rank z su len ni co ta zs A l = Some F"
    and rhs: "csr_guard_symbolic_rank z su len ni co ta zs A r = Some G"
    and orient: "csr_guard_form_gt F G"
    and realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements F)"
  obtains m n where
    "csr_guard_rank z su len ni co ta zs A (l \<cdot> \<sigma>) = Some m"
    "csr_guard_rank z su len ni co ta zs A (r \<cdot> \<sigma>) = Some n"
    "m > n"
proof
  have req_subset: "set (csr_guard_form_requirements G) \<subseteq>
      set (csr_guard_form_requirements F)"
    using orient by (cases F; cases G) simp
  have realized_r: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements G)"
    by (rule csr_guard_requirements_realized_mono[OF realized req_subset])
  show "csr_guard_rank z su len ni co ta zs A (l \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> F)"
    by (rule csr_guard_symbolic_rank_sound[OF distinct lhs realized])
  show "csr_guard_rank z su len ni co ta zs A (r \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> G)"
    by (rule csr_guard_symbolic_rank_sound[OF distinct rhs realized_r])
  show "csr_guard_form_value \<rho> F > csr_guard_form_value \<rho> G"
    by (rule csr_guard_form_gt_value[OF orient])
qed

text \<open>
  The guarded list measure is observed at the two marked roots of the hard
  component.  Both marked calls denote the length of their list argument;
  the surrounding guard argument of the marked U-call is deliberately
  ignored by the numerical measure but remains available to the later
  recognizer check.
\<close>

fun csr_guard_pair_symbolic_rank where
  "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs (Var x) = None"
| "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs (Fun f ts) =
    (if f = u11s \<and> length ts = 2 then
       csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 1)
     else if f = lens \<and> length ts = 1 then
       csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 0)
     else None)"

fun csr_guard_pair_rank where
  "csr_guard_pair_rank u11s lens z su len ni co ta zs (Var x) = None"
| "csr_guard_pair_rank u11s lens z su len ni co ta zs (Fun f ts) =
    (if f = u11s \<and> length ts = 2 then
       csr_guard_rank z su len ni co ta zs Guard_List (ts ! 1)
     else if f = lens \<and> length ts = 1 then
       csr_guard_rank z su len ni co ta zs Guard_List (ts ! 0)
     else None)"

lemma csr_guard_pair_symbolic_rank_sound:
  assumes distinct: "distinct [z,su,len,ni,co,ta,zs]"
    and symbolic:
      "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs t = Some F"
    and realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements F)"
  shows "csr_guard_pair_rank u11s lens z su len ni co ta zs (t \<cdot> \<sigma>) =
    Some (csr_guard_form_value \<rho> F)"
proof (cases t)
  case (Var x)
  then show ?thesis using symbolic by simp
next
  case (Fun f ts)
  consider
      (u11) "f = u11s" "length ts = 2"
        "csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 1) = Some F"
    | (length) "\<not> (f = u11s \<and> length ts = 2)"
        "f = lens" "length ts = 1"
        "csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 0) = Some F"
    using symbolic unfolding Fun
    by (auto split: if_splits)
  then show ?thesis
  proof cases
    case u11
    have child: "csr_guard_rank z su len ni co ta zs Guard_List
        (ts ! 1 \<cdot> \<sigma>) = Some (csr_guard_form_value \<rho> F)"
      by (rule csr_guard_symbolic_rank_sound[OF distinct u11(3) realized])
    show ?thesis unfolding Fun using u11 child by simp
  next
    case length
    have child: "csr_guard_rank z su len ni co ta zs Guard_List
        (ts ! 0 \<cdot> \<sigma>) = Some (csr_guard_form_value \<rho> F)"
      by (rule csr_guard_symbolic_rank_sound[OF distinct length(4) realized])
    show ?thesis unfolding Fun using length child by simp
  qed
qed

lemma csr_guard_pair_symbolic_rank_ge_sound:
  assumes distinct: "distinct [z,su,len,ni,co,ta,zs]"
    and lhs: "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs l = Some F"
    and rhs: "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs r = Some G"
    and orient: "csr_guard_form_ge F G"
    and realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements F)"
  obtains m n where
    "csr_guard_pair_rank u11s lens z su len ni co ta zs (l \<cdot> \<sigma>) = Some m"
    "csr_guard_pair_rank u11s lens z su len ni co ta zs (r \<cdot> \<sigma>) = Some n"
    "m \<ge> n"
proof
  have req_subset: "set (csr_guard_form_requirements G) \<subseteq>
      set (csr_guard_form_requirements F)"
    using orient by (cases F; cases G) simp
  have realized_r: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements G)"
    by (rule csr_guard_requirements_realized_mono[OF realized req_subset])
  show "csr_guard_pair_rank u11s lens z su len ni co ta zs (l \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> F)"
    by (rule csr_guard_pair_symbolic_rank_sound[OF distinct lhs realized])
  show "csr_guard_pair_rank u11s lens z su len ni co ta zs (r \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> G)"
    by (rule csr_guard_pair_symbolic_rank_sound[OF distinct rhs realized_r])
  show "csr_guard_form_value \<rho> F \<ge> csr_guard_form_value \<rho> G"
    by (rule csr_guard_form_ge_value[OF orient])
qed

lemma csr_guard_pair_symbolic_rank_gt_sound:
  assumes distinct: "distinct [z,su,len,ni,co,ta,zs]"
    and lhs: "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs l = Some F"
    and rhs: "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs r = Some G"
    and orient: "csr_guard_form_gt F G"
    and realized: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements F)"
  obtains m n where
    "csr_guard_pair_rank u11s lens z su len ni co ta zs (l \<cdot> \<sigma>) = Some m"
    "csr_guard_pair_rank u11s lens z su len ni co ta zs (r \<cdot> \<sigma>) = Some n"
    "m > n"
proof
  have req_subset: "set (csr_guard_form_requirements G) \<subseteq>
      set (csr_guard_form_requirements F)"
    using orient by (cases F; cases G) simp
  have realized_r: "csr_guard_requirements_realized
      z su len ni co ta zs \<sigma> \<rho> (csr_guard_form_requirements G)"
    by (rule csr_guard_requirements_realized_mono[OF realized req_subset])
  show "csr_guard_pair_rank u11s lens z su len ni co ta zs (l \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> F)"
    by (rule csr_guard_pair_symbolic_rank_sound[OF distinct lhs realized])
  show "csr_guard_pair_rank u11s lens z su len ni co ta zs (r \<cdot> \<sigma>) =
      Some (csr_guard_form_value \<rho> G)"
    by (rule csr_guard_pair_symbolic_rank_sound[OF distinct rhs realized_r])
  show "csr_guard_form_value \<rho> F > csr_guard_form_value \<rho> G"
    by (rule csr_guard_form_gt_value[OF orient])
qed

lemma csr_guard_pair_u11_length_weak:
  fixes q :: "('f,'v) term" and L :: 'v
  assumes wrappers: "u11s \<noteq> lens"
  defines "l \<equiv> Fun u11s [q, Var L]"
    and "r \<equiv> Fun lens [Var L]"
  obtains F G where
    "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs l = Some F"
    "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs r = Some G"
    "csr_guard_form_ge F G"
proof
  show "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs l =
      Some (Guard_Form [(L,Guard_List)] [(L,Guard_List)] 0)"
    unfolding l_def by simp
  show "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs r =
      Some (Guard_Form [(L,Guard_List)] [(L,Guard_List)] 0)"
    unfolding r_def using wrappers by simp
  show "csr_guard_form_ge
      (Guard_Form [(L,Guard_List)] [(L,Guard_List)] 0)
      (Guard_Form [(L,Guard_List)] [(L,Guard_List)] 0)"
    by simp
qed

lemma csr_guard_pair_length_cons_u11_strict:
  fixes q :: "('f,'v) term" and N L :: 'v
  assumes wrappers: "lens \<noteq> u11s"
    and constructors: "co \<noteq> ni" "co \<noteq> ta"
  defines "l \<equiv> Fun lens [Fun co [Var N, Var L]]"
    and "r \<equiv> Fun u11s [q, Var L]"
  obtains F G where
    "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs l = Some F"
    "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs r = Some G"
    "csr_guard_form_gt F G"
proof
  show "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs l =
      Some (Guard_Form
        [(N,Guard_Nat),(L,Guard_List)] [(L,Guard_List)] 1)"
    unfolding l_def using wrappers constructors by simp
  show "csr_guard_pair_symbolic_rank u11s lens z su len ni co ta zs r =
      Some (Guard_Form [(L,Guard_List)] [(L,Guard_List)] 0)"
    unfolding r_def by simp
  show "csr_guard_form_gt
      (Guard_Form [(N,Guard_Nat),(L,Guard_List)] [(L,Guard_List)] 1)
      (Guard_Form [(L,Guard_List)] [(L,Guard_List)] 0)"
    by simp
qed

definition csr_guard_pair_rank_gt where
  "csr_guard_pair_rank_gt u11s lens z su len ni co ta zs =
    {(s,t). \<exists>m n.
      csr_guard_pair_rank u11s lens z su len ni co ta zs s = Some m \<and>
      csr_guard_pair_rank u11s lens z su len ni co ta zs t = Some n \<and> m > n}"

definition csr_guard_pair_rank_ge where
  "csr_guard_pair_rank_ge u11s lens z su len ni co ta zs =
    {(s,t). \<exists>m n.
      csr_guard_pair_rank u11s lens z su len ni co ta zs s = Some m \<and>
      csr_guard_pair_rank u11s lens z su len ni co ta zs t = Some n \<and> m \<ge> n}"

lemma csr_guard_pair_rank_gt_ge_comp:
  "csr_guard_pair_rank_gt u11s lens z su len ni co ta zs O
      csr_guard_pair_rank_ge u11s lens z su len ni co ta zs
    \<subseteq> csr_guard_pair_rank_gt u11s lens z su len ni co ta zs"
  unfolding csr_guard_pair_rank_gt_def csr_guard_pair_rank_ge_def by auto

lemma csr_guard_pair_rank_ge_gt_comp:
  "csr_guard_pair_rank_ge u11s lens z su len ni co ta zs O
      csr_guard_pair_rank_gt u11s lens z su len ni co ta zs
    \<subseteq> csr_guard_pair_rank_gt u11s lens z su len ni co ta zs"
  unfolding csr_guard_pair_rank_gt_def csr_guard_pair_rank_ge_def by auto

lemma csr_guard_pair_rank_ge_trans:
  "trans (csr_guard_pair_rank_ge u11s lens z su len ni co ta zs)"
  unfolding trans_def csr_guard_pair_rank_ge_def by auto

lemma SN_csr_guard_pair_rank_gt:
  "SN (csr_guard_pair_rank_gt u11s lens z su len ni co ta zs)"
proof -
  have sub: "csr_guard_pair_rank_gt u11s lens z su len ni co ta zs
      \<subseteq> inv_image {(m,n). m > n}
        (the \<circ> csr_guard_pair_rank u11s lens z su len ni co ta zs)"
    unfolding csr_guard_pair_rank_gt_def inv_image_def by auto
  have "SN (inv_image {(m,n). m > n}
      (the \<circ> csr_guard_pair_rank u11s lens z su len ni co ta zs))"
    by (rule SN_inv_image[OF SN_nat_gt])
  then show ?thesis by (rule SN_subset[OF _ sub])
qed

lemma SN_rel_csr_guard_pair_rank:
  "SN_rel (csr_guard_pair_rank_gt u11s lens z su len ni co ta zs)
    (csr_guard_pair_rank_ge u11s lens z su len ni co ta zs)"
proof -
  let ?S = "csr_guard_pair_rank_gt u11s lens z su len ni co ta zs"
  let ?NS = "csr_guard_pair_rank_ge u11s lens z su len ni co ta zs"
  have compat: "?NS O ?S \<subseteq> ?S"
    by (rule csr_guard_pair_rank_ge_gt_comp)
  have sn: "SN ((?NS \<union> ?S)\<^sup>* O ?S O (?NS \<union> ?S)\<^sup>*)"
    by (rule compatible_SN'[OF compat SN_csr_guard_pair_rank_gt])
  have sub: "?NS\<^sup>* O ?S O ?NS\<^sup>*
      \<subseteq> (?NS \<union> ?S)\<^sup>* O ?S O (?NS \<union> ?S)\<^sup>*"
  proof -
    have ns: "?NS\<^sup>* \<subseteq> (?NS \<union> ?S)\<^sup>*"
      by (rule rtrancl_mono, auto)
    show ?thesis
      by (rule relcomp_mono[OF ns relcomp_mono[OF subset_refl ns]])
  qed
  show ?thesis unfolding SN_rel_defs by (rule SN_subset[OF sn sub])
qed

lemma csr_guard_symbolic_rank_zero [simp]:
  "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (Fun z []) =
    Some (Guard_Form [] [] 0)"
  by simp

lemma csr_guard_symbolic_rank_nil:
  assumes "ni \<noteq> co" "ni \<noteq> ta"
  shows "csr_guard_symbolic_rank z su len ni co ta zs Guard_List (Fun ni []) =
    Some (Guard_Form [] [] 0)"
  using assms by simp

lemma csr_guard_rank_cons_list:
  assumes distinct: "co \<noteq> ni" "co \<noteq> ta"
    and arity: "csr_guard_rank z su len ni co ta zs Guard_Nat n = Some kn"
      "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
  shows "csr_guard_rank z su len ni co ta zs Guard_List
      (Fun co [n,l]) = Some (Suc kl)"
  using assms by simp

lemma csr_guard_rank_cons_list_strict:
  assumes distinct: "co \<noteq> ni" "co \<noteq> ta"
    and arity: "csr_guard_rank z su len ni co ta zs Guard_Nat n = Some kn"
      "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
  obtains k where
    "csr_guard_rank z su len ni co ta zs Guard_List
       (Fun co [n,l]) = Some k"
    "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
    "k > kl"
proof
  show "csr_guard_rank z su len ni co ta zs Guard_List
       (Fun co [n,l]) = Some (Suc kl)"
    by (rule csr_guard_rank_cons_list[OF distinct arity])
  show "csr_guard_rank z su len ni co ta zs Guard_List l = Some kl"
    by (rule arity(2))
  show "Suc kl > kl" by simp
qed

text \<open>
  The executable processor will validate the recognizer/schema rules and use
  the following relation as its strict component.  Keeping it explicit makes
  mutation-negative tests possible before it is connected to CPF parsing.
\<close>

definition csr_guard_rank_gt where
  "csr_guard_rank_gt z su len ni co ta zs A =
    {(s,t). \<exists>m n.
      csr_guard_rank z su len ni co ta zs A s = Some m \<and>
      csr_guard_rank z su len ni co ta zs A t = Some n \<and> m > n}"

definition csr_guard_rank_ge where
  "csr_guard_rank_ge z su len ni co ta zs A =
    {(s,t). \<exists>m n.
      csr_guard_rank z su len ni co ta zs A s = Some m \<and>
      csr_guard_rank z su len ni co ta zs A t = Some n \<and> m \<ge> n}"

lemma csr_guard_rank_gt_ge_comp:
  "csr_guard_rank_gt z su len ni co ta zs A O
      csr_guard_rank_ge z su len ni co ta zs A
    \<subseteq> csr_guard_rank_gt z su len ni co ta zs A"
  unfolding csr_guard_rank_gt_def csr_guard_rank_ge_def by auto

lemma csr_guard_rank_ge_gt_comp:
  "csr_guard_rank_ge z su len ni co ta zs A O
      csr_guard_rank_gt z su len ni co ta zs A
    \<subseteq> csr_guard_rank_gt z su len ni co ta zs A"
  unfolding csr_guard_rank_gt_def csr_guard_rank_ge_def by auto

lemma csr_guard_rank_ge_refl_on:
  "{t. \<exists>n. csr_guard_rank z su len ni co ta zs A t = Some n}
    \<subseteq> {t. (t,t) \<in> csr_guard_rank_ge z su len ni co ta zs A}"
  unfolding csr_guard_rank_ge_def by auto

lemma SN_csr_guard_rank_gt:
  "SN (csr_guard_rank_gt z su len ni co ta zs A)"
proof -
  have sub: "csr_guard_rank_gt z su len ni co ta zs A
      \<subseteq> inv_image {(m,n). m > n}
        (the \<circ> csr_guard_rank z su len ni co ta zs A)"
    unfolding csr_guard_rank_gt_def inv_image_def by auto
  have "SN (inv_image {(m,n). m > n}
      (the \<circ> csr_guard_rank z su len ni co ta zs A))"
    by (rule SN_inv_image[OF SN_nat_gt])
  then show ?thesis by (rule SN_subset[OF _ sub])
qed

lemma SN_rel_csr_guard_rank:
  "SN_rel (csr_guard_rank_gt z su len ni co ta zs A)
    (csr_guard_rank_ge z su len ni co ta zs A)"
proof -
  let ?S = "csr_guard_rank_gt z su len ni co ta zs A"
  let ?NS = "csr_guard_rank_ge z su len ni co ta zs A"
  have compat: "?NS O ?S \<subseteq> ?S"
    by (rule csr_guard_rank_ge_gt_comp)
  have sn: "SN ((?NS \<union> ?S)\<^sup>* O ?S O (?NS \<union> ?S)\<^sup>*)"
    by (rule compatible_SN'[OF compat SN_csr_guard_rank_gt])
  have sub: "?NS\<^sup>* O ?S O ?NS\<^sup>*
      \<subseteq> (?NS \<union> ?S)\<^sup>* O ?S O (?NS \<union> ?S)\<^sup>*"
  proof -
    have ns: "?NS\<^sup>* \<subseteq> (?NS \<union> ?S)\<^sup>*"
      by (rule rtrancl_mono, auto)
    show ?thesis
      by (rule relcomp_mono[OF ns relcomp_mono[OF subset_refl ns]])
  qed
  show ?thesis unfolding SN_rel_defs by (rule SN_subset[OF sn sub])
qed

text \<open>
  This is the framework boundary needed by an executable guarded-list
  processor.  The checker may establish the two inclusions using a typed
  symbolic rank calculation; the generic CSR-DP soundness argument below is
  independent of the concrete recognizer names and rules.
\<close>

lemma finite_min_csr_dpp_by_guard_rank:
  assumes strict: "csr_min_pair_step shp \<mu> P R
      \<subseteq> csr_guard_rank_gt z su len ni co ta zs A"
    and weak: "csdp_step shp \<mu> R
      \<subseteq> csr_guard_rank_ge z su len ni co ta zs A"
  shows "finite_min_csr_dpp shp \<mu> P R"
  unfolding finite_min_csr_dpp_def
  by (rule SN_rel_mono[OF strict weak SN_rel_csr_guard_rank])

end
