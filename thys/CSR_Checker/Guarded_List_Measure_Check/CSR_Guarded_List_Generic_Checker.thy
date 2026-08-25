(*
Author: Ferrum contributors
License: LGPL (see file COPYING.LESSER)
*)
theory CSR_Guarded_List_Generic_Checker
  imports CSR_Guarded_List_Measure
begin

text \<open>
  An executable symbolic account of the semantic guard language.  Unlike the
  original OvCons checker, the checks below do not enumerate a particular
  residual TRS.  A rule is accepted precisely when successful recognition on
  its right-hand side entails successful recognition on its left-hand side,
  and when normalization preserves every guarded rank.
\<close>

datatype 'v csr_guard_truth_form = Guard_Truth_Form
  "'v list" "('v \<times> csr_guard_sort) list"

fun csr_guard_truth_variables where
  "csr_guard_truth_variables (Guard_Truth_Form xs req) = xs"

fun csr_guard_truth_requirements where
  "csr_guard_truth_requirements (Guard_Truth_Form xs req) = req"

fun csr_guard_truth_form_append where
  "csr_guard_truth_form_append (Guard_Truth_Form xs req)
      (Guard_Truth_Form ys ss) = Guard_Truth_Form (xs @ ys) (req @ ss)"

definition csr_guard_sort_requirement_implied where
  "csr_guard_sort_requirement_implied target source \<longleftrightarrow>
    target = source \<or> (target = Guard_List \<and> source = Guard_IList)"

definition csr_guard_requirements_covered where
  "csr_guard_requirements_covered source target \<longleftrightarrow>
    list_all (\<lambda>(x,A). list_ex (\<lambda>(y,B).
      x = y \<and> csr_guard_sort_requirement_implied B A) target) source"

lemma csr_guard_requirements_covered_sound:
  assumes constructors: "distinct [z,su,len,ni,co,ta,zs]"
    and realized: "csr_guard_requirements_realized z su len ni co ta zs
      \<sigma> (csr_guard_rank_environment z su len ni co ta zs \<sigma>) target"
    and covered: "csr_guard_requirements_covered source target"
  shows "csr_guard_requirements_realized z su len ni co ta zs
    \<sigma> (csr_guard_rank_environment z su len ni co ta zs \<sigma>) source"
  unfolding csr_guard_requirements_realized_def
proof (intro allI impI)
  fix x A
  assume source: "(x,A) \<in> set source"
  from covered source obtain B where target: "(x,B) \<in> set target"
    and implied: "csr_guard_sort_requirement_implied B A"
    unfolding csr_guard_requirements_covered_def list_all_iff list_ex_iff
    by fastforce
  from realized target have target_rank:
    "csr_guard_rank z su len ni co ta zs B (\<sigma> x) =
      Some (csr_guard_rank_environment z su len ni co ta zs \<sigma> (x,B))"
    unfolding csr_guard_requirements_realized_def by blast
  from implied consider (same) "B = A"
    | (list_ilist) "B = Guard_List" "A = Guard_IList"
    unfolding csr_guard_sort_requirement_implied_def by blast
  then show "csr_guard_rank z su len ni co ta zs A (\<sigma> x) =
      Some (csr_guard_rank_environment z su len ni co ta zs \<sigma> (x,A))"
  proof cases
    case same
    then show ?thesis using target_rank by simp
  next
    case list_ilist
    from csr_guard_rank_list_imp_ilist[OF constructors,
        of "\<sigma> x" "csr_guard_rank_environment
          z su len ni co ta zs \<sigma> (x,B)"]
      target_rank list_ilist
    obtain m where ilist:
      "csr_guard_rank z su len ni co ta zs Guard_IList (\<sigma> x) = Some m"
      by auto
    show ?thesis
      using ilist list_ilist unfolding csr_guard_rank_environment_def by simp
  qed
qed

lemma csr_guard_truth_option_append_the:
  assumes left: "L \<noteq> None" and right: "R \<noteq> None"
  shows "(case (L,R) of
      (Some F, Some G) \<Rightarrow> Some (csr_guard_truth_form_append F G)
    | _ \<Rightarrow> None) =
    Some (csr_guard_truth_form_append (the L) (the R))"
  using left right by (cases L; cases R; simp)

lemma map_option_the:
  assumes "x \<noteq> None"
  shows "map_option f x = Some (f (the x))"
  using assms by (cases x) simp_all

fun csr_guard_symbolic_truth ::
  "'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
   'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow>
   ('f,'v) term \<Rightarrow> 'v csr_guard_truth_form option"
where
  "csr_guard_symbolic_truth tt a natp listp ilistp z su len ni co ta zs
      (Var x) = Some (Guard_Truth_Form [x] [])"
| "csr_guard_symbolic_truth tt a natp listp ilistp z su len ni co ta zs
      (Fun f ts) =
     (if f = tt \<and> ts = [] then Some (Guard_Truth_Form [] [])
     else if f = a \<and> length ts = 2 then
       (case (csr_guard_symbolic_truth tt a natp listp ilistp
                z su len ni co ta zs (ts ! 0),
              csr_guard_symbolic_truth tt a natp listp ilistp
                z su len ni co ta zs (ts ! 1)) of
          (Some F, Some G) \<Rightarrow> Some (csr_guard_truth_form_append F G)
        | _ \<Rightarrow> None)
     else if f = natp \<and> length ts = 1 then
       map_option (\<lambda>F. Guard_Truth_Form [] (csr_guard_form_requirements F))
         (csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat (ts ! 0))
     else if f = listp \<and> length ts = 1 then
       map_option (\<lambda>F. Guard_Truth_Form [] (csr_guard_form_requirements F))
         (csr_guard_symbolic_rank z su len ni co ta zs Guard_List (ts ! 0))
     else if f = ilistp \<and> length ts = 1 then
       map_option (\<lambda>F. Guard_Truth_Form [] (csr_guard_form_requirements F))
         (csr_guard_symbolic_rank z su len ni co ta zs Guard_IList (ts ! 0))
     else None)"

definition csr_guard_truth_form_realized where
  "csr_guard_truth_form_realized tt a natp listp ilistp z su len ni co ta zs
      \<sigma> \<rho> F \<longleftrightarrow>
    (\<forall>x \<in> set (csr_guard_truth_variables F).
      csr_guard_truth tt a natp listp ilistp z su len ni co ta zs (\<sigma> x)) \<and>
    csr_guard_requirements_realized z su len ni co ta zs \<sigma> \<rho>
      (csr_guard_truth_requirements F)"

lemma csr_guard_truth_form_realized_append [simp]:
  "csr_guard_truth_form_realized tt a natp listp ilistp z su len ni co ta zs
      \<sigma> \<rho> (csr_guard_truth_form_append F G) \<longleftrightarrow>
    csr_guard_truth_form_realized tt a natp listp ilistp z su len ni co ta zs
      \<sigma> \<rho> F \<and>
    csr_guard_truth_form_realized tt a natp listp ilistp z su len ni co ta zs
      \<sigma> \<rho> G"
  by (cases F; cases G; auto simp: csr_guard_truth_form_realized_def)

lemma csr_guard_symbolic_truth_sound:
  assumes names: "distinct [tt,a,natp,listp,ilistp]"
    and constructors: "distinct [z,su,len,ni,co,ta,zs]"
    and symbolic: "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs t = Some req"
    and realized: "csr_guard_truth_form_realized tt a natp listp ilistp
      z su len ni co ta zs \<sigma> \<rho> req"
  shows "csr_guard_truth tt a natp listp ilistp z su len ni co ta zs
    (t \<cdot> \<sigma>)"
  using symbolic realized
proof (induction t arbitrary: req)
  case (Var x)
  from Var.prems(1) have req: "req = Guard_Truth_Form [x] []" by simp
  show ?case using Var.prems(2) unfolding req csr_guard_truth_form_realized_def
    by simp
next
  case (Fun f ts)
  show ?case
  proof (cases "f = tt \<and> ts = []")
    case True
    then show ?thesis by simp
  next
    case not_tt: False
    show ?thesis
    proof (cases "f = a \<and> length ts = 2")
      case True
      have ts_nonempty: "ts \<noteq> []" using True by auto
      let ?left = "csr_guard_symbolic_truth tt a natp listp ilistp
        z su len ni co ta zs (ts ! 0)"
      let ?right = "csr_guard_symbolic_truth tt a natp listp ilistp
        z su len ni co ta zs (ts ! 1)"
      obtain LF where left: "?left = Some LF"
      proof (cases ?left)
        case None
        then show ?thesis using Fun.prems(1) not_tt True ts_nonempty by simp
      next
        case (Some F)
        show ?thesis by (rule that[of F], rule Some)
      qed
      obtain RF where right: "?right = Some RF"
      proof (cases ?right)
        case None
        then show ?thesis using Fun.prems(1) not_tt True ts_nonempty left by simp
      next
        case (Some F)
        show ?thesis by (rule that[of F], rule Some)
      qed
      have req: "req = csr_guard_truth_form_append LF RF"
        using Fun.prems(1) not_tt True ts_nonempty left right by simp
      have mem0: "ts ! 0 \<in> set ts" and mem1: "ts ! 1 \<in> set ts"
        using True by auto
      have realized_left: "csr_guard_truth_form_realized tt a natp listp ilistp
          z su len ni co ta zs \<sigma> \<rho> LF"
        and realized_right: "csr_guard_truth_form_realized tt a natp listp ilistp
          z su len ni co ta zs \<sigma> \<rho> RF"
        using Fun.prems(2) req by simp_all
      have truth_left: "csr_guard_truth tt a natp listp ilistp
          z su len ni co ta zs (ts ! 0 \<cdot> \<sigma>)"
        by (rule Fun.IH[OF mem0 left realized_left])
      have truth_right: "csr_guard_truth tt a natp listp ilistp
          z su len ni co ta zs (ts ! 1 \<cdot> \<sigma>)"
        by (rule Fun.IH[OF mem1 right realized_right])
      show ?thesis using not_tt True truth_left truth_right by simp
    next
      case not_and: False
      show ?thesis
      proof (cases "f = natp \<and> length ts = 1")
        case True
        then obtain F where rank:
            "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat
              (ts ! 0) = Some F"
          and req: "req = Guard_Truth_Form [] (csr_guard_form_requirements F)"
          using Fun.prems(1) not_tt not_and
          by (auto split: option.splits)
        have ground: "csr_guard_rank z su len ni co ta zs Guard_Nat
            (ts ! 0 \<cdot> \<sigma>) = Some (csr_guard_form_value \<rho> F)"
          by (rule csr_guard_symbolic_rank_sound[OF constructors rank],
              use Fun.prems(2) req in
                \<open>simp add: csr_guard_truth_form_realized_def\<close>)
        show ?thesis using not_tt not_and True ground by simp
      next
        case not_nat: False
        show ?thesis
        proof (cases "f = listp \<and> length ts = 1")
          case True
          then obtain F where rank:
              "csr_guard_symbolic_rank z su len ni co ta zs Guard_List
                (ts ! 0) = Some F"
            and req: "req = Guard_Truth_Form [] (csr_guard_form_requirements F)"
            using Fun.prems(1) not_tt not_and not_nat
            by (auto split: option.splits)
          have ground: "csr_guard_rank z su len ni co ta zs Guard_List
              (ts ! 0 \<cdot> \<sigma>) = Some (csr_guard_form_value \<rho> F)"
            by (rule csr_guard_symbolic_rank_sound[OF constructors rank],
                use Fun.prems(2) req in
                  \<open>simp add: csr_guard_truth_form_realized_def\<close>)
          show ?thesis using not_tt not_and not_nat True ground by simp
        next
          case not_list: False
          show ?thesis
          proof (cases "f = ilistp \<and> length ts = 1")
            case True
            then obtain F where rank:
                "csr_guard_symbolic_rank z su len ni co ta zs Guard_IList
                  (ts ! 0) = Some F"
              and req: "req = Guard_Truth_Form [] (csr_guard_form_requirements F)"
              using Fun.prems(1) not_tt not_and not_nat not_list
              by (auto split: option.splits)
            have ground: "csr_guard_rank z su len ni co ta zs Guard_IList
                (ts ! 0 \<cdot> \<sigma>) = Some (csr_guard_form_value \<rho> F)"
              by (rule csr_guard_symbolic_rank_sound[OF constructors rank],
                  use Fun.prems(2) req in
                    \<open>simp add: csr_guard_truth_form_realized_def\<close>)
            show ?thesis using not_tt not_and not_nat not_list True ground by simp
          next
            case False
            from Fun.prems(1) have contradiction: False
              by (simp only: csr_guard_symbolic_truth.simps not_tt not_and
                  not_nat not_list False if_False option.distinct)
            show ?thesis by (rule FalseE[OF contradiction])
          qed
        qed
      qed
    qed
  qed
qed

lemma csr_guard_symbolic_truth_complete:
  assumes names: "distinct [tt,a,natp,listp,ilistp]"
    and constructors: "distinct [z,su,len,ni,co,ta,zs]"
    and truth: "csr_guard_truth tt a natp listp ilistp z su len ni co ta zs
      (t \<cdot> \<sigma>)"
  shows "\<exists>req. csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs t = Some req \<and>
    csr_guard_truth_form_realized tt a natp listp ilistp z su len ni co ta zs
      \<sigma> (csr_guard_rank_environment z su len ni co ta zs \<sigma>) req"
  using truth
proof (induction t)
  case (Var x)
  then show ?case
    unfolding csr_guard_truth_form_realized_def by simp
next
  case (Fun f ts)
  let ?\<rho> = "csr_guard_rank_environment z su len ni co ta zs \<sigma>"
  consider
      (truth) "f = tt" "ts = []"
    | (conj) "f = a" "length ts = 2"
        "csr_guard_truth tt a natp listp ilistp z su len ni co ta zs
          (ts ! 0 \<cdot> \<sigma>)"
        "csr_guard_truth tt a natp listp ilistp z su len ni co ta zs
          (ts ! 1 \<cdot> \<sigma>)"
    | (nat) n where "f = natp" "length ts = 1"
        "csr_guard_rank z su len ni co ta zs Guard_Nat
          (ts ! 0 \<cdot> \<sigma>) = Some n"
    | (list) n where "f = listp" "length ts = 1"
        "csr_guard_rank z su len ni co ta zs Guard_List
          (ts ! 0 \<cdot> \<sigma>) = Some n"
    | (ilist) n where "f = ilistp" "length ts = 1"
        "csr_guard_rank z su len ni co ta zs Guard_IList
          (ts ! 0 \<cdot> \<sigma>) = Some n"
    using Fun.prems
    by (auto split: if_splits option.splits)
  then show ?case
  proof cases
    case truth
    then show ?thesis unfolding csr_guard_truth_form_realized_def by simp
  next
    case conj
    have not_truth: "\<not> (f = tt \<and> ts = [])" using conj(2) by auto
    have ts_nonempty: "ts \<noteq> []" using conj(2) by auto
    have mem0: "ts ! 0 \<in> set ts" and mem1: "ts ! 1 \<in> set ts"
      using conj(2) by auto
    let ?left = "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs (ts ! 0)"
    let ?right = "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs (ts ! 1)"
    let ?LF = "the ?left"
    let ?RF = "the ?right"
    have left_complete: "\<exists>F. ?left = Some F \<and>
        csr_guard_truth_form_realized tt a natp listp ilistp
          z su len ni co ta zs \<sigma> ?\<rho> F"
      by (rule Fun.IH[OF mem0 conj(3)])
    have right_complete: "\<exists>F. ?right = Some F \<and>
        csr_guard_truth_form_realized tt a natp listp ilistp
          z su len ni co ta zs \<sigma> ?\<rho> F"
      by (rule Fun.IH[OF mem1 conj(4)])
    have left_nonempty: "?left \<noteq> None" using left_complete by auto
    have right_nonempty: "?right \<noteq> None" using right_complete by auto
    have left: "?left = Some ?LF" using left_nonempty by (cases ?left) auto
    have right: "?right = Some ?RF" using right_nonempty by (cases ?right) auto
    have realized_left: "csr_guard_truth_form_realized tt a natp listp ilistp
        z su len ni co ta zs \<sigma> ?\<rho> ?LF"
      using left_complete left by auto
    have realized_right: "csr_guard_truth_form_realized tt a natp listp ilistp
        z su len ni co ta zs \<sigma> ?\<rho> ?RF"
      using right_complete right by auto
    show ?thesis
    proof (intro exI[of _ "csr_guard_truth_form_append ?LF ?RF"] conjI)
      show "csr_guard_symbolic_truth tt a natp listp ilistp
          z su len ni co ta zs (Fun f ts) =
        Some (csr_guard_truth_form_append ?LF ?RF)"
      proof -
        have first: "\<not> (f = tt \<and> ts = [])" using ts_nonempty by auto
        have first_a: "\<not> (a = tt \<and> ts = [])" using ts_nonempty by auto
        have second: "f = a \<and> length ts = 2" using conj by auto
        have combined: "(case (?left,?right) of
              (Some F, Some G) \<Rightarrow>
                Some (csr_guard_truth_form_append F G)
            | _ \<Rightarrow> None) =
          Some (csr_guard_truth_form_append ?LF ?RF)"
          by (rule csr_guard_truth_option_append_the[
              OF left_nonempty right_nonempty])
        show ?thesis
          unfolding csr_guard_symbolic_truth.simps
          apply (subst HOL.if_not_P[OF first])
          apply (subst HOL.if_P[OF second])
          apply (rule combined)
          done
      qed
      show "csr_guard_truth_form_realized tt a natp listp ilistp
          z su len ni co ta zs \<sigma> ?\<rho>
          (csr_guard_truth_form_append ?LF ?RF)"
        using realized_left realized_right by simp
    qed
  next
    case (nat n)
    let ?rank = "csr_guard_symbolic_rank z su len ni co ta zs Guard_Nat
      (ts ! 0)"
    let ?F = "the ?rank"
    note complete = csr_guard_symbolic_rank_complete[OF constructors nat(3)]
    have nonempty: "?rank \<noteq> None" using complete by auto
    have rank: "?rank = Some ?F" using nonempty by (cases ?rank) auto
    have realized: "csr_guard_requirements_realized z su len ni co ta zs
        \<sigma> ?\<rho> (csr_guard_form_requirements ?F)"
      using complete rank by auto
    have not_tt: "\<not> (f = tt \<and> ts = [])" using nat by auto
    have not_and: "\<not> (f = a \<and> length ts = 2)" using nat by auto
    have is_nat: "f = natp \<and> length ts = 1" using nat by auto
    have mapped: "map_option
        (\<lambda>F. Guard_Truth_Form [] (csr_guard_form_requirements F)) ?rank =
      Some (Guard_Truth_Form [] (csr_guard_form_requirements ?F))"
      by (rule map_option_the[OF nonempty])
    have symbolic: "csr_guard_symbolic_truth tt a natp listp ilistp
        z su len ni co ta zs (Fun f ts) =
      Some (Guard_Truth_Form [] (csr_guard_form_requirements ?F))"
      unfolding csr_guard_symbolic_truth.simps
      apply (subst HOL.if_not_P[OF not_tt])
      apply (subst HOL.if_not_P[OF not_and])
      apply (subst HOL.if_P[OF is_nat])
      apply (rule mapped)
      done
    show ?thesis
      unfolding csr_guard_truth_form_realized_def
      by (intro exI[of _ "Guard_Truth_Form [] (csr_guard_form_requirements ?F)"]
          conjI symbolic; use realized in simp)
  next
    case (list n)
    let ?rank = "csr_guard_symbolic_rank z su len ni co ta zs Guard_List
      (ts ! 0)"
    let ?F = "the ?rank"
    note complete = csr_guard_symbolic_rank_complete[OF constructors list(3)]
    have nonempty: "?rank \<noteq> None" using complete by auto
    have rank: "?rank = Some ?F" using nonempty by (cases ?rank) auto
    have realized: "csr_guard_requirements_realized z su len ni co ta zs
        \<sigma> ?\<rho> (csr_guard_form_requirements ?F)"
      using complete rank by auto
    have not_tt: "\<not> (f = tt \<and> ts = [])" using list by auto
    have not_and: "\<not> (f = a \<and> length ts = 2)" using list by auto
    have not_nat: "\<not> (f = natp \<and> length ts = 1)"
      using names list by auto
    have is_list: "f = listp \<and> length ts = 1" using list by auto
    have mapped: "map_option
        (\<lambda>F. Guard_Truth_Form [] (csr_guard_form_requirements F)) ?rank =
      Some (Guard_Truth_Form [] (csr_guard_form_requirements ?F))"
      by (rule map_option_the[OF nonempty])
    have symbolic: "csr_guard_symbolic_truth tt a natp listp ilistp
        z su len ni co ta zs (Fun f ts) =
      Some (Guard_Truth_Form [] (csr_guard_form_requirements ?F))"
      unfolding csr_guard_symbolic_truth.simps
      apply (subst HOL.if_not_P[OF not_tt])
      apply (subst HOL.if_not_P[OF not_and])
      apply (subst HOL.if_not_P[OF not_nat])
      apply (subst HOL.if_P[OF is_list])
      apply (rule mapped)
      done
    show ?thesis
      unfolding csr_guard_truth_form_realized_def
      by (intro exI[of _ "Guard_Truth_Form [] (csr_guard_form_requirements ?F)"]
          conjI symbolic; use realized in simp)
  next
    case (ilist n)
    let ?rank = "csr_guard_symbolic_rank z su len ni co ta zs Guard_IList
      (ts ! 0)"
    let ?F = "the ?rank"
    note complete = csr_guard_symbolic_rank_complete[OF constructors ilist(3)]
    have nonempty: "?rank \<noteq> None" using complete by auto
    have rank: "?rank = Some ?F" using nonempty by (cases ?rank) auto
    have realized: "csr_guard_requirements_realized z su len ni co ta zs
        \<sigma> ?\<rho> (csr_guard_form_requirements ?F)"
      using complete rank by auto
    have not_tt: "\<not> (f = tt \<and> ts = [])" using ilist by auto
    have not_and: "\<not> (f = a \<and> length ts = 2)" using ilist by auto
    have not_nat: "\<not> (f = natp \<and> length ts = 1)"
      using names ilist by auto
    have not_list: "\<not> (f = listp \<and> length ts = 1)"
      using names ilist by auto
    have is_ilist: "f = ilistp \<and> length ts = 1" using ilist by auto
    have mapped: "map_option
        (\<lambda>F. Guard_Truth_Form [] (csr_guard_form_requirements F)) ?rank =
      Some (Guard_Truth_Form [] (csr_guard_form_requirements ?F))"
      by (rule map_option_the[OF nonempty])
    have symbolic: "csr_guard_symbolic_truth tt a natp listp ilistp
        z su len ni co ta zs (Fun f ts) =
      Some (Guard_Truth_Form [] (csr_guard_form_requirements ?F))"
      unfolding csr_guard_symbolic_truth.simps
      apply (subst HOL.if_not_P[OF not_tt])
      apply (subst HOL.if_not_P[OF not_and])
      apply (subst HOL.if_not_P[OF not_nat])
      apply (subst HOL.if_not_P[OF not_list])
      apply (subst HOL.if_P[OF is_ilist])
      apply (rule mapped)
      done
    show ?thesis
      unfolding csr_guard_truth_form_realized_def
      by (intro exI[of _ "Guard_Truth_Form [] (csr_guard_form_requirements ?F)"]
          conjI symbolic; use realized in simp)
  qed
qed

definition csr_guard_truth_rule_backward_check where
  "csr_guard_truth_rule_backward_check tt a natp listp ilistp
      z su len ni co ta zs l r =
    (case csr_guard_symbolic_truth tt a natp listp ilistp
            z su len ni co ta zs r of
       None \<Rightarrow> True
     | Some F_r \<Rightarrow>
         (case csr_guard_symbolic_truth tt a natp listp ilistp
                 z su len ni co ta zs l of
            None \<Rightarrow> False
          | Some F_l \<Rightarrow>
              set (csr_guard_truth_variables F_l) \<subseteq>
                set (csr_guard_truth_variables F_r) \<and>
              csr_guard_requirements_covered
                (csr_guard_truth_requirements F_l)
                (csr_guard_truth_requirements F_r)))"

lemma csr_guard_truth_rule_backward_check_nonempty:
  assumes checked: "csr_guard_truth_rule_backward_check tt a natp listp ilistp
      z su len ni co ta zs l r"
    and rhs: "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs r = Some F"
  shows "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs l \<noteq> None"
  using checked rhs unfolding csr_guard_truth_rule_backward_check_def
  by (cases "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs l") simp_all

lemma csr_guard_truth_rule_backward_check_subsets:
  assumes checked: "csr_guard_truth_rule_backward_check tt a natp listp ilistp
      z su len ni co ta zs l r"
    and rhs: "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs r = Some F"
    and lhs: "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs l = Some G"
  shows "set (csr_guard_truth_variables G) \<subseteq>
      set (csr_guard_truth_variables F) \<and>
    csr_guard_requirements_covered
      (csr_guard_truth_requirements G)
      (csr_guard_truth_requirements F)"
  using checked rhs lhs unfolding csr_guard_truth_rule_backward_check_def by simp

lemma csr_guard_truth_rule_backward_check_sound:
  assumes names: "distinct [tt,a,natp,listp,ilistp]"
    and constructors: "distinct [z,su,len,ni,co,ta,zs]"
    and checked: "csr_guard_truth_rule_backward_check tt a natp listp ilistp
      z su len ni co ta zs l r"
    and target: "csr_guard_truth tt a natp listp ilistp z su len ni co ta zs
      (r \<cdot> \<sigma>)"
  shows "csr_guard_truth tt a natp listp ilistp z su len ni co ta zs
    (l \<cdot> \<sigma>)"
proof -
  let ?rhs = "csr_guard_symbolic_truth tt a natp listp ilistp
    z su len ni co ta zs r"
  let ?F = "the ?rhs"
  note rhs_complete = csr_guard_symbolic_truth_complete[OF names constructors target]
  have rhs_nonempty: "?rhs \<noteq> None" using rhs_complete by auto
  have rhs: "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs r = Some ?F"
    using rhs_nonempty by (cases ?rhs) auto
  have realized_r: "csr_guard_truth_form_realized tt a natp listp ilistp
      z su len ni co ta zs \<sigma>
      (csr_guard_rank_environment z su len ni co ta zs \<sigma>) ?F"
    using rhs_complete rhs by auto
  let ?lhs = "csr_guard_symbolic_truth tt a natp listp ilistp
    z su len ni co ta zs l"
  let ?LF = "the ?lhs"
  have lhs_nonempty: "?lhs \<noteq> None"
    by (rule csr_guard_truth_rule_backward_check_nonempty[OF checked rhs])
  have lhs: "csr_guard_symbolic_truth tt a natp listp ilistp
      z su len ni co ta zs l = Some ?LF"
    using lhs_nonempty by (cases ?lhs) auto
  have truth_subset: "set (csr_guard_truth_variables ?LF) \<subseteq>
      set (csr_guard_truth_variables ?F)"
    and rank_covered: "csr_guard_requirements_covered
      (csr_guard_truth_requirements ?LF)
      (csr_guard_truth_requirements ?F)"
    using csr_guard_truth_rule_backward_check_subsets[OF checked rhs lhs]
    by simp_all
  have realized_l: "csr_guard_truth_form_realized tt a natp listp ilistp
      z su len ni co ta zs \<sigma>
      (csr_guard_rank_environment z su len ni co ta zs \<sigma>)
      ?LF"
  proof -
    from realized_r have truths:
      "\<forall>x\<in>set (csr_guard_truth_variables ?F).
        csr_guard_truth tt a natp listp ilistp
        z su len ni co ta zs (\<sigma> x)"
      and ranks: "csr_guard_requirements_realized z su len ni co ta zs \<sigma>
        (csr_guard_rank_environment z su len ni co ta zs \<sigma>)
        (csr_guard_truth_requirements ?F)"
      unfolding csr_guard_truth_form_realized_def by simp_all
    show ?thesis unfolding csr_guard_truth_form_realized_def
    proof
      show "\<forall>x\<in>set (csr_guard_truth_variables ?LF).
          csr_guard_truth tt a natp listp ilistp
          z su len ni co ta zs (\<sigma> x)"
        using truths truth_subset by auto
      show "csr_guard_requirements_realized z su len ni co ta zs \<sigma>
          (csr_guard_rank_environment z su len ni co ta zs \<sigma>)
          (csr_guard_truth_requirements ?LF)"
        by (rule csr_guard_requirements_covered_sound[
            OF constructors ranks rank_covered])
    qed
  qed
  show ?thesis
    by (rule csr_guard_symbolic_truth_sound[OF names constructors lhs realized_l])
qed

definition csr_guard_rules_check where
  "csr_guard_rules_check tt a natp listp ilistp u11 u21 u31
      z su len ni co ta zs R =
    (list_all (\<lambda>(l,r).
       csr_guard_truth_rule_backward_check tt a natp listp ilistp
         z su len ni co ta zs l r \<and>
       list_all (\<lambda>A. csr_guard_normal_rule_backward_eq
         a u11 u21 u31 z su len ni co ta zs A l r)
         [Guard_Nat, Guard_List, Guard_IList]) R)"

lemma csr_guard_rules_check_sound:
  assumes checked: "csr_guard_rules_check tt a natp listp ilistp
      u11 u21 u31 z su len ni co ta zs R"
    and symbols: "distinct
      [tt,a,natp,listp,ilistp,u11,u21,u31,z,su,len,ni,co,ta,zs]"
  shows "csr_guard_truth_rules_backward tt a natp listp ilistp
      z su len ni co ta zs (set R) \<and>
    csr_guard_normal_rules_backward_eq
      a u11 u21 u31 z su len ni co ta zs (set R)"
proof
  have names: "distinct [tt,a,natp,listp,ilistp]" using symbols by simp
  have constructors: "distinct [z,su,len,ni,co,ta,zs]" using symbols by simp
  show "csr_guard_truth_rules_backward tt a natp listp ilistp
      z su len ni co ta zs (set R)"
    unfolding csr_guard_truth_rules_backward_def
  proof (intro ballI allI impI)
    fix lr \<sigma>
    assume lr: "lr \<in> set R"
      and target: "csr_guard_truth tt a natp listp ilistp
        z su len ni co ta zs (snd lr \<cdot> \<sigma>)"
    from checked lr have rule_checked:
      "csr_guard_truth_rule_backward_check tt a natp listp ilistp
        z su len ni co ta zs (fst lr) (snd lr)"
      unfolding csr_guard_rules_check_def list_all_iff by auto
    show "csr_guard_truth tt a natp listp ilistp z su len ni co ta zs
      (fst lr \<cdot> \<sigma>)"
      by (rule csr_guard_truth_rule_backward_check_sound[
          OF names constructors rule_checked target])
  qed
  show "csr_guard_normal_rules_backward_eq
      a u11 u21 u31 z su len ni co ta zs (set R)"
    unfolding csr_guard_normal_rules_backward_eq_def
  proof (intro allI impI)
    fix l r A
    assume lr: "(l,r) \<in> set R"
    from checked lr show "csr_guard_normal_rule_backward_eq
      a u11 u21 u31 z su len ni co ta zs A l r"
      unfolding csr_guard_rules_check_def list_all_iff
      by (cases A) auto
  qed
qed

text \<open>The executable criterion is not tied to the OvCons residual: it
  accepts an additional rule over unrelated symbols, but rejects mutations
  that lose a successful guard or a constructor rank.\<close>

lemma csr_guard_rules_check_accepts_unrelated_rule:
  "csr_guard_rules_check (0::nat) 1 2 3 4 5 6 7 8 9 10 11 12 13 14
    [(Fun 15 [Var (0::nat)], Fun 16 [Var 0])]"
  by eval

lemma csr_guard_rules_check_accepts_ovcons_residual:
  "csr_guard_rules_check (0::nat) 1 2 3 4 5 6 7 8 9 10 11 12 13 14
    (sorted_list_of_set
      (csr_guard_ovcons_residual
        (0::nat) 1 2 3 4 5 6 7 8 9 10 11 12 13 14
        (0::nat) 1 2 3 4 5 6 7))"
  by eval

lemma csr_guard_rules_check_rejects_lost_truth:
  "\<not> csr_guard_rules_check (0::nat) 1 2 3 4 5 6 7 8 9 10 11 12 13 14
    [(Var (0::nat), Fun 0 [])]"
  by eval

lemma csr_guard_rules_check_rejects_lost_rank:
  "\<not> csr_guard_rules_check (0::nat) 1 2 3 4 5 6 7 8 9 10 11 12 13 14
    [(Var (0::nat), Fun 8 [])]"
  by eval

end
