theory LP_Cut_SEG_Roles
  imports LP_Cut_SEG_Finite
begin

text \<open>Position-directed role encoding. A zero depth denotes data and maps
every constructor, even a constructor whose spelling coincides with a control
symbol. Positive depths denote a finite control skeleton. Only a continuation's
first argument is another control term. This encoding is applied to the TRS
measure, never to the ordered source program or its unification/failure tests.
\<close>

fun lpc_seg_role_term where
  "lpc_seg_role_term 0 is_cont c d t = map_term d id t"
| "lpc_seg_role_term (Suc n) is_cont c d (Var x) = Var x"
| "lpc_seg_role_term (Suc n) is_cont c d (Fun f ts) =
    Fun (c f) (map (\<lambda>i. lpc_seg_role_term
      (if is_cont f \<and> i=0 then n else 0) is_cont c d (ts!i)) [0..<length ts])"

fun lpc_seg_role_value where
  "lpc_seg_role_value 0 is_cont c d v = map_lp_iterm d id v"
| "lpc_seg_role_value (Suc n) is_cont c d (LPIVar x) = LPIVar x"
| "lpc_seg_role_value (Suc n) is_cont c d (LPIFun f vs) =
    LPIFun (c f) (map (\<lambda>i. lpc_seg_role_value
      (if is_cont f \<and> i=0 then n else 0) is_cont c d (vs!i)) [0..<length vs])"

fun lpc_seg_role_shape where
  "lpc_seg_role_shape 0 is_cont t = True"
| "lpc_seg_role_shape (Suc n) is_cont (Var x) = False"
| "lpc_seg_role_shape (Suc n) is_cont (Fun f ts) =
    ((is_cont f \<longrightarrow> n>0 \<and> ts\<noteq>[]) \<and>
     list_all (\<lambda>i. lpc_seg_role_shape
       (if is_cont f \<and> i=0 then n else 0) is_cont (ts!i)) [0..<length ts])"

declare lpc_seg_role_term.simps[code del]
declare lpc_seg_role_shape.simps[code del]

lemma lpc_seg_role_term_code[code]:
  "lpc_seg_role_term n is_cont c d t = (if n=0 then map_term d id t else
    case t of Var x \<Rightarrow> Var x | Fun f ts \<Rightarrow>
      Fun (c f) (map (\<lambda>i. lpc_seg_role_term
        (if is_cont f \<and> i=0 then n-1 else 0) is_cont c d (ts!i)) [0..<length ts]))"
  by (cases n; cases t) simp_all

lemma lpc_seg_role_shape_code[code]:
  "lpc_seg_role_shape n is_cont t = (if n=0 then True else
    case t of Var x \<Rightarrow> False | Fun f ts \<Rightarrow>
      ((is_cont f \<longrightarrow> n-1>0 \<and> ts\<noteq>[]) \<and>
       list_all (\<lambda>i. lpc_seg_role_shape
         (if is_cont f \<and> i=0 then n-1 else 0) is_cont (ts!i)) [0..<length ts]))"
  by (cases n; cases t) simp_all

lemma lpc_seg_role_eval:
  assumes shape: "lpc_seg_role_shape n is_cont t"
  shows "lpc_seg_role_value n is_cont c d (lp_ieval t eta) =
    lp_ieval (lpc_seg_role_term n is_cont c d t) (\<lambda>x. map_lp_iterm d id (eta x))"
  using shape
proof (induct n arbitrary: t)
  case 0 show ?case
    by (simp only: lpc_seg_role_value.simps lpc_seg_role_term.simps; rule lp_signature_eval)
next
  case (Suc n)
  show ?case
  proof (cases t)
    case (Var x) then show ?thesis using Suc.prems by simp
  next
    case (Fun f ts)
    have child: "lpc_seg_role_value (if is_cont f \<and> i=0 then n else 0) is_cont c d
        (lp_ieval (ts!i) eta) =
      lp_ieval (lpc_seg_role_term (if is_cont f \<and> i=0 then n else 0) is_cont c d (ts!i))
        (\<lambda>x. map_lp_iterm d id (eta x))" if i: "i<length ts" for i
    proof (cases "is_cont f \<and> i=0")
      case True
      have all: "\<forall>j\<in>set [0..<length ts]. lpc_seg_role_shape
        (if is_cont f \<and> j=0 then n else 0) is_cont (ts!j)"
        using Suc.prems by (simp only: Fun lpc_seg_role_shape.simps list_all_iff) blast
      have member: "i\<in>set [0..<length ts]" using i by simp
      have shape: "lpc_seg_role_shape n is_cont (ts!i)"
        using bspec[OF all member] True by simp
      show ?thesis using Suc.hyps[OF shape] True by (simp add: id_def)
    next
      case False show ?thesis
        by (simp only: False if_False lpc_seg_role_value.simps lpc_seg_role_term.simps;
          rule lp_signature_eval)
    qed
    show ?thesis unfolding Fun
      by (simp add: map_map child id_def cong: map_cong)
  qed
qed

lemma lpc_seg_role_finite:
  "lp_seg_ground v \<Longrightarrow> lp_seg_ground (lpc_seg_role_value n is_cont c d v)"
proof (induct n arbitrary: v)
  case 0 then show ?case by (simp add: lpc_seg_ground_map)
next
  case (Suc n)
  obtain f vs where v: "v=LPIFun f vs" and finite: "list_all lp_seg_ground vs"
    using Suc.prems by (cases rule: lp_seg_ground.cases) auto
  show ?case using finite Suc.hyps
    by (auto simp: v list_all_iff lpc_seg_ground_map)
qed

lemma lpc_seg_map_index:
  "map (\<lambda>i. f (vs!i)) [0..<length vs] = map f vs"
  by (rule nth_equalityI) auto

lemma lpc_seg_role_continuation:
  assumes "is_cont u"
  shows "lpc_seg_role_value (Suc n) is_cont c d (LPIFun u (v#vs)) =
    LPIFun (c u) (lpc_seg_role_value n is_cont c d v # map (map_lp_iterm d id) vs)"
  using assms
  by (simp only: lpc_seg_role_value.simps length_Cons map_upt_Suc nth_Cons_0 nth_Cons_Suc)
    (simp add: lpc_seg_map_index)

lemma lpc_seg_role_continuation_context:
  assumes cont: "is_cont u"
    and first: "lp_seg_ground v"
    and rest: "list_all lp_seg_ground vs"
  shows "lpc_seg_finite_value (lpc_seg_role_value (Suc n) is_cont c d (LPIFun u (v#vs))) =
    (More (c u) [] \<box> (map (\<lambda>w. lpc_seg_finite_value (map_lp_iterm d id w)) vs))
      \<langle>lpc_seg_finite_value (lpc_seg_role_value n is_cont c d v)\<rangle>"
proof -
  have head: "lp_seg_ground (lpc_seg_role_value n is_cont c d v)"
    by (rule lpc_seg_role_finite[OF first])
  have tail: "lp_seg_ground (map_lp_iterm d id w)" if "w\<in>set vs" for w
    by (rule lpc_seg_ground_map) (use rest that in \<open>auto simp: list_all_iff\<close>)
  have finite: "list_all lp_seg_ground
    (lpc_seg_role_value n is_cont c d v # map (map_lp_iterm d id) vs)"
    using head tail by (auto simp: list_all_iff)
  show ?thesis by (simp only: lpc_seg_role_continuation[where is_cont=is_cont and u=u and n=n and c=c and d=d and v=v and vs=vs, OF cont]
    lpc_seg_finite_value_fun[OF finite]) (simp add: map_map)
qed

theorem lpc_seg_encoded_root:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes left_shape: "lpc_seg_role_shape nl is_cont l"
    and right_shape: "lpc_seg_role_shape nr is_cont r"
    and left: "lpc_seg_role_term nl is_cont c d l=Fun f ts"
    and rule: "(Fun f ts,lpc_seg_role_term nr is_cont c d r)\<in>R"
    and variables: "vars_term (lpc_seg_role_term nr is_cont c d r) \<subseteq> vars_term (Fun f ts)"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and symbols: "\<And>t. t\<in>set ts \<Longrightarrow> funs_term t \<subseteq> C"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "(lpc_seg_finite_value (lpc_seg_role_value nl is_cont c d (lp_ieval l eta)),
    lpc_seg_finite_value (lpc_seg_role_value nr is_cont c d (lp_ieval r eta)))\<in>qrstep False Q R"
proof -
  let ?eta = "\<lambda>x. map_lp_iterm d id (eta x)"
  have lhs: "lpc_seg_role_value nl is_cont c d (lp_ieval l eta) = lp_ieval (Fun f ts) ?eta"
    using lpc_seg_role_eval[OF left_shape, of c d eta] by (simp only: left)
  have rhs: "lpc_seg_role_value nr is_cont c d (lp_ieval r eta) =
      lp_ieval (lpc_seg_role_term nr is_cont c d r) ?eta"
    by (rule lpc_seg_role_eval[OF right_shape])
  have finite': "lp_seg_ground (lp_ieval (Fun f ts) ?eta)"
    using lpc_seg_role_finite[OF finite, of nl is_cont c d] by (simp only: lhs)
  have vals: "\<And>x. lp_constructor_value C (?eta x)"
    by (rule lp_constructor_value_map[OF range])
  show ?thesis unfolding lhs rhs
    by (rule lpc_seg_constructor_root[OF rule variables finite' symbols vals roots])
qed

definition lpc_seg_check_encoded_pair where
  "lpc_seg_check_encoded_pair nl nr is_cont c d C R l r =
    (vars_term r \<subseteq> vars_term l \<and>
      lpc_seg_role_shape nl is_cont l \<and> lpc_seg_role_shape nr is_cont r \<and>
      (let left=lpc_seg_role_term nl is_cont c d l;
           right=lpc_seg_role_term nr is_cont c d r in
       (left,right)\<in>R \<and> vars_term right \<subseteq> vars_term left \<and>
       (case left of Var x \<Rightarrow> False | Fun f ts \<Rightarrow>
         list_all (\<lambda>t. funs_term t \<subseteq> C) ts)))"

theorem lpc_seg_checked_encoded_pair:
  assumes checked: "lpc_seg_check_encoded_pair nl nr is_cont c d C R l r"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "(lpc_seg_finite_value (lpc_seg_role_value nl is_cont c d (lp_ieval l eta)),
    lpc_seg_finite_value (lpc_seg_role_value nr is_cont c d (lp_ieval r eta)))\<in>qrstep False Q R"
proof -
  obtain f ts where left: "lpc_seg_role_term nl is_cont c d l=Fun f ts"
    using checked by (auto simp: lpc_seg_check_encoded_pair_def Let_def split: term.splits)
  have ls: "lpc_seg_role_shape nl is_cont l" and rs: "lpc_seg_role_shape nr is_cont r"
    and rule: "(Fun f ts,lpc_seg_role_term nr is_cont c d r)\<in>R"
    and vars: "vars_term (lpc_seg_role_term nr is_cont c d r) \<subseteq> vars_term (Fun f ts)"
    and symbols: "\<And>t. t\<in>set ts \<Longrightarrow> funs_term t \<subseteq> C"
    using checked by (auto simp: lpc_seg_check_encoded_pair_def Let_def left list_all_iff)
  show ?thesis by (rule lpc_seg_encoded_root[OF ls rs left rule vars finite symbols range roots])
qed

fun lpc_seg_constructor_term where
  "lpc_seg_constructor_term C (Var x) = True"
| "lpc_seg_constructor_term C (Fun f ts) =
    (List.member C f \<and> list_all (lpc_seg_constructor_term C) ts)"

lemma lpc_seg_constructor_term_iff:
  "lpc_seg_constructor_term C t \<longleftrightarrow> funs_term t \<subseteq> set C"
  by (induct t) (auto simp: List.member_iff list_all_iff)

definition lpc_seg_check_encoded_pair_list where
  "lpc_seg_check_encoded_pair_list nl nr is_cont c d C R l r =
    (vars_term r \<subseteq> vars_term l \<and>
      lpc_seg_role_shape nl is_cont l \<and> lpc_seg_role_shape nr is_cont r \<and>
      (let left=lpc_seg_role_term nl is_cont c d l;
           right=lpc_seg_role_term nr is_cont c d r in
       List.member R (left,right) \<and> vars_term right \<subseteq> vars_term left \<and>
       (case left of Var x \<Rightarrow> False | Fun f ts \<Rightarrow>
         list_all (lpc_seg_constructor_term C) ts)))"

lemma lpc_seg_check_encoded_pair_list_sound:
  "lpc_seg_check_encoded_pair_list nl nr is_cont c d C R l r \<longleftrightarrow>
    lpc_seg_check_encoded_pair nl nr is_cont c d (set C) (set R) l r"
  by (simp add: lpc_seg_check_encoded_pair_list_def lpc_seg_check_encoded_pair_def
    List.member_iff lpc_seg_constructor_term_iff list_all_iff split: term.splits)

lemma lpc_seg_checked_pair_finite:
  assumes checked: "lpc_seg_check_encoded_pair nl nr is_cont c d C R l r"
    and finite: "lp_seg_ground (lp_ieval l eta)"
  shows "lp_seg_ground (lp_ieval r eta)"
  using checked finite by (auto simp: lpc_seg_check_encoded_pair_def lp_seg_ground_eval)

theorem lpc_seg_checked_call:
  assumes checked: "lpc_seg_check_encoded_pair 1 2 is_cont c d C R l (Fun u (child#captured))"
    and cont: "is_cont u"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "lp_seg_ground (lp_ieval child eta) \<and>
    list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) captured \<and>
    (lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lp_ieval l eta)),
      (More (c u) [] \<box> (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) captured))
        \<langle>lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lp_ieval child eta))\<rangle>)
      \<in>qrstep False Q R"
proof -
  have right: "lp_seg_ground (lp_ieval (Fun u (child#captured)) eta)"
    by (rule lpc_seg_checked_pair_finite[OF checked finite])
  have first: "lp_seg_ground (lp_ieval child eta)"
    and rest: "list_all lp_seg_ground (map (\<lambda>t. lp_ieval t eta) captured)"
    using right by simp_all
  have equal: "lpc_seg_finite_value (lpc_seg_role_value 2 is_cont c d (lp_ieval (Fun u (child#captured)) eta)) =
    (More (c u) [] \<box> (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) captured))
      \<langle>lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lp_ieval child eta))\<rangle>"
    using lpc_seg_role_continuation_context[where is_cont=is_cont and u=u and n=1 and c=c and d=d, OF cont first rest]
    by (simp add: numeral_eq_Suc map_map)
  have step: "(lpc_seg_finite_value (lpc_seg_role_value 1 is_cont c d (lp_ieval l eta)),
    lpc_seg_finite_value (lpc_seg_role_value 2 is_cont c d (lp_ieval (Fun u (child#captured)) eta)))
      \<in>qrstep False Q R"
    by (rule lpc_seg_checked_encoded_pair[OF checked finite range roots])
  have captured: "list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) captured"
    using rest by (simp add: list_all_iff)
  show ?thesis using first captured step by (simp only: equal)
qed

end
