theory Higher_Order_Blocked_Calls
  imports "Higher_Order_Functional_Access.Higher_Order_Functional_Access_Schema"
begin

text \<open>A call whose arguments satisfy a reduction-stable blocking invariant
is computable when its arguments are computable.  The invariant must exclude
all root steps, not just syntactic matches at the current state.  This is a
semantic foundation for conservative higher-order graph exclusions; it does
not itself add an executable acceptance path.\<close>

fun ho_is_abstraction where
  "ho_is_abstraction (HAbs A t)=True"
| "ho_is_abstraction t=False"

definition ho_lambda_clash where
  "ho_lambda_clash xs ls = (\<exists>i<length xs. i<length ls \<and>
    ho_is_abstraction (xs!i) \<and> (\<exists>d. ho_application_head (ls!i)=HConst d))"

definition ho_lambda_blocked where
  "ho_lambda_blocked R c xs = list_all (\<lambda>(G,l,r).
    ho_application_head (ho_erase_pattern l)\<noteq>HConst c \<or>
    ho_lambda_clash xs (ho_spine_arguments (ho_erase_pattern l))) R"

lemma ho_lambda_clash_code [code]:
  "ho_lambda_clash xs ls = list_ex (\<lambda>i. i<length ls \<and>
    ho_is_abstraction (xs!i) \<and>
    (case ho_application_head (ls!i) of HConst d \<Rightarrow> True | _ \<Rightarrow> False))
    [0..<length xs]"
proof -
  have shape: "(case t of HConst d \<Rightarrow> True | _ \<Rightarrow> False) =
      (\<exists>d. t=HConst d)" for t
    by (cases t) auto
  show ?thesis by (auto simp: ho_lambda_clash_def list_ex_iff shape)
qed

context ho_source_accessible_reducibility
begin

lemma abstraction_source_reduct:
  assumes abs: "ho_is_abstraction t" and step: "ho_step S V R B t u"
  shows "ho_is_abstraction u"
proof -
  obtain A v where t: "t=HAbs A v" using abs by (cases t) auto
  show ?thesis using step unfolding t
    by (cases rule: ho_step.cases) (auto dest: rule_instance_constant_head)
qed

lemma lambda_clash_arguments_step:
  assumes clash: "ho_lambda_clash xs ls"
    and step: "ho_arguments_step S V R B xs ys"
  shows "ho_lambda_clash ys ls"
proof -
  obtain us v vs w where xs: "xs=us@v#vs" and ys: "ys=us@w#vs"
    and vw: "ho_step S V R B v w"
    using step unfolding ho_arguments_step_def by blast
  obtain i where i: "i<length xs" "i<length ls" and abs: "ho_is_abstraction (xs!i)"
    and head: "\<exists>d. ho_application_head (ls!i)=HConst d"
    using clash unfolding ho_lambda_clash_def by blast
  have update: "ys=xs[length us:=w]" by (simp add: xs ys list_update_append)
  have same_length: "length ys=length xs" by (simp add: xs ys)
  have out: "ho_is_abstraction (ys!i)"
  proof (cases "i=length us")
    case True
    have av: "ho_is_abstraction v" using abs True xs by simp
    have aw: "ho_is_abstraction w" by (rule abstraction_source_reduct[OF av vw])
    show ?thesis using True ys aw by simp
  next
    case False
    show ?thesis using abs False update by simp
  qed
  show ?thesis unfolding ho_lambda_clash_def
    by (rule exI[of _ i]) (use i head out same_length in simp)
qed

lemma lambda_blocked_arguments_step:
  assumes block: "ho_lambda_blocked R c xs"
    and step: "ho_arguments_step S V R B xs ys"
  shows "ho_lambda_blocked R c ys"
  using block unfolding ho_lambda_blocked_def list_all_iff
  by (auto intro: lambda_clash_arguments_step[OF _ step])

lemma lambda_blocked_no_root:
  assumes block: "ho_lambda_blocked R c xs"
  shows "\<not>ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
proof
  assume root: "ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
  obtain G l r s where member: "(G,l,r)\<in>set R"
    and inst: "ho_instantiate s 0 l=Some (ho_apply_terms (HConst c) xs)"
    using root unfolding ho_root_step_def by blast
  have head: "ho_application_head (ho_erase_pattern l)=HConst c"
    using rule_instance_head_spine(1)[OF member inst] by simp
  have zero_l: "ho_zero_arity_pattern l"
    using zero member unfolding ho_zero_arity_rules_def by auto
  have eq: "ho_subst s 0 (ho_erase_pattern l)=ho_apply_terms (HConst c) xs"
    using inst ho_zero_arity_instantiate[OF zero_l, of s 0] by simp
  have args: "map (ho_subst s 0) (ho_spine_arguments (ho_erase_pattern l))=xs"
    using ho_constant_arguments_subst[OF head, of s 0] eq by simp
  have clash: "ho_lambda_clash xs (ho_spine_arguments (ho_erase_pattern l))"
    using block member head by (auto simp: ho_lambda_blocked_def list_all_iff)
  obtain i d where i: "i<length xs" "i<length (ho_spine_arguments (ho_erase_pattern l))"
    and abs: "ho_is_abstraction (xs!i)"
    and constant_head: "ho_application_head (ho_spine_arguments (ho_erase_pattern l)!i)=HConst d"
    using clash unfolding ho_lambda_clash_def by blast
  have const: "ho_application_head (xs!i)=HConst d"
    using ho_constant_head_substitution[OF constant_head, of s 0] args i by (metis nth_map)
  show False using abs const by (cases "xs!i") auto
qed

theorem blocked_calls_computable:
  assumes arities: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity d"
    and bound: "arity c\<le>length (ho_argument_types T)"
    and symbol: "ho_lookup S c=Some T"
    and stable: "\<And>xs ys. P xs \<Longrightarrow>
      ho_arguments_step S V R B xs ys \<Longrightarrow> P ys"
    and blocked: "\<And>xs u. P xs \<Longrightarrow>
      \<not>ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
    and invariant: "P xs"
    and args: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
  shows "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
proof -
  let ?Q = "priority_call_order (\<lambda>_. 0) (\<lambda>i. i)"
  have all: "P (snd p) \<longrightarrow>
      list_all2 source_candidate (take (arity c) (ho_argument_types T)) (snd p) \<longrightarrow>
      source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) (snd p))"
    for p :: "nat \<times> ho_term list"
  proof (induction p rule: wf_induct[OF wf_priority_call_order[of "\<lambda>_. 0" "\<lambda>i. i"]])
    case (1 p)
    show ?case
    proof (intro impI)
      assume inv: "P (snd p)"
        and aa: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) (snd p)"
      have types: "list_all2 (\<lambda>A x. ho_typeof S V B x=Some A)
          (take (arity c) (ho_argument_types T)) (snd p)"
        by (rule list_all2_mono[OF aa]) (rule source.candidate_typed)
      have ty: "ho_typeof S V B (ho_apply_terms (HConst c) (snd p))=
          Some (ho_drop_type (arity c) T)"
        by (rule ho_apply_prefix_type[OF _ bound types]) (use symbol in simp)
      have len: "length (snd p)=arity c"
        using list_all2_lengthD[OF aa] bound by simp
      have reducts: "source_candidate (ho_drop_type (arity c) T) u"
        if st: "ho_step S V R B (ho_apply_terms (HConst c) (snd p)) u" for u
      proof -
        have split: "ho_root_step S V R B (ho_apply_terms (HConst c) (snd p)) u \<or>
            (\<exists>ys. ho_arguments_step S V R B (snd p) ys \<and>
              u=ho_apply_terms (HConst c) ys)"
          by (rule source_call_reduct[where a=arity])
             (blast intro: arities, use len in arith, rule st)
        obtain ys where step: "ho_arguments_step S V R B (snd p) ys"
          and eq: "u=ho_apply_terms (HConst c) ys"
          using split blocked[OF inv] by blast
        have small: "((fst p,ys),p)\<in>?Q"
          using candidate_argument_step_order[where c="fst p" and prec="\<lambda>_. 0"
            and priority="\<lambda>i. i", OF aa step] by simp
        have ay: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) ys"
          by (rule candidate_arguments_step[OF aa step])
        have py: "P ys" by (rule stable[OF inv step])
        show ?thesis using 1 small ay py eq by auto
      qed
      have neu: "ho_saturated_neutral R (ho_apply_terms (HConst c) (snd p))"
      proof (unfold ho_saturated_neutral_def, intro conjI allI impI)
        fix A t
        show "ho_apply_terms (HConst c) (snd p)\<noteq>HAbs A t"
        proof
          assume eq: "ho_apply_terms (HConst c) (snd p)=HAbs A t"
          have "ho_application_head (ho_apply_terms (HConst c) (snd p))=HConst c" by simp
          then show False by (simp add: eq)
        qed
      next
        fix G l r assume member: "(G,l,r)\<in>set R"
          and head: "ho_application_head (ho_erase_pattern l)=
            ho_application_head (ho_apply_terms (HConst c) (snd p))"
        have hc: "ho_application_head (ho_erase_pattern l)=HConst c" using head by simp
        show "ho_spine_length (ho_erase_pattern l)\<le>
            ho_spine_length (ho_apply_terms (HConst c) (snd p))"
          using arities[OF member hc] len by simp
      qed
      show "source_candidate (ho_drop_type (arity c) T)
          (ho_apply_terms (HConst c) (snd p))"
      proof (rule source_candidate_saturated[OF ty neu _ reducts])
        fix x assume "x\<in>set (ho_spine_arguments (ho_apply_terms (HConst c) (snd p)))"
        then have "x\<in>set (snd p)" by simp
        then show "\<exists>A. source_candidate A x"
          using aa by (metis list_all2_nthD2 in_set_conv_nth)
      qed
    qed
  qed
  show ?thesis using all[of "(c,xs)"] invariant args by simp
qed

corollary lambda_blocked_calls_computable:
  assumes arities: "\<And>G l r d. (G,l,r)\<in>set R \<Longrightarrow>
      ho_application_head (ho_erase_pattern l)=HConst d \<Longrightarrow>
      ho_spine_length (ho_erase_pattern l)=arity d"
    and bound: "arity c\<le>length (ho_argument_types T)"
    and symbol: "ho_lookup S c=Some T"
    and block: "ho_lambda_blocked R c xs"
    and args: "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs"
  shows "source_candidate (ho_drop_type (arity c) T) (ho_apply_terms (HConst c) xs)"
proof (rule blocked_calls_computable[where P="ho_lambda_blocked R c" and arity=arity])
  show "ho_spine_length (ho_erase_pattern l)=arity d"
    if "(G,l,r)\<in>set R" "ho_application_head (ho_erase_pattern l)=HConst d" for G l r d
    by (rule arities[OF that])
  show "arity c\<le>length (ho_argument_types T)" by (rule bound)
  show "ho_lookup S c=Some T" by (rule symbol)
  show "ho_lambda_blocked R c ys"
    if "ho_lambda_blocked R c xs" "ho_arguments_step S V R B xs ys" for xs ys
    by (rule lambda_blocked_arguments_step[OF that])
  show "\<not>ho_root_step S V R B (ho_apply_terms (HConst c) xs) u"
    if "ho_lambda_blocked R c xs" for xs u
    by (rule lambda_blocked_no_root[OF that])
  show "ho_lambda_blocked R c xs" by (rule block)
  show "list_all2 source_candidate (take (arity c) (ho_argument_types T)) xs" by (rule args)
qed

end

end
