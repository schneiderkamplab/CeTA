theory Relative_ADP_DP_Argument_Filter
  imports Dependency_Pair_Injective_Renaming
    Proof_Checker_Base.Check_Termination Ord.Argument_Filter
begin

text \<open>Argument filtering is a chain simulation for ordinary, non-minimal
DP problems. Unlike whole-TRS filtering it need not preserve every rewrite
step strictly: connecting R steps may disappear, while every root P step
still supplies one dependency pair. No normal-form or minimality premise is
introduced by this transformation.\<close>

lemma finite_plain_dpp_argument_filter:
  fixes pi :: "'f afs"
  assumes finite: "finite_dpp
    (False, False, af_rule pi ` P, {}, {}, {}, af_rule pi ` R)"
  shows "finite_dpp (False, False, P, {}, {}, {}, R)"
proof (rule ccontr)
  assume "\<not> finite_dpp (False, False, P, {}, {}, {}, R)"
  then obtain s t sigma where chain:
    "min_ichain (False, False, P, {}, {}, {}, R) s t sigma"
    unfolding finite_dpp_def by blast
  have pairs: "\<And>n. (s n, t n) \<in> P"
    and links: "\<And>n. (t n \<cdot> sigma n, s (Suc n) \<cdot> sigma (Suc n))
      \<in> (Trs.rstep R)^*"
    using chain unfolding min_ichain.simps ichain.simps by auto
  let ?s = "\<lambda>n. af_term pi (s n)"
  let ?t = "\<lambda>n. af_term pi (t n)"
  let ?sigma = "\<lambda>n x. af_term pi (sigma n x)"
  have filtered_pairs: "\<And>n. (?s n, ?t n) \<in> af_rule pi ` P"
    using pairs unfolding af_rule_def afs_rule_def af_term_def by force
  have filtered_links: "\<And>n. (?t n \<cdot> ?sigma n,
      ?s (Suc n) \<cdot> ?sigma (Suc n)) \<in> (Trs.rstep (af_rule pi ` R))^*"
    using af_rsteps[OF links, of pi] by (simp add: af_subst)
  have "min_ichain (False, False, af_rule pi ` P, {}, {}, {}, af_rule pi ` R)
      ?s ?t ?sigma"
    unfolding min_ichain.simps ichain.simps
    using filtered_pairs filtered_links by simp
  with finite show False unfolding finite_dpp_def by blast
qed

context fixes
  I :: "('tp, ('f::{showl,compare_order,countable},nat list) lab,string) tp_ops"
  and J :: "('dpp, ('f,nat list) lab,string) dpp_ops"
begin

definition check_filtered_plain_dpp where
  "check_filtered_plain_dpp filters P R certificate =
    (case afs_of filters of None \<Rightarrow> error (showsl_lit (STR ''invalid DP argument filter''))
    | Some filtering \<Rightarrow> check_dp_termination_proof I J False
        (showsl_lit (STR ''filtered non-minimal DP problem''))
        (mk_dpp J (False,False,af_rules filtering P,[],[],[],af_rules filtering R)) certificate)"

lemma check_filtered_plain_dpp_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and ok: "isOK (check_filtered_plain_dpp filters P R certificate)"
  shows "finite_dpp (False,False,set P,{},{},{},set R)"
proof -
  from ok obtain filtering where af: "afs_of filters = Some filtering"
    unfolding check_filtered_plain_dpp_def
    by (cases "afs_of filters") auto
  from ok af have checked: "isOK (check_dp_termination_proof I J False
      (showsl_lit (STR ''filtered non-minimal DP problem''))
      (mk_dpp J (False,False,af_rules filtering P,[],[],[],af_rules filtering R)) certificate)"
    unfolding check_filtered_plain_dpp_def by simp
  from check_dp_termination_proof[OF I J checked]
  have "finite_dpp (False,False,af_rule filtering ` set P,{},{},{},af_rule filtering ` set R)"
    by (simp add: dpp_spec.mk_sound[OF J])
  then show ?thesis by (rule finite_plain_dpp_argument_filter)
qed

end

end
