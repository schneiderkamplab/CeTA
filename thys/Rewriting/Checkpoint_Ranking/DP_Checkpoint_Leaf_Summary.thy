theory DP_Checkpoint_Leaf_Summary
 imports DP_Checkpoint_Leaf_Effect DP_Checkpoint_Effect_Schema
begin

definition checkpoint_leaf_outputs where
 "checkpoint_leaf_outputs L p s = (if vars_term p={} \<and> L\<notin>funs_term p
   then {t. checkpoint_leaf_relation L s t} else UNIV)"

lemma checkpoint_leaf_outputs_leaf:
 "Fun L []\<in>checkpoint_leaf_outputs L p (Fun L [])"
 by (simp add: checkpoint_leaf_outputs_def checkpoint_leaf_relation_identity_leaf)
lemma checkpoint_leaf_outputs_constructor:
 "f\<noteq>L \<Longrightarrow> list_all2 (\<lambda>x y. y\<in>checkpoint_leaf_outputs L p x) xs ys \<Longrightarrow>
 Fun f ys\<in>checkpoint_leaf_outputs L p (Fun f xs)"
 by (auto simp: checkpoint_leaf_outputs_def intro: checkpoint_leaf_relation_constructor split: if_splits)

lemma checkpoint_leaf_template_instance:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes "vars_term t\<subseteq>{0}" "funs_term t\<subseteq>C-{L}"
 and "vars_term (checkpoint_skeleton C (sigma 0))={}"
 and "L\<notin>funs_term (checkpoint_skeleton C (sigma 0))"
 shows "vars_term (checkpoint_skeleton C (t\<cdot>sigma))={} \<and>
   L\<notin>funs_term (checkpoint_skeleton C (t\<cdot>sigma))"
 using assms
proof (induct t)
 case (Var x) then show ?case by auto
next
 case (Fun f ts)
 have root: "f\<in>C" "f\<noteq>L" using Fun.prems by auto
 have children: "\<And>x. x\<in>set ts \<Longrightarrow>
 vars_term (checkpoint_skeleton C (x\<cdot>sigma))={} \<and>
 L\<notin>funs_term (checkpoint_skeleton C (x\<cdot>sigma))"
 proof -
  fix x assume member: "x\<in>set ts"
  have vars: "vars_term x\<subseteq>{0}" and funs: "funs_term x\<subseteq>C-{L}"
   using Fun.prems member by auto
  show "vars_term (checkpoint_skeleton C (x\<cdot>sigma))={} \<and>
   L\<notin>funs_term (checkpoint_skeleton C (x\<cdot>sigma))"
   by (rule Fun.hyps[OF member vars funs Fun.prems(3,4)])
 qed
 show ?case using root children by auto
qed

lemma checkpoint_leaf_template_output:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes "vars_term t\<subseteq>{0}" "funs_term t\<subseteq>C-{L}"
 shows "checkpoint_skeleton C (t\<cdot>sigma)\<in>checkpoint_leaf_outputs L (checkpoint_skeleton C (sigma 0)) (Fun L [])"
 using checkpoint_leaf_template_instance[OF assms, of sigma]
 by (auto simp: checkpoint_leaf_outputs_def intro: checkpoint_leaf_relation_replace)

definition checkpoint_leaf_summary_rules where
 "checkpoint_leaf_summary_rules L N Z S ein eout spine_in sout resume head tail templates =
 checkpoint_effect_rules L N Z S ein eout spine_in sout resume head tail @
 map (\<lambda>t. (Fun ein [Fun L [],Var 0],Fun eout [Fun L [],t,Var 0])) templates"

definition check_checkpoint_leaf_summary where
 "check_checkpoint_leaf_summary C L N Z S ein eout spine_in sout resume head tail templates support witnesses =
 (distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail] \<and> {L,N,Z,S}\<subseteq>C \<and>
 list_all (\<lambda>t. vars_term t\<subseteq>{0} \<and> funs_term t\<subseteq>C-{L}) templates \<and>
 list_all (checkpoint_skeleton_safe_rule C) support \<and>
 list_all2 (check_checkpoint_schema_rule {ein,eout,spine_in,sout,resume,head,tail}
   (checkpoint_leaf_summary_rules L N Z S ein eout spine_in sout resume head tail templates)) support witnesses)"

lemma checkpoint_leaf_summary_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes distinct: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail]"
 and constructors: "{L,N,Z,S}\<subseteq>C"
 and templates: "list_all (\<lambda>t. vars_term t\<subseteq>{0} \<and> funs_term t\<subseteq>C-{L}) templates"
 and rule: "(l,r)\<in>set (checkpoint_leaf_summary_rules L N Z S ein eout spine_in sout resume head tail templates)"
 shows "checkpoint_interpret C (checkpoint_effect_algebra (checkpoint_leaf_outputs L) N S ein eout spine_in sout resume head tail) (r\<cdot>sigma)
 \<subseteq> checkpoint_interpret C (checkpoint_effect_algebra (checkpoint_leaf_outputs L) N S ein eout spine_in sout resume head tail) (l\<cdot>sigma)"
proof (cases "(l,r)\<in>set (checkpoint_effect_rules L N Z S ein eout spine_in sout resume head tail)")
 case True
 show ?thesis
  by (rule checkpoint_effect_rules_sound[where E="checkpoint_leaf_outputs L", OF distinct constructors checkpoint_leaf_outputs_leaf _ _ _ True];
   rule checkpoint_leaf_outputs_constructor; use distinct in auto)
next
 case False
 obtain t where t: "t\<in>set templates" "l=Fun ein [Fun L [],Var 0]" "r=Fun eout [Fun L [],t,Var 0]"
  using rule False by (auto simp: checkpoint_leaf_summary_rules_def)
 have safe: "vars_term t\<subseteq>{0}" "funs_term t\<subseteq>C-{L}"
  using templates t(1) by (auto simp: list_all_iff)
 show ?thesis using checkpoint_leaf_template_output[OF safe, of sigma] distinct constructors
  by (auto simp: t checkpoint_effect_algebra_def)
qed

lemma checked_checkpoint_leaf_success:
 fixes support :: "('f,'v) rule list"
 and input param copied result returned_param :: "('f,'v) term"
 assumes checked: "check_checkpoint_leaf_summary C L N Z S ein eout spine_in sout resume head tail templates support witnesses"
 and success: "(Fun ein [input,param],Fun eout [copied,result,returned_param])\<in>(Trs.rstep (set support))\<^sup>*"
 and closed: "vars_term (checkpoint_skeleton C param)={}"
 and leaf_free: "L\<notin>funs_term (checkpoint_skeleton C param)"
 shows "checkpoint_leaf_relation L (checkpoint_skeleton C input) (checkpoint_skeleton C result)"
proof -
 have safe: "checkpoint_skeleton_safe C (set support)"
 and distinct: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail]"
 and constructors: "{L,N,Z,S}\<subseteq>C"
 and templates: "list_all (\<lambda>t. vars_term t\<subseteq>{0} \<and> funs_term t\<subseteq>C-{L}) templates"
 and table: "list_all2 (check_checkpoint_schema_rule {ein,eout,spine_in,sout,resume,head,tail}
   (checkpoint_leaf_summary_rules L N Z S ein eout spine_in sout resume head tail templates)) support witnesses"
  using checked by (auto simp: check_checkpoint_leaf_summary_def checkpoint_skeleton_safe_list)
 have mono: "\<And>l r (sigma::'v \<Rightarrow> ('f,'v) term). (l,r)\<in>set support \<Longrightarrow>
 checkpoint_interpret C (checkpoint_effect_algebra (checkpoint_leaf_outputs L) N S ein eout spine_in sout resume head tail) (r\<cdot>sigma)
 \<subseteq> checkpoint_interpret C (checkpoint_effect_algebra (checkpoint_leaf_outputs L) N S ein eout spine_in sout resume head tail) (l\<cdot>sigma)"
  by (rule checkpoint_schema_table_sound[OF _ _ table])
   (rule checkpoint_leaf_summary_rules_sound[OF distinct constructors templates], assumption,
    rule checkpoint_effect_unrestricted_lhs, assumption, assumption)
 have "checkpoint_skeleton C result\<in>checkpoint_leaf_outputs L (checkpoint_skeleton C param) (checkpoint_skeleton C input)"
  by (rule checkpoint_effect_success[OF safe _ mono success]) (use distinct in auto)
 then show ?thesis using closed leaf_free by (simp add: checkpoint_leaf_outputs_def)
qed

ML \<open>
val thms = @{thms checkpoint_leaf_template_instance checkpoint_leaf_template_output
 checkpoint_leaf_summary_rules_sound checked_checkpoint_leaf_success};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted leaf summary" else ();
\<close>
end
