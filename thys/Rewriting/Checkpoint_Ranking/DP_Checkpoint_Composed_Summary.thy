theory DP_Checkpoint_Composed_Summary
 imports DP_Checkpoint_Effect_Composition
begin

lemma checkpoint_composed_leaf_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes distinct: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail]"
 and constructors: "{L,N,Z,S}\<subseteq>C"
 and templates: "list_all (\<lambda>t. vars_term t\<subseteq>{0} \<and> funs_term t\<subseteq>C-{L}) templates"
 and rule: "(l,r)\<in>set (checkpoint_leaf_summary_rules L N Z S ein eout spine_in sout resume head tail templates)"
 shows "checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (r\<cdot>sigma)
 \<subseteq>checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (l\<cdot>sigma)"
proof (cases "(l,r)\<in>set (checkpoint_effect_rules L N Z S ein eout spine_in sout resume head tail)")
 case True
 have short: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail]" using distinct by auto
 have nil: "\<And>p. Fun Z []\<in>checkpoint_leaf_outputs L p (Fun Z [])"
  by (rule checkpoint_leaf_outputs_constructor; use distinct in auto)
 have node: "\<And>p x y. y\<in>checkpoint_leaf_outputs L p x \<Longrightarrow>
  Fun N [y]\<in>checkpoint_leaf_outputs L p (Fun N [x])"
  by (rule checkpoint_leaf_outputs_constructor; use distinct in auto)
 have cons: "\<And>p x y xs ys. y\<in>checkpoint_leaf_outputs L p x \<Longrightarrow> ys\<in>checkpoint_leaf_outputs L p xs \<Longrightarrow>
  Fun S [y,ys]\<in>checkpoint_leaf_outputs L p (Fun S [x,xs])"
  by (rule checkpoint_leaf_outputs_constructor; use distinct in auto)
 show ?thesis
  apply (rule checkpoint_effect_local_sound[where E="checkpoint_leaf_outputs L", OF short constructors checkpoint_leaf_outputs_leaf nil node cons _ True])
  apply (assumption | rule checkpoint_composed_helper_agrees[OF distinct])+
  done
next
 case False
 obtain t where t: "t\<in>set templates" "l=Fun ein [Fun L [],Var 0]" "r=Fun eout [Fun L [],t,Var 0]"
  using rule False by (auto simp: checkpoint_leaf_summary_rules_def)
 have safe: "vars_term t\<subseteq>{0}" "funs_term t\<subseteq>C-{L}"
  using templates t(1) by (auto simp: list_all_iff)
 show ?thesis using checkpoint_leaf_template_output[OF safe, of sigma] distinct constructors
  by (auto simp: t checkpoint_composed_algebra_def checkpoint_effect_algebra_def)
qed

definition checkpoint_composed_rules where
 "checkpoint_composed_rules L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates =
 checkpoint_leaf_summary_rules L N Z S ein eout spine_in sout resume head tail templates @
 checkpoint_list_rules N Z S lin lout lhead ltail ein eout"

definition check_checkpoint_composed_summary where
 "check_checkpoint_composed_summary C L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates support witnesses =
 (distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail] \<and> {L,N,Z,S}\<subseteq>C \<and>
 list_all (\<lambda>t. vars_term t\<subseteq>{0} \<and> funs_term t\<subseteq>C-{L}) templates \<and>
 list_all (checkpoint_skeleton_safe_rule C) support \<and>
 list_all2 (check_checkpoint_schema_rule {ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail}
   (checkpoint_composed_rules L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates)) support witnesses)"

lemma checkpoint_composed_rules_sound:
 fixes sigma :: "nat \<Rightarrow> ('f,'v) term"
 assumes distinct: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail]"
 and constructors: "{L,N,Z,S}\<subseteq>C"
 and templates: "list_all (\<lambda>t. vars_term t\<subseteq>{0} \<and> funs_term t\<subseteq>C-{L}) templates"
 and rule: "(l,r)\<in>set (checkpoint_composed_rules L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates)"
 shows "checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (r\<cdot>sigma)
 \<subseteq>checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (l\<cdot>sigma)"
proof (cases "(l,r)\<in>set (checkpoint_leaf_summary_rules L N Z S ein eout spine_in sout resume head tail templates)")
 case True
 show ?thesis by (rule checkpoint_composed_leaf_rules_sound[OF distinct constructors templates True])
next
 case False
 have member: "(l,r)\<in>set (checkpoint_list_rules N Z S lin lout lhead ltail ein eout)"
  using rule False by (auto simp: checkpoint_composed_rules_def)
 have c: "{N,Z,S}\<subseteq>C" using constructors by auto
 show ?thesis
  apply (rule checkpoint_composed_list_rules_sound[where E="checkpoint_leaf_outputs L", OF distinct c _ _ member])
   apply (rule checkpoint_leaf_outputs_list_nil; use distinct in auto)
  apply (rule checkpoint_leaf_outputs_list_cons; use distinct in auto)
  done
qed

lemma checkpoint_composed_unrestricted:
 "f\<notin>{ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail} \<Longrightarrow>
 checkpoint_interpret C (checkpoint_composed_algebra E N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (Fun f ts)=UNIV"
 by (simp add: checkpoint_composed_algebra_def checkpoint_effect_algebra_def)

lemma checked_checkpoint_composed_success:
 fixes support :: "('f,'v) rule list" and input param copied result returned_param :: "('f,'v) term"
 assumes checked: "check_checkpoint_composed_summary C L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates support witnesses"
 and success: "(Fun lin [input,param],Fun lout [copied,result,returned_param])\<in>(Trs.rstep (set support))\<^sup>*"
 and closed: "vars_term (checkpoint_skeleton C param)={}"
 and leaf_free: "L\<notin>funs_term (checkpoint_skeleton C param)"
 shows "checkpoint_leaf_relation L (checkpoint_skeleton C input) (checkpoint_skeleton C result)"
proof -
 have safe: "checkpoint_skeleton_safe C (set support)"
 and distinct: "distinct [L,N,Z,S,ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail]"
 and constructors: "{L,N,Z,S}\<subseteq>C"
 and templates: "list_all (\<lambda>t. vars_term t\<subseteq>{0} \<and> funs_term t\<subseteq>C-{L}) templates"
 and table: "list_all2 (check_checkpoint_schema_rule {ein,eout,spine_in,sout,resume,head,tail,lin,lout,lhead,ltail}
   (checkpoint_composed_rules L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates)) support witnesses"
  using checked by (auto simp: check_checkpoint_composed_summary_def checkpoint_skeleton_safe_list)
 have mono: "\<And>l r (sigma::'v \<Rightarrow> ('f,'v) term). (l,r)\<in>set support \<Longrightarrow>
 checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (r\<cdot>sigma)
 \<subseteq>checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (l\<cdot>sigma)"
  by (rule checkpoint_schema_table_sound[OF _ _ table])
   (rule checkpoint_composed_rules_sound[OF distinct constructors templates], assumption,
    rule checkpoint_composed_unrestricted, assumption, assumption)
 have included: "checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (Fun lout [copied,result,returned_param])
 \<subseteq>checkpoint_interpret C (checkpoint_composed_algebra (checkpoint_leaf_outputs L) N Z S ein eout spine_in sout resume head tail lin lout lhead ltail) (Fun lin [input,param])"
  by (rule checkpoint_interpret_rsteps[OF safe checkpoint_composed_algebra_mono mono success])
 show ?thesis using included distinct closed leaf_free
  by (auto simp: checkpoint_composed_algebra_def checkpoint_leaf_outputs_def)
qed

lemma checked_checkpoint_composed_list_return:
 fixes support :: "('f,'v) rule list" and input param copied result returned_param :: "('f,'v) term"
 assumes checked: "check_checkpoint_composed_summary C L N Z S ein eout spine_in sout resume head tail lin lout lhead ltail templates support witnesses"
 and domain: "check_checkpoint_list_domain C N Z S lin lout lhead ltail ein eout support domain_witnesses"
 and success: "(Fun lin [input,param],Fun lout [copied,result,returned_param])\<in>(Trs.rstep (set support))\<^sup>*"
 and closed: "vars_term (checkpoint_skeleton C param)={}"
 and leaf_free: "L\<notin>funs_term (checkpoint_skeleton C param)"
 shows "\<exists>xs ys. checkpoint_skeleton C input=checkpoint_encoded_list N Z S xs \<and>
 checkpoint_skeleton C result=checkpoint_encoded_list N Z S ys \<and>
 list_all2 (checkpoint_leaf_relation L) xs ys \<and> length ys=length xs \<and>
 (Inr (map (checkpoint_rank_view L) ys),Inr (checkpoint_rank_view L h#map (checkpoint_rank_view L) xs))\<in>lpp_forest_call_order"
proof -
 obtain xs where before: "checkpoint_skeleton C input=checkpoint_encoded_list N Z S xs"
  using checked_checkpoint_list_domain[OF domain success] by blast
 have effect: "checkpoint_leaf_relation L (checkpoint_encoded_list N Z S xs) (checkpoint_skeleton C result)"
  using checked_checkpoint_composed_success[OF checked success closed leaf_free] before by simp
 have distinct: "distinct [L,N,Z,S]" using checked by (auto simp: check_checkpoint_composed_summary_def)
 obtain ys where after: "checkpoint_skeleton C result=checkpoint_encoded_list N Z S ys"
 and related: "list_all2 (checkpoint_leaf_relation L) xs ys"
  using effect checkpoint_encoded_list_effect_exact[OF distinct] by blast
 show ?thesis
  apply (rule exI[of _ xs], rule exI[of _ ys], intro conjI)
  apply (rule before)
  apply (rule after)
  apply (rule related)
  using list_all2_lengthD[OF related] apply simp
  apply (rule checkpoint_rank_forest_return[OF related])
  done
qed

ML \<open>
val thms = @{thms checkpoint_composed_leaf_rules_sound checkpoint_composed_rules_sound checked_checkpoint_composed_success checked_checkpoint_composed_list_return};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms))
 then error "Untrusted composed summary" else ();
\<close>
end
