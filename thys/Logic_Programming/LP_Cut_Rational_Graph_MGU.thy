theory LP_Cut_Rational_Graph_MGU
  imports LP_Cut_Rational_Closed_Match LP_Rational_Graph_Match
begin

text \<open>The graph is a candidate principal solution, not a finite encoding
used as runtime data. Anchors must reconstruct every graph equation from the
original source equality. This rules out choosing an arbitrary ground solution
for unconstrained variables in the active continuation.\<close>
definition lpc_check_rational_binding ::
  "nat \<Rightarrow> ('f,string) lp_rational_node list \<Rightarrow> ('f,string) term list \<Rightarrow>
    string \<Rightarrow> ('f,string) term \<Rightarrow> nat \<Rightarrow> bool" where
  "lpc_check_rational_binding fuel G anchors x t r =
    (lp_rational_graph_closed G \<and> length anchors=length G \<and> r<length G \<and>
     anchors!r=Var x \<and> lp_rational_match fuel G [(x,r)] t r \<and>
     list_all (\<lambda>i. case G!i of LPRExternal y \<Rightarrow> False
       | LPRBranch f js \<Rightarrow> lp_check_equation_congruence [(Var x,t)]
           (anchors!i) (Fun f (map ((!) anchors) js))) [0..<length G])"

definition lpc_graph_binding :: "('f,string) lp_rational_node list \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> ('f,string) lp_iterm" where
  "lpc_graph_binding G x r y =
    (if x=y then lp_rational_graph_value G LPIVar r else LPIVar y)"

lemma lpc_graph_binding_environment:
  "lpc_graph_binding G x r = lp_rational_match_env G LPIVar [(x,r)]"
  by (rule ext) (simp add: lpc_graph_binding_def lp_rational_match_env_def)

lemma lpc_rational_binding_anchor_model:
  assumes checked: "lpc_check_rational_binding fuel G anchors x t r"
    and solution: "eta x=lp_ieval t eta"
  shows "lp_rational_graph_model G eta (\<lambda>i. lp_ieval (anchors!i) eta)"
proof (unfold lp_rational_graph_model_def, intro allI impI)
  fix i assume index: "i<length G"
  have all: "\<forall>i\<in>set [0..<length G]. case G!i of LPRExternal y \<Rightarrow> False
      | LPRBranch f js \<Rightarrow> lp_check_equation_congruence [(Var x,t)]
          (anchors!i) (Fun f (map ((!) anchors) js))"
    using checked by (simp add: lpc_check_rational_binding_def list_all_iff)
  have at: "case G!i of LPRExternal y \<Rightarrow> False
      | LPRBranch f js \<Rightarrow> lp_check_equation_congruence [(Var x,t)]
          (anchors!i) (Fun f (map ((!) anchors) js))"
    using all[rule_format, of i] index by simp
  obtain f js where branch: "G!i=LPRBranch f js"
    and equation: "lp_check_equation_congruence [(Var x,t)] (anchors!i)
      (Fun f (map ((!) anchors) js))"
    using at by (cases "G!i") auto
  have equal: "lp_ieval (anchors!i) eta=lp_ieval (Fun f (map ((!) anchors) js)) eta"
    by (rule lp_check_equation_congruence_sound[OF equation]) (use solution in auto)
  show "lp_ieval (anchors!i) eta = (case G!i of LPRExternal y \<Rightarrow> eta y
      | LPRBranch f js \<Rightarrow> LPIFun f (map (\<lambda>i. lp_ieval (anchors!i) eta) js))"
    using equal by (simp add: branch map_map)
qed

lemma lpc_rational_binding_anchor_factor:
  assumes checked: "lpc_check_rational_binding fuel G anchors x t r"
    and solution: "eta x=lp_ieval t eta"
  shows "eta x=lp_rational_graph_value G LPIVar r"
proof -
  have closed: "lp_rational_graph_closed G" and index: "r<length G"
    and anchor: "anchors!r=Var x"
    using checked by (auto simp: lpc_check_rational_binding_def)
  have valid: "lp_rational_graph_valid G" using closed
    by (simp add: lp_rational_graph_closed_def)
  have equal: "lp_ieval (anchors!r) eta=lp_rational_graph_value G eta r"
    by (rule lp_rational_graph_model_unique[OF valid
      lpc_rational_binding_anchor_model[OF checked solution] lp_rational_graph_value_model index])
  show ?thesis using equal anchor lp_rational_closed_value_environment[OF closed index] by simp
qed

lemma lpc_checked_rational_binding_unifies:
  assumes checked: "lpc_check_rational_binding fuel G anchors x t r"
  shows "lp_isubst (LPIVar x) (lpc_graph_binding G x r)=
    lp_isubst (lp_ieval t LPIVar) (lpc_graph_binding G x r)"
proof -
  have matched: "lp_rational_match fuel G [(x,r)] t r"
    using checked by (simp add: lpc_check_rational_binding_def)
  have evaluated_value: "lp_ieval t (lpc_graph_binding G x r)=lp_rational_graph_value G LPIVar r"
    using lp_rational_match_sound[OF matched, of LPIVar]
    by (simp only: lpc_graph_binding_environment)
  have right: "lp_isubst (lp_ieval t LPIVar) (lpc_graph_binding G x r)=
    lp_ieval t (lpc_graph_binding G x r)" by (simp add: lp_ieval_subst)
  have left: "lpc_graph_binding G x r x=lp_rational_graph_value G LPIVar r"
    by (simp add: lpc_graph_binding_def)
  show ?thesis using evaluated_value by (simp only: right lp_isubst_Var left)
qed

lemma lpc_checked_rational_binding_factor:
  fixes eta :: "string \<Rightarrow> ('f,string) lp_iterm"
  assumes checked: "lpc_check_rational_binding fuel G anchors x t r"
    and solution: "eta x=lp_ieval t eta"
  shows "lp_isubst (lpc_graph_binding G x r y) eta=eta y"
proof -
  have closed: "lp_rational_graph_closed G" and index: "r<length G"
    using checked by (auto simp: lpc_check_rational_binding_def)
  show ?thesis
    using lpc_rational_binding_anchor_factor[OF checked solution]
      lp_rational_closed_value_subst[OF closed index, of LPIVar eta]
    by (auto simp: lpc_graph_binding_def)
qed

theorem lpc_checked_rational_binding_mgu:
  fixes G :: "('f,string) lp_rational_node list"
  assumes checked: "lpc_check_rational_binding fuel G anchors x t r"
  shows "lpc_mgu_unify (LPIVar x) (lp_ieval t LPIVar) gs (lpc_graph_binding G x r)"
  unfolding lpc_mgu_unify_def
proof (intro conjI allI impI)
  show "lp_isubst (LPIVar x) (lpc_graph_binding G x r)=
    lp_isubst (lp_ieval t LPIVar) (lpc_graph_binding G x r)"
    by (rule lpc_checked_rational_binding_unifies[OF checked])
next
  fix tau :: "string \<Rightarrow> ('f,string) lp_iterm"
  assume solution: "lp_isubst (LPIVar x) tau=lp_isubst (lp_ieval t LPIVar) tau"
  have eq: "tau x=lp_ieval t tau" using solution by (simp add: lp_ieval_subst)
  have composed: "(\<lambda>y. lp_isubst (lpc_graph_binding G x r y) tau)=tau"
    by (rule ext) (rule lpc_checked_rational_binding_factor[OF checked eq])
  show "\<exists>delta.
    lp_isubst (lp_isubst (LPIVar x) (lpc_graph_binding G x r)) delta=lp_isubst (LPIVar x) tau \<and>
    map (lp_cut_map (\<lambda>u. lp_isubst (lp_isubst u (lpc_graph_binding G x r)) delta)) gs =
    map (lp_cut_map (\<lambda>u. lp_isubst u tau)) gs"
    by (rule exI[of _ tau]) (simp add: lpc_isubst_comp composed lpc_checked_rational_binding_factor[OF checked eq])
qed

ML \<open>
val checked = [@{thm lpc_checked_rational_binding_mgu}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted rational graph MGU dependency" else ();
\<close>
end
