theory LP_Cut_Domain_SEG_Free_Connection_Check
 imports LP_Cut_Domain_SEG_Free_Root_Representation
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_free_connection_checked_lower:
  assumes checked: "lpc_seg_free_check_connection fuel P roots Fs is_cont c d C R nd F ss l outp receipt"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and finite: "lp_seg_ground (lp_ieval l eta)"
    and lower: "\<And>vs v out. (A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,v)\<in>(qrstep False Q R)\<^sup>+ \<Longrightarrow>
      precise_seg_free_root_rep roots Fs is_cont c d vs v out \<Longrightarrow>
      precise_return_contract P vs (qrstep False Q R) v out"
    and range: "range d \<subseteq> C"
    and roots: "\<And>q. q\<in>Q \<Longrightarrow> \<exists>g us. q=Fun g us \<and> g\<notin>C"
  shows "precise_return_contract P (lpc_return_eval eta ss) (qrstep False Q R)
    (A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>)
    (\<lambda>rho. A\<langle>lpc_seg_return_value is_cont c d outp rho\<rangle>)"
proof -
  let ?i = "lpcse_target receipt"
  let ?root = "roots!?i"
  let ?nd = "lpcsr_node ?root"
  let ?vs = "lpcn_vars nd"
  let ?cvs = "lpcn_vars ?nd"
  let ?mu = "lp_cut_instance_subst (lpcse_bindings receipt)"
  let ?eta = "\<lambda>x. lp_ieval (?mu x) eta"
  let ?inp = "lpcsr_input ?root\<cdot>?mu"
  let ?out = "lpc_seg_named_template ?cvs (lpcsr_output ?root)\<cdot>?mu"
  let ?u = "lpcse_continuation receipt"
  let ?caps = "lpcse_captured receipt"
  let ?ctxtD = "More (c ?u) [] \<box>
    (map (\<lambda>t. lpc_seg_finite_value (map_lp_iterm d id (lp_ieval t eta))) ?caps)"
  have index: "?i<length roots" using checked by (simp add: lpc_seg_free_check_connection_def lpc_seg_check_connection_def)
  have single: "length ss=1"
  proof (cases ss)
    case Nil then show ?thesis using checked by (simp add: lpc_seg_free_check_connection_def lpc_seg_check_connection_def)
  next
    case (Cons p ps)
    obtain e observed where p: "p=(e,observed)" by (cases p) simp
    show ?thesis using checked Cons p
      by (cases ps; cases e) (simp_all add: lpc_seg_free_check_connection_def lpc_seg_check_connection_def)
  qed
  obtain e observed where one: "ss=[(e,observed)]"
    using single by (cases ss) auto
  obtain pre where e: "e=LPCGoals pre"
    using checked by (cases e) (auto simp: lpc_seg_free_check_connection_def lpc_seg_check_connection_def one)
  have ss: "ss=[(LPCGoals pre,observed)]" by (simp only: one e)
  have child_single: "length (lpcn_state ?nd)=1"
  proof (cases "lpcn_state ?nd")
    case Nil then show ?thesis using checked by (simp add: lpc_seg_free_check_connection_def lpc_seg_check_connection_def ss Let_def)
  next
    case (Cons x xs)
    show ?thesis using checked Cons by (cases xs) (simp_all add: lpc_seg_free_check_connection_def lpc_seg_check_connection_def ss Let_def)
  qed
  obtain child where child_state: "lpcn_state ?nd=[child]"
    using child_single by (cases "lpcn_state ?nd") auto
  have inst: "lpc_seg_check_instance_boundary (LPCGoals pre) (lpcn_ground nd) (lpcn_guards nd) ?vs observed
    child (lpcn_ground ?nd) (lpcn_guards ?nd) ?cvs (lpcse_bindings receipt) (lpcse_swaps receipt)"
    and cont: "is_cont ?u"
    and enter: "lpc_seg_check_encoded_pair 1 2 is_cont c d C R l (Fun ?u (?inp#?caps))"
    and leave: "lpc_seg_check_encoded_pair 2 1 is_cont c d C R (Fun ?u (?out#?caps)) (lpc_seg_compose_observation observed outp)"
    using checked by (auto simp: lpc_seg_free_check_connection_def lpc_seg_check_connection_def ss child_state Let_def)
  have child_known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule precise_seg_instance_boundary_knowledge[OF inst known])
  have call: "lp_seg_ground (lp_ieval ?inp eta) \<and>
    list_all (\<lambda>t. lp_seg_ground (lp_ieval t eta)) ?caps \<and>
    (lpc_seg_return_value is_cont c d l eta,?ctxtD\<langle>lpc_seg_return_value is_cont c d ?inp eta\<rangle>)\<in>qrstep False Q R"
    using lpc_seg_checked_call[where Q=Q, OF enter cont finite range roots]
    by (simp only: lpc_seg_return_value_def)
  have child_finite: "lp_seg_ground (lp_ieval (lpcsr_input ?root) ?eta)"
    using call by (simp add: lp_ieval_finite_subst)
  have strict: "(A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,
    (A\<circ>\<^sub>c ?ctxtD)\<langle>lpc_seg_return_value is_cont c d (lpcsr_input ?root) ?eta\<rangle>)\<in>(qrstep False Q R)\<^sup>+"
  proof -
    have step: "(A\<langle>lpc_seg_return_value is_cont c d l eta\<rangle>,
      A\<langle>?ctxtD\<langle>lpc_seg_return_value is_cont c d ?inp eta\<rangle>\<rangle>)\<in>qrstep False Q R"
      by (rule qrstep.ctxt) (use call in blast)
    show ?thesis using r_into_trancl[OF step]
      by (simp add: lpc_seg_return_value_def lp_ieval_finite_subst)
  qed
  have free_check: "lpc_check_link_free fuel [] F (Fs!?i) (lpcse_bindings receipt)"
    using checked by (simp add: lpc_seg_free_check_connection_def)
  have child_free: "lpc_free_knowledge (set (Fs!?i)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  have child_contract: "precise_return_contract P (lpc_return_eval ?eta [(child,map Var ?cvs)]) (qrstep False Q R)
    (A\<langle>?ctxtD\<langle>lpc_seg_return_value is_cont c d ?inp eta\<rangle>\<rangle>)
    (\<lambda>rho. A\<langle>?ctxtD\<langle>lpc_seg_return_value is_cont c d (lpcsr_output ?root) rho\<rangle>\<rangle>)"
    using precise_seg_free_root_lower[OF lower index child_known child_free child_finite strict]
    by (simp add: lpc_seg_root_state_def child_state lpc_seg_return_value_def lp_ieval_finite_subst)
  show ?thesis unfolding ss
    by (rule precise_seg_connection_contract[OF inst program known enter leave cont finite _ _ _ _ _ refl child_contract range roots])
      (use checked in \<open>auto simp: lpc_seg_free_check_connection_def lpc_seg_check_connection_def ss child_state Let_def\<close>)
qed


end
end
