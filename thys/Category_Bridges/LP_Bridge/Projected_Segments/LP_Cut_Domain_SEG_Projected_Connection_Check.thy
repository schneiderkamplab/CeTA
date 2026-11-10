theory LP_Cut_Domain_SEG_Projected_Connection_Check
 imports LP_Cut_Domain_SEG_Projected_Child
begin
hide_const (open) CPF_Proof_Parser.rstep CPF_Proof_Parser.afs

context cut_runtime_domain
begin

theorem precise_seg_projected_connection_checked_lower:
  fixes filtering :: "'g afs" and m :: "('g,string) term" and initial
  assumes checked: "lpc_seg_check_projected_connection fuel P roots Fs filtering is_cont c d R nd F ss l outp receipt"
    and program: "lp_cut_source_program P"
    and known: "knowledge (set (lpcn_ground nd)) (lpcn_guards nd) eta"
    and free: "lpc_free_knowledge (set F) eta"
    and origin: "lp_iproject filtering initial m"
    and observed: "lp_iproject filtering (lpc_seg_runtime_value is_cont c d l eta) m"
    and ambient: "lpc_seg_projection_context filtering A"
    and lower: "\<And>us v out. (A initial,v)\<in>(lpc_seg_projected_rel filtering R)\<^sup>+ \<Longrightarrow>
      precise_seg_projected_root_rep filtering roots Fs is_cont c d us v out \<Longrightarrow>
      precise_return_contract P us (lpc_seg_projected_rel filtering R) v out"
  shows "precise_return_contract P (lpc_return_eval eta ss) (lpc_seg_projected_rel filtering R)
    (A initial) (\<lambda>rho. A (lpc_seg_runtime_value is_cont c d outp rho))"
proof -
  let ?i="lpcse_target receipt"
  let ?root="roots!?i"
  let ?nd="lpcsr_node ?root"
  let ?vs="lpcn_vars nd"
  let ?cvs="lpcn_vars ?nd"
  let ?mu="lp_cut_instance_subst (lpcse_bindings receipt)"
  let ?eta="\<lambda>x. lp_ieval (?mu x) eta"
  let ?inp="lpcsr_input ?root\<cdot>?mu"
  let ?out="lpc_seg_named_template ?cvs (lpcsr_output ?root)\<cdot>?mu"
  let ?final="lpc_seg_compose_observation (snd (hd ss)) outp"
  let ?u="lpcse_continuation receipt"
  let ?caps="lpcse_captured receipt"
  let ?ctxtD="\<lambda>x. LPIFun (c ?u) (x#map (\<lambda>t. map_lp_iterm d id (lp_ieval t eta)) ?caps)"
  have index: "?i<length roots" using checked by (simp add: lpc_seg_check_projected_connection_def)
  have single: "length ss=1"
  proof (cases ss)
    case Nil then show ?thesis using checked by (simp add: lpc_seg_check_projected_connection_def)
  next
    case (Cons p ps)
    obtain e observed where p: "p=(e,observed)" by (cases p) simp
    show ?thesis using checked Cons p
      by (cases ps; cases e) (simp_all add: lpc_seg_check_projected_connection_def)
  qed
  obtain e observed where one: "ss=[(e,observed)]" using single by (cases ss) auto
  obtain pre where e: "e=LPCGoals pre"
    using checked by (cases e) (auto simp: lpc_seg_check_projected_connection_def one)
  have ss: "ss=[(LPCGoals pre,observed)]" by (simp only: one e)
  have child_single: "length (lpcn_state ?nd)=1"
  proof (cases "lpcn_state ?nd")
    case Nil then show ?thesis using checked by (simp add: lpc_seg_check_projected_connection_def ss Let_def)
  next
    case (Cons x xs)
    show ?thesis using checked Cons by (cases xs) (simp_all add: lpc_seg_check_projected_connection_def ss Let_def)
  qed
  obtain child where child_state: "lpcn_state ?nd=[child]" using child_single by (cases "lpcn_state ?nd") auto
  have inst: "lpc_seg_check_instance_boundary (LPCGoals pre) (lpcn_ground nd) (lpcn_guards nd) ?vs observed
      child (lpcn_ground ?nd) (lpcn_guards ?nd) ?cvs (lpcse_bindings receipt) (lpcse_swaps receipt)"
    and cont: "is_cont ?u"
    and keep: "lpc_seg_projected_continuation_filter filtering (c ?u) (Suc (length ?caps))"
    and enter: "lpc_seg_check_projected_pair filtering 1 2 is_cont c d R l (Fun ?u (?inp#?caps))"
    and leave: "lpc_seg_check_projected_pair filtering 2 1 is_cont c d R (Fun ?u (?out#?caps)) (lpc_seg_compose_observation observed outp)"
    using checked by (auto simp: lpc_seg_check_projected_connection_def ss child_state Let_def)
  have pr: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d l eta)"
    using observed by (auto simp: lpc_seg_has_projection_def)
  obtain indices and ms :: "('g,string) term list" where af: "afs filtering (c ?u,Suc (length ?caps))=AFList (0#map Suc indices)"
    and cap_pr: "list_all2 (\<lambda>i m. i<length ?caps \<and> lp_iproject filtering (map_lp_iterm d id (lp_ieval (?caps!i) eta)) m) indices ms"
    and child_pr: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d ?inp eta)"
    and ctxt: "lpc_seg_projection_context filtering (\<lambda>x. A (?ctxtD x))"
    and call: "(A (lpc_seg_runtime_value is_cont c d l eta),A (?ctxtD (lpc_seg_runtime_value is_cont c d ?inp eta)))\<in>lpc_seg_projected_rel filtering R"
    by (rule lpc_seg_projected_call[OF enter cont keep pr ambient]) blast
  have shifted: "(A initial,A (?ctxtD (lpc_seg_runtime_value is_cont c d ?inp eta)))\<in>lpc_seg_projected_rel filtering R"
    by (rule lpc_seg_projected_replace_left[OF origin observed call ambient])
  have child_known: "knowledge (set (lpcn_ground ?nd)) (lpcn_guards ?nd) ?eta"
    by (rule precise_seg_instance_boundary_knowledge[OF inst known])
  have free_check: "lpc_check_link_free fuel [] F (Fs!?i) (lpcse_bindings receipt)"
    using checked by (simp add: lpc_seg_check_projected_connection_def)
  have child_free: "lpc_free_knowledge (set (Fs!?i)) ?eta"
    by (rule lpc_checked_link_free_sound[OF free_check _ free]) (simp add: lp_equations_def)
  have child_observed: "lpc_seg_has_projection filtering (lpc_seg_runtime_value is_cont c d (lpcsr_input ?root) ?eta)"
    using child_pr by (simp only: lpc_seg_runtime_value_def lp_ieval_finite_subst)
  have strict: "(A initial,A (?ctxtD (lpc_seg_runtime_value is_cont c d (lpcsr_input ?root) ?eta)))\<in>(lpc_seg_projected_rel filtering R)\<^sup>+"
    using r_into_trancl[OF shifted] by (simp only: lpc_seg_runtime_value_def lp_ieval_finite_subst)
  have contract: "precise_return_contract P (lpc_return_eval ?eta [(child,map Var ?cvs)]) (lpc_seg_projected_rel filtering R)
    (A (?ctxtD (lpc_seg_runtime_value is_cont c d ?inp eta)))
    (\<lambda>rho. A (?ctxtD (lpc_seg_runtime_value is_cont c d (lpcsr_output ?root) rho)))"
    using lower[OF strict precise_seg_projected_root_repI[OF index child_known child_free child_observed ctxt]]
    by (simp add: lpc_seg_root_state_def child_state lpc_seg_runtime_value_def lp_ieval_finite_subst)
  have target: "lpc_seg_has_projection filtering (A (?ctxtD (lpc_seg_runtime_value is_cont c d ?inp eta)))"
    using shifted by (auto simp: lpc_seg_projected_rel_def lpc_seg_has_projection_def)
  show ?thesis unfolding ss
    by (rule precise_seg_projected_connection_contract[OF inst program known leave cont _ _ af cap_pr _ _
      r_into_rtrancl[OF shifted] target ambient contract])
      (use checked in \<open>auto simp: lpc_seg_check_projected_connection_def ss child_state Let_def\<close>)
qed


end
end
