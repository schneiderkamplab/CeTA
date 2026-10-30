theory LP_Prolog_Context_Link
  imports LP_Prolog_Observed_Calls LP_Cut_Return_Table
begin

definition lpp_path_context_holds where
  "lpp_path_context_holds P facts guards observations eta =
    (list_all (\<lambda>b. lpp_guarded_success P lpp_integer_result (lpp_success_atom_eval b eta)) facts \<and>
     list_all (lpp_success_guard_holds lpp_integer_result eta) guards \<and>
     list_all (lpp_numeric_observation_holds eta) observations)"


text \<open>Literal recognition reconstructs the canonical source symbol. The
candidate decoder is untrusted arithmetic: only the final exact term equality
can establish an integer fact. Evaluation facts refer to actual earlier
successful integer operations, never merely to ground arguments.\<close>
definition lpp_context_literal_candidate :: "(string lp_cut_symbol,'v) term \<Rightarrow> int" where
  "lpp_context_literal_candidate t = (case t of Fun (LPCUser encoded_name) [] \<Rightarrow>
    let payload=drop (length (lpp_integer_name 0)-2) encoded_name;
        negative=take 2 payload=''2d'';
        digits=(if negative then drop 2 payload else payload);
        value=foldl (\<lambda>n i. 10*n + int (length (takeWhile (\<lambda>c. c\<noteq>digits!(2*i+1)) ''0123456789'')))
          0 [0..<length digits div 2]
    in (if negative then -value else value) | _ \<Rightarrow> 0)"

definition lpp_context_integer where
  "lpp_context_integer guards t =
    (t=lpp_integer_term (lpp_context_literal_candidate t) \<or>
     LPPSInteger t\<in>set guards \<or>
     list_ex (\<lambda>g. case g of LPPSEvaluates e u \<Rightarrow> u=t | _ \<Rightarrow> False) guards)"

lemma lpp_context_integer_sound:
  assumes "lpp_context_integer guards t"
    "list_all (lpp_success_guard_holds lpp_integer_result eta) guards"
  shows "lpp_is_integer (lp_ieval t eta)"
proof -
  have literal: "t=lpp_integer_term (lpp_context_literal_candidate t) \<Longrightarrow>
    lpp_is_integer (lp_ieval t eta)"
    by (metis lpp_integer_literal_eval lpp_is_integer_def)
  have tested: "LPPSInteger t\<in>set guards \<Longrightarrow> lpp_is_integer (lp_ieval t eta)"
    using assms(2) by (auto simp: list_all_iff)
  have evaluated: "list_ex (\<lambda>g. case g of LPPSEvaluates e u \<Rightarrow> u=t | _ \<Rightarrow> False) guards
    \<Longrightarrow> lpp_is_integer (lp_ieval t eta)"
  proof -
    assume exists: "list_ex (\<lambda>g. case g of LPPSEvaluates e u \<Rightarrow> u=t | _ \<Rightarrow> False) guards"
    then obtain g where member: "g\<in>set guards" and shape:
      "(case g of LPPSEvaluates e u \<Rightarrow> u=t | _ \<Rightarrow> False)"
      by (auto simp: list_ex_iff)
    have holds: "lpp_success_guard_holds lpp_integer_result eta g"
      using assms(2) member by (auto simp: list_all_iff)
    show ?thesis using holds shape
      by (cases g) (auto simp: lpp_integer_result_def lpp_is_integer_def)
  qed
  show ?thesis using assms(1) literal tested evaluated
    unfolding lpp_context_integer_def by blast
qed

fun lpp_context_guard_check where
  "lpp_context_guard_check guards (LPPSInteger t) = lpp_context_integer guards t"
| "lpp_context_guard_check guards (LPPSOpaque t) = True"
| "lpp_context_guard_check guards g = (g\<in>set guards)"


fun lpp_observation_ground_vars where
  "lpp_observation_ground_vars (LPPOGround t) = vars_term t"
| "lpp_observation_ground_vars (LPPOInteger t) = vars_term t"
| "lpp_observation_ground_vars (LPPOEvaluation e t) = vars_term t"
| "lpp_observation_ground_vars (LPPOComparison c a b) = {}"

definition lpp_observations_ground where
  "lpp_observations_ground observations = (\<Union>observation\<in>set observations. lpp_observation_ground_vars observation)"

declare lpp_observations_ground_def[code del]

lemma lpp_observations_ground_code [code]:
  "lpp_observations_ground [] = {}"
  "lpp_observations_ground (observation#observations) =
    lpp_observation_ground_vars observation \<union> lpp_observations_ground observations"
  by (auto simp: lpp_observations_ground_def)

lemma lpp_integer_finite_ground:
  "lpp_is_integer t \<Longrightarrow> lp_seg_ground t"
  by (auto simp: lpp_is_integer_def lpp_integer_value_def intro: lp_seg_ground.intros)

lemma lpp_integer_ground_vars:
  "lpp_is_integer (lp_ieval t eta) \<Longrightarrow>
    \<forall>x\<in>vars_term t. lp_seg_ground (eta x)"
  using lpp_integer_finite_ground[of "lp_ieval t eta"] by (simp add: lp_seg_ground_eval)

lemma lpp_integer_literal_ground_vars:
  "lp_ieval t eta = lpp_integer_value n \<Longrightarrow>
    \<forall>x\<in>vars_term t. lp_seg_ground (eta x)"
  by (rule lpp_integer_ground_vars) (auto simp: lpp_is_integer_def)

lemma lpp_observation_ground_vars_sound:
  "lpp_numeric_observation_holds eta observation \<Longrightarrow>
    \<forall>x\<in>lpp_observation_ground_vars observation. lp_seg_ground (eta x)"
  by (cases observation)
    (auto simp: lp_seg_ground_eval lpp_integer_result_def
      dest: lpp_integer_ground_vars lpp_integer_literal_ground_vars)

lemma lpp_observations_ground_sound:
  "list_all (lpp_numeric_observation_holds eta) observations \<Longrightarrow>
    \<forall>x\<in>lpp_observations_ground observations. lp_seg_ground (eta x)"
  using lpp_observation_ground_vars_sound by (auto simp: lpp_observations_ground_def list_all_iff)

fun lpp_context_observation_check where
  "lpp_context_observation_check guards observations (LPPOGround t) =
    (vars_term t \<subseteq> lpp_observations_ground observations)"
| "lpp_context_observation_check guards observations (LPPOInteger t) = lpp_context_integer guards t"
| "lpp_context_observation_check guards observations observation = (observation\<in>set observations)"

lemma lpp_context_guard_check_sound:
  "lpp_context_guard_check guards g \<Longrightarrow>
   list_all (lpp_success_guard_holds lpp_integer_result eta) guards \<Longrightarrow>
   lpp_success_guard_holds lpp_integer_result eta g"
  by (cases g) (auto simp: list_all_iff intro: lpp_context_integer_sound)

lemma lpp_context_observation_check_sound:
  "lpp_context_observation_check guards observations observation \<Longrightarrow>
   list_all (lpp_success_guard_holds lpp_integer_result eta) guards \<Longrightarrow>
   list_all (lpp_numeric_observation_holds eta) observations \<Longrightarrow>
   lpp_numeric_observation_holds eta observation"
  by (cases observation) (auto simp: list_all_iff lpp_is_integer_def
      lp_seg_ground_eval dest: lpp_context_integer_sound lpp_observations_ground_sound[unfolded list_all_iff])

definition lpp_check_context_transport where
  "lpp_check_context_transport facts guards observations child_facts child_guards child_observations bindings =
    (let mu=lp_cut_instance_subst bindings in
      list_all (\<lambda>b. lpp_success_atom_subst b mu\<in>set facts) child_facts \<and>
      list_all (\<lambda>g. lpp_context_guard_check guards (lpp_success_guard_subst g mu)) child_guards \<and>
      list_all (\<lambda>observation. lpp_context_observation_check guards observations (lpp_numeric_observation_substitute observation mu)) child_observations)"

lemma lpp_context_guard_transport:
  assumes checked: "(case g of LPPSOpaque _ \<Rightarrow> True | _ \<Rightarrow> lpp_success_guard_subst g mu\<in>set guards)"
    and known: "list_all (lpp_success_guard_holds E eta) guards"
  shows "lpp_success_guard_holds E eta (lpp_success_guard_subst g mu)"
  using checked known by (cases g) (auto simp: list_all_iff)

lemma lpp_context_transport_sound:
  assumes checked: "lpp_check_context_transport facts guards observations child_facts child_guards child_observations bindings"
    and source: "lpp_path_context_holds P facts guards observations eta"
  shows "lpp_path_context_holds P child_facts child_guards child_observations
    (\<lambda>x. lp_ieval (lp_cut_instance_subst bindings x) eta)"
proof -
  have guards: "list_all (lpp_success_guard_holds lpp_integer_result eta) guards"
    and observations: "list_all (lpp_numeric_observation_holds eta) observations"
    using source by (auto simp: lpp_path_context_holds_def)
  show ?thesis using checked source
    lpp_context_guard_check_sound[OF _ guards]
    lpp_context_observation_check_sound[OF _ guards observations]
    by (auto simp: lpp_check_context_transport_def lpp_path_context_holds_def
      Let_def list_all_iff lpp_success_atom_subst_eval[symmetric]
      lpp_success_guard_subst_eval[symmetric] lpp_numeric_observation_substitute_eval[symmetric])
qed

text \<open>The target context uses exactly the substitution already checked
by the shared return link. It cannot be attached to a different environment,
or supply later observations to an earlier source operation.\<close>

lemma lpp_return_context_link_sound:
  assumes checked: "lpc_check_return_table_link fuel Q nds states nd ss G guards eqs link"
    and equations: "lp_equations eqs eta'"
    and old: "map eta' (lpcn_vars nd)=map eta (lpcn_vars nd)"
    and known: "lp_cut_knowledge (set G) guards eta'"
    and transport: "lpp_check_context_transport facts tests observations
      child_facts child_tests child_observations (lpcl_bindings link)"
    and source: "lpp_path_context_holds P facts tests observations eta'"
  shows "\<exists>nu. lpc_return_scope_word (rev (lpcl_swaps link)) (lpc_return_eval eta' ss) =
      lpc_return_eval nu (states!lpcl_target link) \<and>
    lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) nu \<and>
    lpp_path_context_holds P child_facts child_tests child_observations nu \<and>
    ([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target link),map nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
proof -
  let ?nu = "\<lambda>x. lp_ieval (lp_cut_instance_subst (lpcl_bindings link) x) eta'"
  have base: "lpc_check_return_link fuel Q nds nd ss G guards eqs (states!lpcl_target link) link"
    using checked by (simp add: lpc_check_return_table_link_def)
  have same: "lpc_return_eval eta' ss = lpc_return_scope_word (lpcl_swaps link)
      (lpc_return_eval ?nu (states!lpcl_target link))"
    and child_known: "lp_cut_knowledge (set (lpcn_ground (nds!lpcl_target link))) (lpcn_guards (nds!lpcl_target link)) ?nu"
    and edge: "([(lpcn_pred nd,map eta (lpcn_vars nd))],
      [(lpcn_pred (nds!lpcl_target link),map ?nu (lpcn_vars (nds!lpcl_target link)))])\<in>lp_ild Q"
    using lpc_return_link_sound[OF base equations old known] by blast+
  have child: "lpp_path_context_holds P child_facts child_tests child_observations ?nu"
    by (rule lpp_context_transport_sound[OF transport source])
  show ?thesis by (rule exI[of _ ?nu])
    (use same child_known edge child in \<open>simp add: lpc_return_scope_word_inverse\<close>)
qed

ML \<open>
val checked = [@{thm lpp_context_transport_sound}, @{thm lpp_return_context_link_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted observed-context link dependency" else ();
\<close>
end
