theory LP_Prolog_Integer_Recurrence_Check
  imports LP_Prolog_Integer_Recurrence_Coordinates ITS_Ext.ITS4_Parser
begin

definition lpp_recurrence_coordinate where
  "lpp_recurrence_coordinate bindings x = (case map_of bindings x of None \<Rightarrow> x | Some y \<Rightarrow> y)"

definition lpp_check_integer_recurrence where
  "lpp_check_integer_recurrence P q modes c xs ops outputs coordinates loc child prf =
    (length modes=length xs \<and> distinct xs \<and> c<length P \<and>
     P!c=(Fun (LPCUser q) (map Var xs),map lpp_recurrence_goal ops @
       [LPCAtom (Fun (LPCUser q) (map lpp_expression_term outputs))]) \<and>
     (case lp_cut_slice P (LPCUser q) (length xs) of [] \<Rightarrow> False | d#remaining \<Rightarrow> d=c) \<and>
     (q,length xs)\<notin>lpp_builtin_signature \<and>
     lpp_recurrence_check xs ops \<and> length outputs=length xs \<and>
     list_all (\<lambda>e. lpp_integer_endpoint e \<and>
       lpp_expression_check (lpp_recurrence_known xs ops) e) outputs \<and>
     length coordinates=length xs \<and> distinct coordinates \<and>
     map snd (transitions_impl child) = [Transition loc loc
       (rename_vars (map_trans_var (lpp_recurrence_coordinate (zip xs coordinates)))
         (lpp_recurrence_relation_formula xs ops outputs))] \<and>
     isOK (check_its4 child False prf))"

theorem lpp_check_integer_recurrence_sound:
  assumes checked: "lpp_check_integer_recurrence P q modes c xs ops outputs coordinates loc child prf"
  shows "\<exists>argv. length argv=length modes \<and> list_all ground argv \<and>
    \<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (\<lambda>t. lp_ieval t LPIVar) argv))]]}"
proof -
  let ?rename = "lpp_recurrence_coordinate (zip xs coordinates)"
  have rules: "transition_rules (lts_of child) = {Transition loc loc
      (rename_vars (map_trans_var ?rename) (lpp_recurrence_relation_formula xs ops outputs))}"
    using checked by (auto simp: lpp_check_integer_recurrence_def set_map[symmetric])
  have lengths: "length xs=length outputs" using checked by (simp add: lpp_check_integer_recurrence_def)
  have child_no: "\<not>LPPIntegerLTS.lts_termination (lts_of child)"
    using check_its4_sound[of child False "prf"] checked
    by (simp add: lpp_check_integer_recurrence_def)
  obtain rho where no: "\<not>SN_on (lpp_recurrence_integer_relation xs ops outputs) {rho}"
    using lpp_recurrence_renamed_lts_nontermination[OF rules lengths child_no] by blast
  obtain cs where first: "lp_cut_slice P (LPCUser q) (length xs)=c#cs"
    using checked by (auto simp: lpp_check_integer_recurrence_def split: list.splits)
  have source_no: "\<not>SN_on (lpp_builtin_source P lpp_integer_source_builtin)
      {[LPCGoals [LPCAtom (LPIFun (LPCUser q) (map (lpp_integer_value o rho) xs))]]}"
    by (rule lpp_recurrence_integer_relation_source_no[OF first _ _ _ _ lengths _ no])
      (use checked in \<open>auto simp: lpp_check_integer_recurrence_def\<close>)
  let ?argv = "map (lpp_integer_term o rho) xs"
  have argv_length: "length ?argv=length modes" using checked
    by (simp add: lpp_check_integer_recurrence_def)
  have argv_ground: "list_all ground ?argv"
    by (simp add: list_all_iff lpp_integer_term_def ground_vars_term_empty)
  have argv_eval: "map (\<lambda>t. lp_ieval t LPIVar) ?argv=map (lpp_integer_value o rho) xs"
    by (simp add: map_map o_def)
  show ?thesis by (rule exI[of _ "?argv"])
    (use argv_length argv_ground source_no in \<open>simp only: argv_eval; blast\<close>)
qed

ML \<open>
val checked = [@{thm lpp_check_integer_recurrence_sound}];
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_its4_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  exists (fn n => not (member (op =) inherited n)) (oracles checked)
  then error "Untrusted arithmetic source NO checker dependency" else ();
\<close>
end
