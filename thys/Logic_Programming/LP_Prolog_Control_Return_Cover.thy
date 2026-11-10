theory LP_Prolog_Control_Return_Cover
 imports LP_Prolog_Control_Return_Program
begin

definition lpp_control_return_program_check where
  "lpp_control_return_program_check fuel P F SP =
    (lpp_control_equality_clause\<in>set SP \<and>
     list_all (\<lambda>cl. list_all lpc_model_safe_goal (snd cl) \<and>
       (case fst cl of Fun (LPCUser f) ts \<Rightarrow>
         f\<noteq>''2:;'' \<and> f\<noteq>''3:subtract'' \<and>
         (f\<in>F \<longrightarrow> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and>
           (case lpp_control_paths fuel (snd cl) of None \<Rightarrow> False | Some paths \<Rightarrow>
             list_all (\<lambda>path.
               list_all (lpp_control_flat_goal F) path \<and>
               ((f,ts),lpp_inline_return_calls (lpp_control_completed_path path),
                 lpp_inline_return_guards (lpp_control_completed_path path))\<in>set SP) paths))
        | _ \<Rightarrow> False)) P)"

lemma lpp_control_return_clause_model:
  assumes ordinary: "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
      "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
    and equation: "lpp_control_equality_clause\<in>set SP"
    and paths: "lpp_control_paths fuel gs=Some paths"
    and covered: "\<And>path. path\<in>set paths \<Longrightarrow>
      list_all (lpp_control_flat_goal F) path \<and>
      ((f,ts),lpp_inline_return_calls (lpp_control_completed_path path),
        lpp_inline_return_guards (lpp_control_completed_path path))\<in>set SP"
    and model: "list_all (lpc_model_goal
      (lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E))))
        (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) gs)"
  shows "lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E))
    (LPIFun (LPCUser f) (map (\<lambda>t. lp_ieval t eta) ts))"
proof -
  let ?M = "lpp_open_return_model F (lpp_inline_return_model SP E)"
  have eq: "?M (LPIFun (LPCUser lpp_control_equality) [a,a])" for a
    using lpp_control_equality_model[where a=a and b=a and E=E, OF equation refl]
    by (simp only: lpp_open_return_model.simps; auto)
  have body: "list_all (lpc_model_goal (lpp_control_return_model ?M))
    (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) gs)"
    using model by (auto simp: list_all_iff lpp_control_model_bind_equiv)
  obtain path where member: "path\<in>set paths" and modeled:
    "list_all (lpc_model_goal (lpp_control_return_model ?M))
      (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) path)"
    using lpp_control_paths_complete[OF eq paths body] by blast
  let ?path = "lpp_control_completed_path path"
  have flat: "list_all (lpp_control_flat_goal F) ?path"
    using covered[OF member] by (auto simp: lpp_control_completed_path_def list_all_iff)
  have control: "list_all (lpc_return_control_goal F) ?path"
    using flat lpp_control_flat_control by (auto simp: list_all_iff)
  have projected: "list_all (lpc_model_goal (lpp_inline_return_model SP E))
    (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) ?path)"
    by (rule lpp_control_flat_body[OF flat lpp_control_completed_model[OF modeled]])
  have clause: "((f,ts),lpp_inline_return_calls ?path,lpp_inline_return_guards ?path)\<in>set SP"
    using covered[OF member] by blast
  have success: "lpp_guarded_success SP E (lpp_success_atom_eval (f,ts) eta)"
    by (rule lpp_guarded_success.clause[OF clause])
      (use lpp_inline_return_body[OF control projected] in auto)
  have base: "?M (LPIFun (LPCUser f) (map (\<lambda>t. lp_ieval t eta) ts))"
    using success ordinary by (simp add: lpp_success_atom_eval_def)
  show ?thesis by (rule lpp_control_return_model.ordinary) (use ordinary base in auto)
qed


theorem lpp_control_return_program_sound:
  assumes checked: "lpp_control_return_program_check fuel P F SP"
  shows "lpc_model_program P
    (lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E)))"
proof (unfold lpc_model_program_def, intro allI impI)
  fix c assume index: "c<length P"
  have local: "list_all lpc_model_safe_goal (snd (P!c)) \<and>
    (case fst (P!c) of Fun (LPCUser f) ts \<Rightarrow>
      f\<noteq>''2:;'' \<and> f\<noteq>''3:subtract'' \<and>
      (f\<in>F \<longrightarrow> f\<noteq>''2:is'' \<and> f\<noteq>''1:integer'' \<and>
       (case lpp_control_paths fuel (snd (P!c)) of None \<Rightarrow> False | Some paths \<Rightarrow>
         list_all (\<lambda>path. list_all (lpp_control_flat_goal F) path \<and>
           ((f,ts),lpp_inline_return_calls (lpp_control_completed_path path),
             lpp_inline_return_guards (lpp_control_completed_path path))\<in>set SP) paths))
     | _ \<Rightarrow> False)"
    using checked index by (auto simp: lpp_control_return_program_check_def list_all_length)
  obtain f ts where head: "fst (P!c)=Fun (LPCUser f) ts"
    using local by (cases "fst (P!c)") (auto split: lp_cut_symbol.splits)
  have ordinary: "f\<noteq>''2:;''" "f\<noteq>''3:subtract''"
    using local by (simp_all add: head)
  have closed: "lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E))
      (lp_ieval (fst (P!c)) eta)"
    if model: "list_all (lpc_model_goal
      (lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E))))
       (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) (snd (P!c)))" for eta m
  proof (cases "f\<in>F")
    case False
    show ?thesis unfolding head lp_ieval.simps
      by (rule lpp_control_return_model.ordinary[OF ordinary]) (simp add: False)
  next
    case True
    obtain paths where paths: "lpp_control_paths fuel (snd (P!c))=Some paths"
      and arithmetic: "f\<noteq>''2:is''" "f\<noteq>''1:integer''"
      and cover: "\<And>path. path\<in>set paths \<Longrightarrow>
        list_all (lpp_control_flat_goal F) path \<and>
        ((f,ts),lpp_inline_return_calls (lpp_control_completed_path path),
          lpp_inline_return_guards (lpp_control_completed_path path))\<in>set SP"
      using local True by (auto simp: head list_all_iff split: option.splits)
    have equation: "lpp_control_equality_clause\<in>set SP"
      using checked by (simp add: lpp_control_return_program_check_def)
    show ?thesis unfolding head lp_ieval.simps
      by (rule lpp_control_return_clause_model[OF ordinary arithmetic equation paths cover model])
  qed
  show "list_all lpc_model_safe_goal (snd (P!c)) \<and>
    (\<forall>eta m. list_all (lpc_model_goal
      (lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E))))
        (map (lp_cut_bind m (\<lambda>t. lp_ieval t eta)) (snd (P!c))) \<longrightarrow>
      lpp_control_return_model (lpp_open_return_model F (lpp_inline_return_model SP E))
        (lp_ieval (fst (P!c)) eta))"
    using local closed by blast
qed

ML \<open>
val checked = [@{thm lpp_control_return_program_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted control return cover" else ();
\<close>
end
