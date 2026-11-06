theory LP_Prolog_Open_Return_Program
 imports LP_Prolog_Open_Return_Model
begin

lemma lpp_open_return_program:
  assumes scoped: "lpc_scoped_model_program P F M"
    and safe: "\<And>c. c<length P \<Longrightarrow> list_all lpc_model_safe_goal (snd (P!c))"
    and heads: "\<And>c. c<length P \<Longrightarrow> \<exists>f ts. fst (P!c)=Fun (LPCUser f) ts"
  shows "lpc_model_program P (lpp_open_return_model F M)"
proof (unfold lpc_model_program_def, rule allI, rule impI, rule conjI)
  fix c assume index: "c<length P"
  show "list_all lpc_model_safe_goal (snd (P!c))" by (rule safe[OF index])
  show "\<forall>rho m. list_all (lpc_model_goal (lpp_open_return_model F M))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c))) \<longrightarrow>
      lpp_open_return_model F M (lp_ieval (fst (P!c)) rho)"
  proof (intro allI impI)
    fix rho m
    assume body: "list_all (lpc_model_goal (lpp_open_return_model F M))
      (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)))"
    obtain f ts where head: "fst (P!c)=Fun (LPCUser f) ts" using heads[OF index] by blast
    show "lpp_open_return_model F M (lp_ieval (fst (P!c)) rho)"
    proof (cases "f\<in>F")
      case False then show ?thesis by (simp add: head)
    next
      case True
      have control: "list_all (lpc_return_control_goal F) (snd (P!c))"
        and model: "lpc_model_program [P!c] M"
        using scoped index True head by (auto simp: lpc_scoped_model_program_def)
      have original: "list_all (lpc_model_goal M)
        (map (lp_cut_bind m (\<lambda>t. lp_ieval t rho)) (snd (P!c)))"
        by (rule lpp_open_return_body[OF control body])
      have result: "M (lp_ieval (fst (P!c)) rho)"
        using model original by (auto simp: lpc_model_program_def)
      show ?thesis using result True by (simp add: head)
    qed
  qed
qed

ML \<open>
val checked = [@{thm lpp_open_return_program}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted open return program" else ();
\<close>
end
