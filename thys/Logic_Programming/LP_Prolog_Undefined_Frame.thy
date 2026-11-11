theory LP_Prolog_Undefined_Frame
  imports LP_Prolog_Stopped_Answers
begin

fun lpp_check_undefined_frame where
  "lpp_check_undefined_frame P B ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved) =
    ((f,length ts)\<notin>B \<and> \<not>lpp_defined P (f,length ts))"
| "lpp_check_undefined_frame P B ss = False"

lemma lpp_check_undefined_frame_sound:
  assumes checked: "lpp_check_undefined_frame P B ss"
  shows "lpp_undefined_answer_stop P B (lpc_return_eval eta ss)"
  using checked
  by (cases rule: lpp_check_undefined_frame.cases[of "(P,B,ss)"])
    (auto simp: lpp_undefined_answer_stop_def lpc_return_eval_def
      lpp_undefined_def lpp_builtin_active_def)

corollary lpp_undefined_frame_contract:
  assumes checked: "lpp_check_undefined_frame P B ss"
  shows "lp_answer_contract
    (lp_answer_stop (lpp_domain_answers P B U D) (lpp_undefined_answer_stop P B))
    (lpc_return_eval eta ss) R t ret"
  by (rule lp_answer_stop_error_contract, rule lpp_check_undefined_frame_sound[OF checked])

lemma lpp_undefined_frame_missing:
  "lpp_check_undefined_frame [] {} [(LPCGoals [LPCAtom (Fun (LPCUser ''absent'') [])],[])]"
  by (simp add: lpp_defined_def)

lemma lpp_undefined_frame_defined_rejected:
  "\<not>lpp_check_undefined_frame [(Fun (LPCUser ''p'') [Var ''x''],[])] {}
    [(LPCGoals [LPCAtom (Fun (LPCUser ''p'') [Var ''a''])],[])]"
  by (simp add: lpp_defined_def)

lemma lpp_undefined_frame_arity_distinct:
  "lpp_check_undefined_frame [(Fun (LPCUser ''p'') [Var ''x''],[])] {}
    [(LPCGoals [LPCAtom (Fun (LPCUser ''p'') [])],[])]"
  by (simp add: lpp_defined_def)

lemma lpp_undefined_frame_builtin_rejected:
  "\<not>lpp_check_undefined_frame [] {(''builtin'',0)}
    [(LPCGoals [LPCAtom (Fun (LPCUser ''builtin'') [])],[])]"
  by simp

lemma lpp_undefined_frame_saved_alternatives:
  "lpp_check_undefined_frame P B [(LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)] =
   lpp_check_undefined_frame P B ((LPCGoals (LPCAtom (Fun (LPCUser f) ts)#gs),active)#saved)"
  by simp

ML \<open>
val audited = [@{thm lpp_check_undefined_frame_sound}, @{thm lpp_undefined_frame_contract}];
val names = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = names [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof audited orelse
  exists (fn n => not (member (op =) inherited n)) (names audited)
  then error "Untrusted undefined-frame contract dependency" else ();
\<close>
end
