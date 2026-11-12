theory LP_Prolog_List_Observation
 imports LP_Prolog_Finite_Length
begin

text \<open>A finite observation follows only the spine. Heads may be rational.
Failure observations end at a rigid non-list constructor, so they survive
arbitrary substitutions. Open and cyclic spines are not classified by this
checker; running out of fuel supplies no evidence.\<close>

inductive lpp_list_observation where
 nil: "lpp_list_observation (LPIFun (LPCUser ''0:prolog_data_5b5d'') []) True"
| cons: "lpp_list_observation t b \<Longrightarrow>
 lpp_list_observation (LPIFun (LPCUser ''2:prolog_data_2e'') [h,t]) b"
| other: "(f \<noteq> LPCUser ''0:prolog_data_5b5d'' \<or> length ts \<noteq> 0) \<Longrightarrow>
 (f \<noteq> LPCUser ''2:prolog_data_2e'' \<or> length ts \<noteq> 2) \<Longrightarrow>
 lpp_list_observation (LPIFun f ts) False"

lemma lpp_list_observation_subst:
 "lpp_list_observation t b \<Longrightarrow> lpp_list_observation (lp_isubst t sigma) b"
 by (induction rule: lpp_list_observation.induct)
    (auto intro: lpp_list_observation.intros)

lemma lpp_list_observation_success:
 "lpp_list_observation t True \<Longrightarrow> \<exists>n. lpp_list_length t n"
 by (induction t "True" rule: lpp_list_observation.induct)
    (auto intro: lpp_list_length.intros)

lemma lpp_list_observation_failure:
 "lpp_list_observation t False \<Longrightarrow> \<not> lpp_list_length t n"
proof (induction t "False" arbitrary: n rule: lpp_list_observation.induct)
 case nil then show ?case by simp
next
 case (cons t h)
 then show ?case by (auto elim: lpp_list_length.cases)
next
 case (other f ts)
 then show ?case by (auto elim: lpp_list_length.cases)
qed

fun lpp_check_list_observation where
 "lpp_check_list_observation 0 t = None"
| "lpp_check_list_observation (Suc fuel) (Var x) = None"
| "lpp_check_list_observation (Suc fuel) (Fun f ts) =
 (if f=LPCUser ''0:prolog_data_5b5d'' \<and> ts=[] then Some True
  else if f=LPCUser ''2:prolog_data_2e'' \<and> length ts=2
    then lpp_check_list_observation fuel (ts!1)
  else Some False)"

lemma lpp_list_observation_two:
 "length ts=2 \<Longrightarrow> lpp_list_observation (lp_ieval (ts!1) eta) b \<Longrightarrow>
 lpp_list_observation (LPIFun (LPCUser ''2:prolog_data_2e'') (map (\<lambda>t. lp_ieval t eta) ts)) b"
 by (cases ts; cases "tl ts"; cases "tl (tl ts)")
    (auto intro: lpp_list_observation.cons)

lemma lpp_check_list_observation_sound:
 "lpp_check_list_observation fuel t = Some b \<Longrightarrow>
 lpp_list_observation (lp_ieval t eta) b"
proof (induction fuel arbitrary: t b)
 case 0 then show ?case by simp
next
 case (Suc fuel)
 then show ?case
  by (cases t) (auto intro: lpp_list_observation.intros lpp_list_observation_two split: if_splits)
qed

definition lpp_is_list_outcome where
 "lpp_is_list_outcome t outcome =
  (outcome = (if (\<exists>n. lpp_list_length t n)
    then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure))"

lemma lpp_list_observation_outcome:
 "lpp_list_observation t b \<Longrightarrow>
 lpp_is_list_outcome t (if b then LPPBuiltinSuccess LPIVar else LPPBuiltinFailure)"
 by (cases b) (auto simp: lpp_is_list_outcome_def
   dest: lpp_list_observation_success lpp_list_observation_failure)

end
