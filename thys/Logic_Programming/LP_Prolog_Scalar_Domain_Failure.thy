theory LP_Prolog_Scalar_Domain_Failure
 imports LP_Prolog_Scalar_Domain_Interface LP_Prolog_Scalar_Recurrence_Failure_Check
begin

fun lpp_domain_fixed_observation where
 "lpp_domain_fixed_observation (Some (LPPRecurrentFixed v))=Some v"
| "lpp_domain_fixed_observation _=None"

lemma lpp_domain_observations_fixed:
 assumes observed: "lpp_domain_observations operation observations actuals"
 shows "lpp_scalar_observations operation (map lpp_domain_fixed_observation observations) actuals"
proof -
 have lengths: "length actuals=length observations" using observed by (simp add: lpp_domain_observations_def)
 have each: "lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value w)"
   if bound: "i<length observations" and entry: "lpp_domain_fixed_observation (observations!i)=Some w" for i w
 proof -
  have fixed: "observations!i=Some (LPPRecurrentFixed w)"
    using entry by (cases "observations!i" rule: lpp_domain_fixed_observation.cases) auto
  have row: "case observations!i of None \<Rightarrow> True | Some d \<Rightarrow>
     (\<exists>v. lpp_recurrent_scalar_member d v \<and>
       lpp_stable_scalar_evaluation operation (actuals!i) (lpp_machine_value v))"
    using observed bound by (auto simp: lpp_domain_observations_def list_all_iff)
  show ?thesis using row fixed by auto
 qed
 show ?thesis using lengths each
   by (auto simp: lpp_scalar_observations_def list_all_iff split: option.splits)
qed
end
