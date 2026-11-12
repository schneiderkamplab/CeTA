theory LP_Prolog_List_Observation_Code
 imports LP_Prolog_List_Observation
begin

text \<open>The unified export represents natural numbers abstractly. This
proved equation avoids constructor patterns on fuel without changing the
observation or its soundness statement.\<close>

declare lpp_check_list_observation.simps [code del]

lemma lpp_check_list_observation_code [code]:
 "lpp_check_list_observation fuel t =
 (if fuel=0 then None else case t of Var x \<Rightarrow> None
  | Fun f ts \<Rightarrow>
    (if f=LPCUser ''0:prolog_data_5b5d'' \<and> ts=[] then Some True
     else if f=LPCUser ''2:prolog_data_2e'' \<and> length ts=2
       then lpp_check_list_observation (fuel-1) (ts!1)
     else Some False))"
 by (cases fuel; cases t) simp_all

ML \<open>
val checked = [@{thm lpp_check_list_observation_code}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted list observation code equation" else ();
\<close>
end
