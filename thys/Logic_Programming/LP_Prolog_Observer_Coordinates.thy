theory LP_Prolog_Observer_Coordinates
 imports LP_Prolog_Answer_Coordinates LP_Prolog_Observer_Rebase
begin

definition lpc_check_coordinate_transport where
 "lpc_check_coordinate_transport old_coordinates new_coordinates routing =
  list_all (\<lambda>(a,b). (routing a,routing b)\<in>set old_coordinates \<or> routing a=routing b) new_coordinates"

lemma lpc_answer_coordinates_reindex:
 assumes checked: "lpc_check_coordinate_transport old_coordinates new_coordinates routing"
 and invariant: "lpc_answer_coordinates old_coordinates ss"
 shows "lpc_answer_coordinates new_coordinates
   (lpc_reinterface (\<lambda>env x. env (routing x)) ss)"
 using checked invariant
 by (fastforce simp: lpc_check_coordinate_transport_def lpc_answer_coordinates_def
   lpc_reinterface_def list_all_iff)

lemma lpp_observer_coordinate_rebase:
 assumes checked: "lpc_check_coordinate_transport old_coordinates new_coordinates (case_sum routing Inr)"
 and invariant: "lpc_answer_coordinates old_coordinates runtime"
 shows "lpc_answer_coordinates new_coordinates
   (lpp_observer_rebase (\<lambda>_ env x. env (routing x)) runtime)"
proof -
 have exact: "lpp_observer_rebase (\<lambda>_ env x. env (routing x)) runtime =
   lpc_reinterface (\<lambda>env x. env (case_sum routing Inr x)) runtime"
  by (auto simp: lpp_observer_rebase_def lpc_reinterface_def case_prod_unfold fun_eq_iff split: sum.splits)
 show ?thesis unfolding exact by (rule lpc_answer_coordinates_reindex[OF checked invariant])
qed

definition lpc_check_coordinate_initialization where
 "lpc_check_coordinate_initialization coordinates payload =
  list_all (\<lambda>(a,b). a<length payload \<and> b<length payload \<and> payload!a = payload!b) coordinates"

lemma lpc_answer_coordinates_initialize:
 assumes checked: "lpc_check_coordinate_initialization coordinates payload"
 shows "lpc_answer_coordinates coordinates (lpc_return_eval eta [(frame_entry,payload)])"
 using checked
 by (auto simp: lpc_check_coordinate_initialization_def lpc_answer_coordinates_def
   lpc_return_eval_def lpc_return_env_def list_all_iff)

end
