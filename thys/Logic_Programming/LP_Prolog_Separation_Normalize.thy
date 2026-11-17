theory LP_Prolog_Separation_Normalize
 imports LP_Prolog_Separation_Fresh_Contract
begin

fun lpp_separation_goal where
 "lpp_separation_goal (LPPSeparate a b) = LPCUnify a b"

fun lpp_runtime_separation where
 "lpp_runtime_separation (LPCUnify a b) = (set2_lp_iterm a\<inter>set2_lp_iterm b={})"
| "lpp_runtime_separation _ = False"

definition lpp_check_separation_normalize where
 "lpp_check_separation_normalize fuel equations before after =
   (lp_cut_normalize fuel equations (map lpp_separation_goal before) =
     Some (Some (map lpp_separation_goal after)))"

text \<open>The payload is normalized by the shared verified equation normalizer.
The encoded equality goals are data here; they are not executed as unifications.
The initialized source equations remain a separate semantic premise.\<close>

lemma lpp_separation_payload_holds:
 "list_all lpp_runtime_separation
   (map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (map lpp_separation_goal facts)) =
   list_all (lpp_separation_holds eta) facts"
proof -
 have "lpp_runtime_separation (lp_cut_map (\<lambda>t. lp_ieval t eta) (lpp_separation_goal observation)) =
   lpp_separation_holds eta observation" for observation
   by (cases observation) simp
 then show ?thesis by (simp add: list_all_iff)
qed

lemma lpp_check_separation_normalize_sound:
 assumes checked: "lpp_check_separation_normalize fuel equations before after"
 and initialized: "lp_equations equations eta"
 and known: "list_all (lpp_separation_holds eta) before"
 shows "list_all (lpp_separation_holds eta) after"
proof -
 have same: "map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (map lpp_separation_goal after) =
   map (lp_cut_map (\<lambda>t. lp_ieval t eta)) (map lpp_separation_goal before)"
   by (rule lp_cut_normalize_success[OF _ initialized])
     (use checked in \<open>simp add: lpp_check_separation_normalize_def\<close>)
 show ?thesis using arg_cong[OF same, of "list_all lpp_runtime_separation"] known
   by (simp only: lpp_separation_payload_holds)
qed

ML \<open>
val checked = @{thms lpp_separation_payload_holds lpp_check_separation_normalize_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted separation normalization" else ();
\<close>
end
