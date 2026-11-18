theory LP_Prolog_Attached_Observer_Product
 imports LP_Prolog_Attached_Observer_Entry LP_Prolog_Return_Interface
begin

text \<open>Two interfaces observe one existing answer execution. The left
coordinates retain the helper's checked context and the right coordinates
retain the ambient caller. Neither projection requires runtime nonsharing.
Saved alternatives keep their own combined environments.\<close>

lemma lpp_observer_reindex_eval:
 "lp_ieval (map_term id route_index t) eta = lp_ieval t (\<lambda>x. eta (route_index x))"
 by (induct t) auto

lemma lpp_observer_reindex_attach:
 "lpc_reinterface (\<lambda>eta x. eta (route_index x))
   (lpc_attach_answers (map (lp_cut_map (map_term id route_index)) rest) ss) =
  lpc_attach_answers rest (lpc_reinterface (\<lambda>eta x. eta (route_index x)) ss)"
proof -
 have frame: "lpc_attach_frame (map (lp_cut_map (map_term id route_index)) rest) (e,eta) =
   lpc_attach_frame rest (e,\<lambda>x. eta (route_index x))" for e eta
  by (cases e) (simp_all add: map_map o_def lp_cut_map_comp lpp_observer_reindex_eval)
 show ?thesis by (auto simp: lpc_reinterface_def lpc_attach_answers_def map_map split_def frame
   split: prod.splits)
qed

lemma lpp_observer_reindex_active:
 "lpc_prefix_active (lpc_reinterface F ss) = lpc_prefix_active ss"
 proof (cases ss)
 case Nil then show ?thesis by (simp add: lpc_reinterface_def)
next
 case (Cons frame saved)
 obtain e eta where "frame=(e,eta)" by (cases frame) auto
 then show ?thesis by (cases e) (simp_all add: Cons lpc_reinterface_def)
qed

lemma lpp_attached_observer_product_step:
 assumes active: "lpc_prefix_active ss"
 and step: "lpp_domain_answers P B U D
   (lpc_attach_answers rest (lpc_reinterface (\<lambda>eta x. eta (Inr x)) ss)) event result"
 shows "event=None \<and> (\<exists>tt.
   lpp_domain_answers P B U D ss None tt \<and>
   lpp_domain_answers P B U D
    (lpc_attach_answers (map (lp_cut_map (map_term id Inr)) rest) ss) None
    (lpc_attach_answers (map (lp_cut_map (map_term id Inr)) rest) tt) \<and>
   lpp_domain_answers P B U D
    (lpc_reinterface (\<lambda>eta x. eta (Inl x)) ss) None
    (lpc_reinterface (\<lambda>eta x. eta (Inl x)) tt) \<and>
   result=lpc_attach_answers rest (lpc_reinterface (\<lambda>eta x. eta (Inr x)) tt))"
proof -
 let ?L = "\<lambda>eta x. eta (Inl x)"
 let ?R = "\<lambda>eta x. eta (Inr x)"
 let ?rest = "map (lp_cut_map (map_term id Inr)) rest"
 have actual: "lpp_domain_answers P B U D
   (lpc_reinterface ?R (lpc_attach_answers ?rest ss)) event result"
  using step by (simp only: lpp_observer_reindex_attach)
 obtain ev us where joint: "lpp_domain_answers P B U D
    (lpc_attach_answers ?rest ss) ev us"
  and emitted: "map_option ?R ev=event"
  and projected: "lpc_reinterface ?R us=result"
  using lpp_domain_reinterface_reflect[where F = ?R, OF _ actual] by blast
 obtain tt where silent: "ev=None"
  and helper: "lpp_domain_answers P B U D ss None tt"
  and attached: "us=lpc_attach_answers ?rest tt"
  using lpp_domain_attach_reflect[OF active joint] by blast
 have left: "lpp_domain_answers P B U D
   (lpc_reinterface ?L ss) None (lpc_reinterface ?L tt)"
  using lpp_domain_reinterface_forward[where F = ?L, OF _ helper] by simp
 show ?thesis using joint emitted projected silent helper attached left
  by (auto simp: lpp_observer_reindex_attach)
qed

lemma lpp_observer_product_initial:
 "lpc_reinterface (\<lambda>eta x. eta (Inl x)) [(e,case_sum helper caller)] = [(e,helper)]"
 "lpc_reinterface (\<lambda>eta x. eta (Inr x)) [(e,case_sum helper caller)] = [(e,caller)]"
 by (simp_all add: lpc_reinterface_def)

lemma lpp_observer_reindex_leaf:
 "lpp_leaf_stack_invariant A specs (lpc_reinterface (\<lambda>eta x. eta (route_index x)) ss) =
  lpp_leaf_stack_invariant A (map (\<lambda>(slot,shape). (route_index slot,shape)) specs) ss"
 by (auto simp: lpp_leaf_stack_invariant_def lpc_reinterface_def list_all_iff split_def)

text \<open>The native finite representation concatenates observation tuples.
These are the existing checked projections, not an unchecked positional cast.
The same runtime value may occur in both tuples.\<close>

lemma lpp_observer_product_left_projection:
 "lpc_check_return_projection [0..<length helper]
   [(e,helper@caller)] [(e,helper)]"
proof -
 have tuple: "map ((!) (helper@caller)) [0..<length helper] = helper"
  by (rule nth_equalityI) (auto simp: nth_append)
 show ?thesis by (simp add: lpc_check_return_projection_def list_all_iff tuple)
qed

lemma lpp_observer_product_right_projection:
 "lpc_check_return_projection [length helper..<length helper+length caller]
   [(e,helper@caller)] [(e,caller)]"
proof -
 have tuple: "map ((!) (helper@caller)) [length helper..<length helper+length caller] = caller"
  by (rule nth_equalityI) (auto simp: nth_append)
 show ?thesis by (simp add: lpc_check_return_projection_def list_all_iff tuple)
qed

ML \<open>
val checked = @{thms lpp_observer_reindex_eval lpp_observer_reindex_attach
 lpp_observer_reindex_active lpp_attached_observer_product_step
 lpp_observer_product_initial lpp_observer_reindex_leaf
 lpp_observer_product_left_projection lpp_observer_product_right_projection};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted attached observer product" else ();
\<close>
end
