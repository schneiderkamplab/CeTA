theory LP_Prolog_Bounded_Arithmetic
 imports LP_Prolog_Bounded_Instantiation LP_Prolog_Stable_Is
begin

text \<open>Successful scalar evaluation changes only its result variable.
The result may be integer or binary64; all atomic results are admitted here.
The evaluated expression is not assumed atomic.\<close>

lemma lpp_scalar_unifier_bounded_images:
 assumes chosen: "lpp_scalar_unifier a f=Some mu"
 and allowed: "Fun (LPCUser f) []\<in>A"
 shows "lpp_bounded_images A mu V"
proof -
 have image: "\<exists>u\<in>A. LPIFun (LPCUser f) []=lp_ieval u LPIVar"
  by (rule bexI[of _ "Fun (LPCUser f) []"]) (use allowed in auto)
 show ?thesis using chosen image unfolding lpp_bounded_images_def
  by (cases a) (auto split: if_splits)
qed

lemma lpp_stable_is_bounded_images:
 assumes success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)"
 and atoms: "\<And>f. Fun (LPCUser f) []\<in>A"
 shows "lpp_bounded_images A mu V"
proof -
 obtain f where chosen: "lpp_scalar_unifier a f=Some mu"
  using success by (auto simp: lpp_stable_is_outcome_def split: option.splits)
 show ?thesis by (rule lpp_scalar_unifier_bounded_images[OF chosen atoms])
qed

lemma lpp_stable_is_structural_effect:
 fixes t :: "(string lp_cut_symbol,string) term"
 and A :: "(string lp_cut_symbol,string) term set"
 assumes success: "lpp_stable_is_outcome operation a e (LPPBuiltinSuccess mu)"
 and atoms: "\<And>f. Fun (LPCUser f) []\<in>A"
 shows "\<exists>u. lp_isubst (lp_ieval t LPIVar) mu=lp_ieval u LPIVar \<and>
  lpp_leaf_effect A (lpp_structure_template t) (lpp_structure_template u)"
 by (rule lpp_bounded_runtime_structural_effect)
   (rule lpp_stable_is_bounded_images[OF success], rule atoms)

ML \<open>
val checked = @{thms lpp_scalar_unifier_bounded_images lpp_stable_is_bounded_images
 lpp_stable_is_structural_effect};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted bounded arithmetic effect" else ();
\<close>
end
