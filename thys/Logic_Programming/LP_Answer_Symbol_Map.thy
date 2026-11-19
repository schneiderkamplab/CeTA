theory LP_Answer_Symbol_Map
 imports LP_SEG_Answers LP_Constructor_Source
begin

text \<open>Transport successful residual paths through explicit predicate and
data-symbol maps. Runtime terms may be infinite. This transports witnesses;
it does not infer successful-return properties from termination.\<close>

definition lp_answer_map_atom where
 "lp_answer_map_atom predicate_map symbol_map atom =
  (predicate_map (fst atom),map (map_term symbol_map id) (snd atom))"

definition lp_answer_map_iatom where
 "lp_answer_map_iatom predicate_map symbol_map atom =
  (predicate_map (fst atom),map (map_lp_iterm symbol_map id) (snd atom))"

definition lp_answer_map_program where
 "lp_answer_map_program predicate_map symbol_map P =
  map (\<lambda>(head,body). (lp_answer_map_atom predicate_map symbol_map head,
    map (lp_answer_map_atom predicate_map symbol_map) body)) P"

lemma lp_answer_symbol_eval:
 "map_lp_iterm symbol_map id (lp_ieval t rho) =
  lp_ieval (map_term symbol_map id t) (\<lambda>x. map_lp_iterm symbol_map id (rho x))"
 by (induct t) (auto simp: map_map o_def intro!: map_cong)

lemma lp_answer_symbol_atom_eval:
 "lp_answer_map_iatom predicate_map symbol_map (lp_atom_eval atom rho) =
  lp_atom_eval (lp_answer_map_atom predicate_map symbol_map atom)
   (\<lambda>x. map_lp_iterm symbol_map id (rho x))"
 by (simp add: lp_answer_map_iatom_def lp_answer_map_atom_def lp_atom_eval_def
   map_map o_def lp_answer_symbol_eval)

lemma lp_answer_symbol_atom_subst:
 "lp_answer_map_iatom predicate_map symbol_map (lp_iatom_subst atom sigma) =
  lp_iatom_subst (lp_answer_map_iatom predicate_map symbol_map atom)
   (\<lambda>x. map_lp_iterm symbol_map id (sigma x))"
 by (simp add: lp_answer_map_iatom_def lp_iatom_subst_def map_map o_def lp_data_map_subst)

lemma lp_answer_symbol_step:
 assumes step: "((gs,rho),(hs,eta))\<in>lp_seg_answer_step P"
 shows "((map (lp_answer_map_iatom predicate_map symbol_map) gs,\<lambda>x. map_lp_iterm symbol_map id (rho x)),
   (map (lp_answer_map_iatom predicate_map symbol_map) hs,\<lambda>x. map_lp_iterm symbol_map id (eta x)))
   \<in>lp_seg_answer_step (lp_answer_map_program predicate_map symbol_map P)"
proof -
 obtain c a sigma nu tail where index: "c<length P"
 and matching: "lp_iatom_subst a sigma=lp_atom_eval (fst (P!c)) nu"
 and before: "gs=a#tail"
 and after: "hs=map (\<lambda>b. lp_atom_eval b nu) (snd (P!c)) @
   map (\<lambda>b. lp_iatom_subst b sigma) tail"
 and environment: "eta=(\<lambda>x. lp_isubst (rho x) sigma)"
  using step by (cases rule: lp_seg_answer_step.cases) blast
 let ?map = "lp_answer_map_iatom predicate_map symbol_map"
 let ?sigma = "\<lambda>x. map_lp_iterm symbol_map id (sigma x)"
 let ?nu = "\<lambda>x. map_lp_iterm symbol_map id (nu x)"
 let ?rho = "\<lambda>x. map_lp_iterm symbol_map id (rho x)"
 let ?P = "lp_answer_map_program predicate_map symbol_map P"
 have bound: "c<length ?P" using index by (simp add: lp_answer_map_program_def)
 have equation: "lp_iatom_subst (?map a) ?sigma=lp_atom_eval (fst (?P!c)) ?nu"
  using arg_cong[OF matching, of ?map] index
  by (simp add: lp_answer_map_program_def lp_answer_symbol_atom_subst lp_answer_symbol_atom_eval split: prod.splits)
 have mapped: "(((?map a)#map ?map tail,?rho),
   (map (\<lambda>b. lp_atom_eval b ?nu) (snd (?P!c)) @
    map (\<lambda>b. lp_iatom_subst b ?sigma) (map ?map tail),
    \<lambda>x. lp_isubst (?rho x) ?sigma))\<in>lp_seg_answer_step ?P"
  by (rule lp_seg_answer_step.resolve[OF bound equation])
 show ?thesis using mapped index
  by (simp add: before after environment lp_answer_map_program_def map_map o_def
    lp_answer_symbol_atom_eval lp_answer_symbol_atom_subst lp_data_map_subst split: prod.splits)
qed

lemma lp_answer_symbol_path:
 assumes path: "((gs,rho),(hs,eta))\<in>(lp_seg_answer_step P)\<^sup>*"
 shows "((map (lp_answer_map_iatom predicate_map symbol_map) gs,\<lambda>x. map_lp_iterm symbol_map id (rho x)),
   (map (lp_answer_map_iatom predicate_map symbol_map) hs,\<lambda>x. map_lp_iterm symbol_map id (eta x)))
   \<in>(lp_seg_answer_step (lp_answer_map_program predicate_map symbol_map P))\<^sup>*"
 using path
proof (induct rule: rtrancl_induct2)
 case refl then show ?case by simp
next
 case (step hs eta ks tau)
 show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) lp_answer_symbol_step[OF step.hyps(2)]])
qed

lemma lp_answer_step_program_subset:
 assumes included: "set P \<subseteq> set Q"
 and step: "((gs,rho),(hs,eta))\<in>lp_seg_answer_step P"
 shows "((gs,rho),(hs,eta))\<in>lp_seg_answer_step Q"
proof -
 obtain c a sigma nu tail where index: "c<length P"
 and matching: "lp_iatom_subst a sigma=lp_atom_eval (fst (P!c)) nu"
 and initial: "gs=a#tail"
 and final: "hs=map (\<lambda>b. lp_atom_eval b nu) (snd (P!c)) @
   map (\<lambda>b. lp_iatom_subst b sigma) tail"
 and environment: "eta=(\<lambda>x. lp_isubst (rho x) sigma)"
  using step by (cases rule: lp_seg_answer_step.cases) blast
 obtain d where bound: "d<length Q" and same: "Q!d=P!c"
  using included index by (metis in_set_conv_nth subsetD)
 show ?thesis unfolding initial final environment
  using lp_seg_answer_step.resolve[OF bound, of a sigma nu tail rho] matching
  by (simp add: same)
qed

lemma lp_answer_path_program_subset:
 assumes included: "set P \<subseteq> set Q"
 and path: "((gs,rho),(hs,eta))\<in>(lp_seg_answer_step P)\<^sup>*"
 shows "((gs,rho),(hs,eta))\<in>(lp_seg_answer_step Q)\<^sup>*"
 using path
proof (induct rule: rtrancl_induct2)
 case refl then show ?case by simp
next
 case (step hs eta ks tau)
 show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) lp_answer_step_program_subset[OF included step.hyps(2)]])
qed

lemma lp_answer_symbol_path_in:
 assumes included: "set (lp_answer_map_program predicate_map symbol_map P) \<subseteq> set Q"
 and path: "((gs,rho),(hs,eta))\<in>(lp_seg_answer_step P)\<^sup>*"
 shows "((map (lp_answer_map_iatom predicate_map symbol_map) gs,\<lambda>x. map_lp_iterm symbol_map id (rho x)),
   (map (lp_answer_map_iatom predicate_map symbol_map) hs,\<lambda>x. map_lp_iterm symbol_map id (eta x)))
   \<in>(lp_seg_answer_step Q)\<^sup>*"
 by (rule lp_answer_path_program_subset[OF included lp_answer_symbol_path[OF path]])

ML \<open>
val checked = @{thms lp_answer_symbol_eval lp_answer_symbol_atom_eval
 lp_answer_symbol_atom_subst lp_answer_symbol_step lp_answer_symbol_path
 lp_answer_step_program_subset lp_answer_path_program_subset lp_answer_symbol_path_in};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted residual symbol transport" else ();
\<close>
end
