theory LP_Answer_Clause_Rename
 imports LP_Answer_Symbol_Map
begin

definition lp_answer_rename_atom where
 "lp_answer_rename_atom names atom = (fst atom,map (map_term id ((!) names)) (snd atom))"

definition lp_answer_rename_clause where
 "lp_answer_rename_clause names clause =
  (lp_answer_rename_atom names (fst clause),map (lp_answer_rename_atom names) (snd clause))"

definition lp_answer_check_clause_rename where
 "lp_answer_check_clause_rename source_clause target_clause names =
  (distinct names \<and>
   list_all (\<lambda>atom. list_all (\<lambda>t. list_all (\<lambda>i. i<length names) (vars_term_list t)) (snd atom))
    (fst source_clause#snd source_clause) \<and> target_clause=lp_answer_rename_clause names source_clause)"

lemma lp_answer_rename_eval:
 assumes distinct: "distinct names"
 and bound: "vars_term t \<subseteq> {..<length names}"
 shows "lp_ieval (map_term id ((!) names) t)
   (\<lambda>x. nu (inv_into {..<length names} ((!) names) x)) = lp_ieval t nu"
proof -
 have injective: "inj_on ((!) names) {..<length names}"
  by (rule inj_on_nth[OF distinct]) simp
 have same: "inv_into {..<length names} ((!) names) (names!i)=i" if "i<length names" for i
  by (rule inv_into_f_f[OF injective]) (use that in simp)
 show ?thesis using bound by (induct t) (auto simp: same intro!: map_cong)
qed

lemma lp_answer_checked_rename_evaluates:
 assumes checked: "lp_answer_check_clause_rename source_clause target_clause names"
 shows "\<exists>nu'. lp_atom_eval (fst target_clause) nu'=lp_atom_eval (fst source_clause) nu \<and>
   map (\<lambda>b. lp_atom_eval b nu') (snd target_clause)=map (\<lambda>b. lp_atom_eval b nu) (snd source_clause)"
proof -
 let ?nu = "\<lambda>x. nu (inv_into {..<length names} ((!) names) x)"
 have distinct: "distinct names" and target_clause: "target_clause=lp_answer_rename_clause names source_clause"
  using checked by (auto simp: lp_answer_check_clause_rename_def)
 have bounded: "vars_term t \<subseteq> {..<length names}"
  if "atom\<in>set (fst source_clause#snd source_clause)" "t\<in>set (snd atom)" for atom t
  using checked that by (auto simp: lp_answer_check_clause_rename_def list_all_iff set_vars_term_list)
 have eval: "lp_atom_eval (lp_answer_rename_atom names atom) ?nu=lp_atom_eval atom nu"
  if "atom\<in>set (fst source_clause#snd source_clause)" for atom
  unfolding lp_answer_rename_atom_def lp_atom_eval_def
  by (auto simp: map_map o_def intro!: map_cong lp_answer_rename_eval[OF distinct bounded[OF that]])
 show ?thesis
  apply (rule exI[of _ ?nu])
  using eval by (auto simp: target_clause lp_answer_rename_clause_def map_map o_def intro!: map_cong)
qed

lemma lp_answer_clause_rename_rejects_alias:
 "\<not> distinct names \<Longrightarrow> \<not> lp_answer_check_clause_rename source_clause target_clause names"
 by (simp add: lp_answer_check_clause_rename_def)

definition lp_answer_check_renamed_program where
 "lp_answer_check_renamed_program P Q receipts =
  (length receipts=length P \<and> list_all (\<lambda>i.
    fst (receipts!i)<length Q \<and>
    lp_answer_check_clause_rename (P!i) (Q!fst (receipts!i)) (snd (receipts!i))) [0..<length P])"

lemma lp_answer_checked_renamed_step:
 assumes checked: "lp_answer_check_renamed_program P Q receipts"
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
 let ?d = "fst (receipts!c)"
 have bound: "?d<length Q" and renamed: "lp_answer_check_clause_rename (P!c) (Q!?d) (snd (receipts!c))"
  using checked index by (auto simp: lp_answer_check_renamed_program_def list_all_iff)
 obtain nu' where head: "lp_atom_eval (fst (Q!?d)) nu'=lp_atom_eval (fst (P!c)) nu"
 and body: "map (\<lambda>b. lp_atom_eval b nu') (snd (Q!?d))=map (\<lambda>b. lp_atom_eval b nu) (snd (P!c))"
  using lp_answer_checked_rename_evaluates[OF renamed, of nu] by blast
 have match: "lp_iatom_subst a sigma=lp_atom_eval (fst (Q!?d)) nu'" using matching head by simp
 show ?thesis unfolding initial final environment
  using lp_seg_answer_step.resolve[OF bound match, of tail rho] by (simp add: body)
qed

lemma lp_answer_checked_renamed_path:
 assumes checked: "lp_answer_check_renamed_program P Q receipts"
 and path: "((gs,rho),(hs,eta))\<in>(lp_seg_answer_step P)\<^sup>*"
 shows "((gs,rho),(hs,eta))\<in>(lp_seg_answer_step Q)\<^sup>*"
 using path
proof (induct rule: rtrancl_induct2)
 case refl then show ?case by simp
next
 case (step hs eta ks tau)
 show ?case by (rule rtrancl_into_rtrancl[OF step.hyps(3) lp_answer_checked_renamed_step[OF checked step.hyps(2)]])
qed

ML \<open>
val checked = @{thms lp_answer_rename_eval lp_answer_checked_rename_evaluates
 lp_answer_clause_rename_rejects_alias lp_answer_checked_renamed_step lp_answer_checked_renamed_path};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted clause variable transport" else ();
\<close>
end
