theory LP_Prolog_Stable_Shape_Entries
 imports LP_Return_Shape_Entry LP_Prolog_Stable_Structural_Coverage LP_Prolog_Stable_Return_Context
begin

fun lpp_check_shape_entry_row where
  "lpp_check_shape_entry_row T G seeds shapes positions ((h,ps,b,gs),os) facts =
    (length shapes=length (snd b) \<and>
     lpp_check_path_types T ps gs facts \<and>
     lpp_shape_seed_check G (map lpp_transfer_variable facts) (ps,gs,os) seeds \<and>
     list_all (\<lambda>i. i<length shapes \<and> shapes!i\<noteq>LPReturnAny \<and>
       lp_return_shape_check 16 G seeds (shapes!i) (snd b!i)) positions)"

lemma lpp_checked_shape_entry_projections:
  fixes P :: "string lpp_success_clause list"
    and eta :: "string \<Rightarrow> (string lp_cut_symbol,string) lp_iterm"
    and flt :: "'f afs" and data :: "string lp_cut_symbol \<Rightarrow> 'f"
  assumes compatible: "lpp_stable_integer_operations operation"
    and checked: "lpp_check_shape_entry_row T G seeds shapes positions ((h,ps,b,gs),os) facts"
    and transfer: "lpp_check_transfer_program T P receipts"
    and observed: "lpp_stable_context_holds operation P (ps,gs,os) eta"
    and filter: "lp_return_shape_filter_check flt data G"
  shows "\<forall>i\<in>set positions. i<length (snd b) \<and>
    (\<exists>u::('f,string) term. lp_iproject flt (map_lp_iterm data id (snd (lpp_success_atom_eval b eta)!i)) u)"
proof -
  have typed: "lpp_check_path_types T ps gs facts"
    and seed_check: "lpp_shape_seed_check G (map lpp_transfer_variable facts) (ps,gs,os) seeds"
    and lengths: "length shapes=length (snd b)"
    and checks: "\<forall>i\<in>set positions. i<length shapes \<and> shapes!i\<noteq>LPReturnAny \<and>
      lp_return_shape_check 16 G seeds (shapes!i) (snd b!i)"
    using checked by (auto simp: list_all_iff)
  have guards: "list_all (lpp_success_guard_holds (lpp_stable_scalar_evaluation operation) eta) gs"
    and prefix: "list_all (lpp_guarded_success P (lpp_stable_scalar_evaluation operation))
      (map (\<lambda>g. lpp_success_atom_eval g eta) ps)"
    using observed by (auto simp: lpp_stable_context_holds_def lpp_evaluation_context_holds_def list_all_iff)
  have known: "lpp_integer_known (map lpp_transfer_variable facts) eta"
    by (rule lpp_check_path_types_sound[OF transfer typed guards prefix lpp_stable_evaluation_integer_contract[OF compatible]])
  have integers: "\<forall>x\<in>set (map lpp_transfer_variable facts). lp_seg_ground (eta x)"
    using known by (auto simp: lpp_integer_known_def lpp_integer_value_def intro: lp_seg_ground.intros)
  have seeds: "lp_return_shape_known G seeds eta"
    by (rule lpp_shape_seed_check_sound[OF seed_check integers lpp_stable_context_finite_envelope[OF compatible observed]])
  show ?thesis
  proof (intro ballI conjI)
    fix i assume member: "i\<in>set positions"
    have bound: "i<length (snd b)" and shape: "shapes!i\<noteq>LPReturnAny"
      and term_check: "lp_return_shape_check 16 G seeds (shapes!i) (snd b!i)"
      using checks member lengths by auto
    show "i<length (snd b)" by (rule bound)
    have projected: "\<exists>u::('f,string) term. lp_iproject flt (map_lp_iterm data id (lp_ieval (snd b!i) eta)) u"
      by (rule lp_return_shape_entry_projection[OF filter seeds shape term_check])
    show "\<exists>u::('f,string) term. lp_iproject flt (map_lp_iterm data id (snd (lpp_success_atom_eval b eta)!i)) u"
      using projected bound by (simp add: lpp_success_atom_eval_def)
  qed
qed

end
