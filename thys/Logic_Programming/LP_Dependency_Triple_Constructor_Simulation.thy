theory LP_Dependency_Triple_Constructor_Simulation
  imports LP_Dependency_Triple_Constructor_Success LP_Dependency_Triple_Simulation
begin

context lp_triple_translation
begin

definition dt_constructor_strict where
  "dt_constructor_strict C = {(lp_ieval l \<rho>,lp_ieval r \<rho>) | l r \<rho>.
    (l,r)\<in>set dt_pairs \<and> (\<forall>x. lp_constructor_value C (\<rho> x))}"

definition dt_constructor_step where
  "dt_constructor_step C U = (lp_clink C (set dt_support) U)\<^sup>* O
    dt_constructor_strict C O (lp_clink C (set dt_support) U)\<^sup>*"

lemma dt_constructor_control_instance_pair:
  assumes range: "range data\<subseteq>C" and member: "p\<in>set dt_control"
  shows "(lp_ieval (lp_mark sharp (fst p)) (\<lambda>x. map_lp_iterm data id (\<rho> x)),
    lp_ieval (lp_mark sharp (snd p)) (\<lambda>x. map_lp_iterm data id (\<rho> x)))
    \<in>dt_constructor_strict C"
proof -
  have pair: "(lp_mark sharp (fst p),lp_mark sharp (snd p))\<in>set dt_pairs"
    using member unfolding dt_pairs_def by force
  show ?thesis unfolding dt_constructor_strict_def
    using pair lp_constructor_value_map[OF range] by blast
qed

lemma dt_constructor_stepI:
  assumes before: "(s,l)\<in>(lp_clink C (set dt_support) U)\<^sup>*"
    and strict: "(l,r)\<in>dt_constructor_strict C"
    and after: "(r,t)\<in>(lp_clink C (set dt_support) U)\<^sup>*"
  shows "(s,t)\<in>dt_constructor_step C U"
  using assms by (auto simp: dt_constructor_step_def)

lemma dt_data_constructor_prefix_tail:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set (lp_translation.translated P inp out pu) \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. pu c i\<in>U" and marked: "\<And>c i. sharp (du c i)\<in>U"
    and prefix: "list_all (lp_data_fixed_atom data) ps" and target: "lp_data_fixed_atom data b"
    and c: "c<length D" and triple: "D!c=(h,ps,b)"
    and i: "i<length ps"
    and success: "((map (\<lambda>g. lp_atom_eval g \<rho>) (drop i ps),\<rho>),([],\<eta>))
      \<in>(lp_seg_answer_step P)\<^sup>*"
  shows "(LPIFun (sharp (du c i))
      (lp_itag inp (lp_atom_eval (ps!i) (\<lambda>x. map_lp_iterm data id (\<rho> x))) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) (dt_saved c i)),
      lp_itag (sharp \<circ> inp) (lp_atom_eval b (\<lambda>x. map_lp_iterm data id (\<eta> x))))\<in>(dt_constructor_step C U)\<^sup>+"
  using i success
proof (induct "length ps - i" arbitrary: i \<rho> rule: less_induct)
  case less
  have body: "drop i ps = ps!i # drop (Suc i) ps"
    using less.prems(1) by (simp add: Cons_nth_drop_Suc)
  have split_shape: "map (\<lambda>g. lp_atom_eval g \<rho>) (drop i ps) =
      [lp_atom_eval (ps!i) \<rho>] @ map (\<lambda>g. lp_atom_eval g \<rho>) (drop (Suc i) ps)"
    by (simp only: body list.map append_Cons append_Nil)
  note split = lp_seg_answer_steps_split[OF less.prems(2), THEN spec,
    of "[lp_atom_eval (ps!i) \<rho>]", THEN spec, of "drop (Suc i) ps"]
  obtain \<mu> where head: "(([lp_atom_eval (ps!i) \<rho>],\<rho>),([],\<mu>))
      \<in>(lp_seg_answer_step P)\<^sup>*"
    and tail: "((map (\<lambda>g. lp_atom_eval g \<mu>) (drop (Suc i) ps),\<mu>),([],\<eta>))
      \<in>(lp_seg_answer_step P)\<^sup>*"
    using mp[OF split split_shape] by blast
  have atom: "lp_data_fixed_atom data (ps!i)"
    using prefix less.prems(1) by (simp add: list_all_length)
  have weak: "(LPIFun (sharp (du c i))
      (lp_itag inp (lp_atom_eval (ps!i) (\<lambda>x. map_lp_iterm data id (\<rho> x))) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) (dt_saved c i)),
      LPIFun (sharp (du c i))
      (lp_itag out (lp_atom_eval (ps!i) (\<lambda>x. map_lp_iterm data id (\<mu> x))) # map (\<lambda>x. map_lp_iterm data id (\<mu> x)) (dt_saved c i)))
      \<in>(lp_clink C (set dt_support) U)\<^sup>*"
    unfolding dt_support_def
    using lp_translation.lp_triple_data_success_capture[where inp=inp and out=out and u=pu,
      OF fixed range shapes frames marked head]
    by (simp add: lp_data_atom_eval[OF atom])
  have member: "dt_return c i\<in>set dt_control"
    by (rule dt_return_member[OF c]) (use triple less.prems(1) in simp)
  show ?case
  proof (cases "Suc i < length ps")
    case True
    have strict: "(LPIFun (sharp (du c i))
        (lp_itag out (lp_atom_eval (ps!i) (\<lambda>x. map_lp_iterm data id (\<mu> x))) # map (\<lambda>x. map_lp_iterm data id (\<mu> x)) (dt_saved c i)),
        LPIFun (sharp (du c (Suc i)))
        (lp_itag inp (lp_atom_eval (ps!Suc i) (\<lambda>x. map_lp_iterm data id (\<mu> x))) # map (\<lambda>x. map_lp_iterm data id (\<mu> x)) (dt_saved c (Suc i))))\<in>dt_constructor_strict C"
      using dt_constructor_control_instance_pair[OF range member, of \<mu>]
      by (simp add: dt_return_def triple True dt_frame_def lp_itag_eval o_def)
    have first: "(LPIFun (sharp (du c i))
        (lp_itag inp (lp_atom_eval (ps!i) (\<lambda>x. map_lp_iterm data id (\<rho> x))) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) (dt_saved c i)),
        LPIFun (sharp (du c (Suc i)))
        (lp_itag inp (lp_atom_eval (ps!Suc i) (\<lambda>x. map_lp_iterm data id (\<mu> x))) # map (\<lambda>x. map_lp_iterm data id (\<mu> x)) (dt_saved c (Suc i))))\<in>dt_constructor_step C U"
      by (rule dt_constructor_stepI[OF weak strict]) simp
    have continuation: "(LPIFun (sharp (du c (Suc i)))
        (lp_itag inp (lp_atom_eval (ps!Suc i) (\<lambda>x. map_lp_iterm data id (\<mu> x))) # map (\<lambda>x. map_lp_iterm data id (\<mu> x)) (dt_saved c (Suc i))),
        lp_itag (sharp \<circ> inp) (lp_atom_eval b (\<lambda>x. map_lp_iterm data id (\<eta> x))))\<in>(dt_constructor_step C U)\<^sup>+"
      by (rule less.hyps[OF _ True tail]) (use True in simp)
    show ?thesis by (rule trancl_trans[OF r_into_trancl[OF first] continuation])
  next
    case False
    have finished: "drop (Suc i) ps=[]" using False by simp
    have eta: "\<eta>=\<mu>"
      using tail finished by (auto elim: converse_rtranclE lp_seg_answer_step.cases)
    have strict: "(LPIFun (sharp (du c i))
        (lp_itag out (lp_atom_eval (ps!i) (\<lambda>x. map_lp_iterm data id (\<mu> x))) # map (\<lambda>x. map_lp_iterm data id (\<mu> x)) (dt_saved c i)),
        lp_itag (sharp \<circ> inp) (lp_atom_eval b (\<lambda>x. map_lp_iterm data id (\<eta> x))))\<in>dt_constructor_strict C"
      using dt_constructor_control_instance_pair[OF range member, of \<mu>]
      by (simp add: dt_return_def triple False dt_frame_def lp_itag_eval lp_tag_def o_def eta)
    show ?thesis by (rule r_into_trancl[OF dt_constructor_stepI[OF weak strict]]) simp
  qed
qed

theorem dt_data_constructor_call_simulation:
  assumes fixed: "lp_data_fixed_program data P" and range: "range data\<subseteq>C"
    and shapes: "\<And>l r. (l,r)\<in>set (lp_translation.translated P inp out pu) \<Longrightarrow> lp_constructor_lhs C l"
    and frames: "\<And>c i. pu c i\<in>U" and marked: "\<And>c i. sharp (du c i)\<in>U"
    and triples: "\<And>h ps goal. (h,ps,goal)\<in>set D \<Longrightarrow>
      lp_data_fixed_atom data h \<and> list_all (lp_data_fixed_atom data) ps \<and>
      lp_data_fixed_atom data goal"
    and call: "(a,b)\<in>lp_triple_calls (set D) P"
  shows "(lp_itag (sharp \<circ> inp) (lp_data_atom data a),lp_itag (sharp \<circ> inp) (lp_data_atom data b))\<in>(dt_constructor_step C U)\<^sup>+"
proof -
  obtain h ps goal \<sigma> \<rho> \<eta> where triple: "(h,ps,goal)\<in>set D"
    and matching: "lp_iatom_subst a \<sigma>=lp_atom_eval h \<rho>"
    and success: "((map (\<lambda>g. lp_atom_eval g \<rho>) ps,\<rho>),([],\<eta>))
      \<in>(lp_seg_answer_step P)\<^sup>*"
    and b: "b=lp_atom_eval goal \<eta>"
    using call unfolding lp_triple_calls_def by blast
  have hfixed: "lp_data_fixed_atom data h"
    and psfixed: "list_all (lp_data_fixed_atom data) ps"
    and bfixed: "lp_data_fixed_atom data goal"
    using triples[OF triple] by blast+
  have mapped_b: "lp_data_atom data b=lp_atom_eval goal (\<lambda>x. map_lp_iterm data id (\<eta> x))"
    by (simp add: b lp_data_atom_eval[OF bfixed])
  have mapped_match: "lp_iatom_subst (lp_data_atom data a) (\<lambda>x. map_lp_iterm data id (\<sigma> x)) =
    lp_atom_eval h (\<lambda>x. map_lp_iterm data id (\<rho> x))"
    using arg_cong[OF matching, of "lp_data_atom data"]
    by (simp add: lp_data_atom_subst lp_data_atom_eval[OF hfixed])
  obtain c where c: "c<length D" and dc: "D!c=(h,ps,goal)"
    using triple by (metis in_set_conv_nth)
  have entry: "dt_entry c\<in>set dt_control" by (rule dt_entry_member[OF c])
  have instantiate: "(lp_itag (sharp \<circ> inp) (lp_data_atom data a),
      lp_itag (sharp \<circ> inp) (lp_atom_eval h (\<lambda>x. map_lp_iterm data id (\<rho> x))))\<in>lp_clink C (set dt_support) U"
  proof -
    have eq: "lp_itag (sharp \<circ> inp) (lp_atom_eval h (\<lambda>x. map_lp_iterm data id (\<rho> x))) =
      lp_isubst (lp_itag (sharp \<circ> inp) (lp_data_atom data a)) (\<lambda>x. map_lp_iterm data id (\<sigma> x))"
      using mapped_match by (metis lp_itag_subst)
    show ?thesis unfolding lp_clink_def using eq by blast
  qed
  show ?thesis
  proof (cases "ps=[]")
    case True
    have eta: "\<eta>=\<rho>"
      using success True by (auto elim: converse_rtranclE lp_seg_answer_step.cases)
    have strict: "(lp_itag (sharp \<circ> inp) (lp_atom_eval h (\<lambda>x. map_lp_iterm data id (\<rho> x))),
        lp_itag (sharp \<circ> inp) (lp_data_atom data b))\<in>dt_constructor_strict C"
      using dt_constructor_control_instance_pair[OF range entry, of \<rho>]
      by (simp add: dt_entry_def dc True mapped_b eta lp_itag_eval lp_tag_def o_def)
    show ?thesis by (rule r_into_trancl[OF dt_constructor_stepI[OF r_into_rtrancl[OF instantiate] strict]]) simp
  next
    case False
    have strict: "(lp_itag (sharp \<circ> inp) (lp_atom_eval h (\<lambda>x. map_lp_iterm data id (\<rho> x))),
        LPIFun (sharp (du c 0))
        (lp_itag inp (lp_atom_eval (ps!0) (\<lambda>x. map_lp_iterm data id (\<rho> x))) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) (dt_saved c 0)))\<in>dt_constructor_strict C"
      using dt_constructor_control_instance_pair[OF range entry, of \<rho>]
      by (simp add: dt_entry_def dc False dt_frame_def lp_itag_eval lp_tag_def o_def)
    have first: "(lp_itag (sharp \<circ> inp) (lp_data_atom data a),LPIFun (sharp (du c 0))
        (lp_itag inp (lp_atom_eval (ps!0) (\<lambda>x. map_lp_iterm data id (\<rho> x))) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) (dt_saved c 0)))\<in>dt_constructor_step C U"
      by (rule dt_constructor_stepI[OF r_into_rtrancl[OF instantiate] strict]) simp
    have rest: "(LPIFun (sharp (du c 0))
        (lp_itag inp (lp_atom_eval (ps!0) (\<lambda>x. map_lp_iterm data id (\<rho> x))) # map (\<lambda>x. map_lp_iterm data id (\<rho> x)) (dt_saved c 0)),
        lp_itag (sharp \<circ> inp) (lp_data_atom data b))\<in>(dt_constructor_step C U)\<^sup>+"
      unfolding mapped_b by (rule dt_data_constructor_prefix_tail[OF fixed range shapes frames marked psfixed bfixed c dc]) (use False success in auto)
    show ?thesis by (rule trancl_trans[OF r_into_trancl[OF first] rest])
  qed
qed

end
end
