theory LP_Dependency_Triple_Simulation
  imports LP_Dependency_Triple_Success
begin

context lp_triple_translation
begin

definition dt_strict where
  "dt_strict = {(lp_ieval l \<rho>,lp_ieval r \<rho>) | l r \<rho>. (l,r)\<in>set dt_pairs}"

definition dt_step where
  "dt_step = (lp_pi_link (set dt_support))\<^sup>* O dt_strict O
    (lp_pi_link (set dt_support))\<^sup>*"

lemma dt_control_instance:
  assumes rule: "(l,r)\<in>set dt_control"
  shows "(lp_ieval (lp_mark sharp l) \<rho>,lp_ieval (lp_mark sharp r) \<rho>)\<in>dt_strict"
proof -
  have pair: "(lp_mark sharp l,lp_mark sharp r)\<in>set dt_pairs"
    using rule unfolding dt_pairs_def by force
  show ?thesis unfolding dt_strict_def using pair by blast
qed

lemma dt_control_instance_pair:
  "p\<in>set dt_control \<Longrightarrow>
    (lp_ieval (lp_mark sharp (fst p)) \<rho>,lp_ieval (lp_mark sharp (snd p)) \<rho>)\<in>dt_strict"
  by (cases p) (auto intro: dt_control_instance)

lemma dt_stepI:
  assumes before: "(s,l)\<in>(lp_pi_link (set dt_support))\<^sup>*"
    and strict: "(l,r)\<in>dt_strict"
    and after: "(r,t)\<in>(lp_pi_link (set dt_support))\<^sup>*"
  shows "(s,t)\<in>dt_step"
  using assms by (auto simp: dt_step_def)

lemma dt_prefix_tail:
  assumes c: "c<length D" and triple: "D!c=(h,ps,b)"
    and i: "i<length ps"
    and success: "((map (\<lambda>g. lp_atom_eval g \<rho>) (drop i ps),\<rho>),([],\<eta>))
      \<in>(lp_seg_answer_step P)\<^sup>*"
  shows "(LPIFun (sharp (du c i))
      (lp_itag inp (lp_atom_eval (ps!i) \<rho>) # map \<rho> (dt_saved c i)),
      lp_itag (sharp \<circ> inp) (lp_atom_eval b \<eta>))\<in>dt_step\<^sup>+"
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
  have weak: "(LPIFun (sharp (du c i))
      (lp_itag inp (lp_atom_eval (ps!i) \<rho>) # map \<rho> (dt_saved c i)),
      LPIFun (sharp (du c i))
      (lp_itag out (lp_atom_eval (ps!i) \<mu>) # map \<mu> (dt_saved c i)))
      \<in>(lp_pi_link (set dt_support))\<^sup>*"
    unfolding dt_support_def by (rule lp_translation.lp_triple_success_capture[OF head])
  have member: "dt_return c i\<in>set dt_control"
    by (rule dt_return_member[OF c]) (use triple less.prems(1) in simp)
  show ?case
  proof (cases "Suc i < length ps")
    case True
    have strict: "(LPIFun (sharp (du c i))
        (lp_itag out (lp_atom_eval (ps!i) \<mu>) # map \<mu> (dt_saved c i)),
        LPIFun (sharp (du c (Suc i)))
        (lp_itag inp (lp_atom_eval (ps!Suc i) \<mu>) # map \<mu> (dt_saved c (Suc i))))\<in>dt_strict"
      using dt_control_instance_pair[OF member, of \<mu>]
      by (simp add: dt_return_def triple True dt_frame_def lp_itag_eval o_def)
    have first: "(LPIFun (sharp (du c i))
        (lp_itag inp (lp_atom_eval (ps!i) \<rho>) # map \<rho> (dt_saved c i)),
        LPIFun (sharp (du c (Suc i)))
        (lp_itag inp (lp_atom_eval (ps!Suc i) \<mu>) # map \<mu> (dt_saved c (Suc i))))\<in>dt_step"
      by (rule dt_stepI[OF weak strict]) simp
    have continuation: "(LPIFun (sharp (du c (Suc i)))
        (lp_itag inp (lp_atom_eval (ps!Suc i) \<mu>) # map \<mu> (dt_saved c (Suc i))),
        lp_itag (sharp \<circ> inp) (lp_atom_eval b \<eta>))\<in>dt_step\<^sup>+"
      by (rule less.hyps[OF _ True tail]) (use True in simp)
    show ?thesis by (rule trancl_trans[OF r_into_trancl[OF first] continuation])
  next
    case False
    have finished: "drop (Suc i) ps=[]" using False by simp
    have eta: "\<eta>=\<mu>"
      using tail finished by (auto elim: converse_rtranclE lp_seg_answer_step.cases)
    have strict: "(LPIFun (sharp (du c i))
        (lp_itag out (lp_atom_eval (ps!i) \<mu>) # map \<mu> (dt_saved c i)),
        lp_itag (sharp \<circ> inp) (lp_atom_eval b \<eta>))\<in>dt_strict"
      using dt_control_instance_pair[OF member, of \<mu>]
      by (simp add: dt_return_def triple False dt_frame_def lp_itag_eval lp_tag_def o_def eta)
    show ?thesis by (rule r_into_trancl[OF dt_stepI[OF weak strict]]) simp
  qed
qed

theorem dt_call_simulation:
  assumes call: "(a,b)\<in>lp_triple_calls (set D) P"
  shows "(lp_itag (sharp \<circ> inp) a,lp_itag (sharp \<circ> inp) b)\<in>dt_step\<^sup>+"
proof -
  obtain h ps goal \<sigma> \<rho> \<eta> where triple: "(h,ps,goal)\<in>set D"
    and matching: "lp_iatom_subst a \<sigma>=lp_atom_eval h \<rho>"
    and success: "((map (\<lambda>g. lp_atom_eval g \<rho>) ps,\<rho>),([],\<eta>))
      \<in>(lp_seg_answer_step P)\<^sup>*"
    and b: "b=lp_atom_eval goal \<eta>"
    using call unfolding lp_triple_calls_def by blast
  obtain c where c: "c<length D" and dc: "D!c=(h,ps,goal)"
    using triple by (metis in_set_conv_nth)
  have entry: "dt_entry c\<in>set dt_control" by (rule dt_entry_member[OF c])
  have instantiate: "(lp_itag (sharp \<circ> inp) a,
      lp_itag (sharp \<circ> inp) (lp_atom_eval h \<rho>))\<in>lp_pi_link (set dt_support)"
  proof -
    have eq: "lp_itag (sharp \<circ> inp) (lp_atom_eval h \<rho>) =
      lp_isubst (lp_itag (sharp \<circ> inp) a) \<sigma>"
      using matching by (metis lp_itag_subst)
    show ?thesis unfolding lp_pi_link_def using eq by blast
  qed
  show ?thesis
  proof (cases "ps=[]")
    case True
    have eta: "\<eta>=\<rho>"
      using success True by (auto elim: converse_rtranclE lp_seg_answer_step.cases)
    have strict: "(lp_itag (sharp \<circ> inp) (lp_atom_eval h \<rho>),
        lp_itag (sharp \<circ> inp) b)\<in>dt_strict"
      using dt_control_instance_pair[OF entry, of \<rho>]
      by (simp add: dt_entry_def dc True b eta lp_itag_eval lp_tag_def o_def)
    show ?thesis by (rule r_into_trancl[OF dt_stepI[OF r_into_rtrancl[OF instantiate] strict]]) simp
  next
    case False
    have strict: "(lp_itag (sharp \<circ> inp) (lp_atom_eval h \<rho>),
        LPIFun (sharp (du c 0))
        (lp_itag inp (lp_atom_eval (ps!0) \<rho>) # map \<rho> (dt_saved c 0)))\<in>dt_strict"
      using dt_control_instance_pair[OF entry, of \<rho>]
      by (simp add: dt_entry_def dc False dt_frame_def lp_itag_eval lp_tag_def o_def)
    have first: "(lp_itag (sharp \<circ> inp) a,LPIFun (sharp (du c 0))
        (lp_itag inp (lp_atom_eval (ps!0) \<rho>) # map \<rho> (dt_saved c 0)))\<in>dt_step"
      by (rule dt_stepI[OF r_into_rtrancl[OF instantiate] strict]) simp
    have rest: "(LPIFun (sharp (du c 0))
        (lp_itag inp (lp_atom_eval (ps!0) \<rho>) # map \<rho> (dt_saved c 0)),
        lp_itag (sharp \<circ> inp) b)\<in>dt_step\<^sup>+"
      unfolding b by (rule dt_prefix_tail[OF c dc]) (use False success in auto)
    show ?thesis by (rule trancl_trans[OF r_into_trancl[OF first] rest])
  qed
qed

end
end
