theory TRS_Conditional_Witnesses
  imports TRS_Conditional_Ranked CTRS.Conditional_Rewriting_Impl
begin

lemma native_success_correct:
  "native_conditional_success F R (b,s,t) \<Longrightarrow>
    funas_term s \<subseteq> F \<and> funas_term t \<subseteq> F"
  by (erule native_conditional_success.cases)
     (erule native_conditional_inference.cases; auto)

lemma native_reach_refl:
  "funas_term s \<subseteq> F \<Longrightarrow> native_conditional_success F R (True,s,s)"
  by (rule native_conditional_success.conclude[OF native_conditional_inference.reflexive]) simp_all

lemma native_reach_cons:
  assumes a: "native_conditional_success F R (False,s,u)"
    and b: "native_conditional_success F R (True,u,t)"
  shows "native_conditional_success F R (True,s,t)"
proof -
  have inf: "native_conditional_inference F R (True,s,t) [(False,s,u),(True,u,t)]"
    using native_success_correct[OF a] native_success_correct[OF b]
    by (intro native_conditional_inference.transitive) auto
  show ?thesis by (rule native_conditional_success.conclude[OF inf]) (simp add: a b)
qed

lemma native_reach_single:
  "native_conditional_success F R (False,s,t) \<Longrightarrow>
    native_conditional_success F R (True,s,t)"
  by (meson native_reach_cons native_reach_refl native_success_correct)


lemma ranked_cstep_context:
  assumes step: "(s,t) \<in> ranked_cstep F R" and ctx: "funas_ctxt D \<subseteq> F"
  shows "(D\<langle>s\<rangle>,D\<langle>t\<rangle>) \<in> ranked_cstep F R"
proof -
  from step obtain gs where inf: "native_conditional_inference F R (False,s,t) gs"
    and pre: "list_all (native_conditional_success F R) gs"
    unfolding ranked_cstep_def by (auto elim: native_conditional_success.cases)
  from inf obtain l r cs C sigma where mem: "((l,r),cs) \<in> R"
    and eq: "s=C\<langle>l \<cdot> sigma\<rangle>" "t=C\<langle>r \<cdot> sigma\<rangle>"
      "gs=map (\<lambda>(a,b). (True,a \<cdot> sigma,b \<cdot> sigma)) cs"
    and wf: "funas_ctxt C \<subseteq> F" "\<forall>x. funas_term (sigma x) \<subseteq> F"
      "funas_term s \<subseteq> F" "funas_term t \<subseteq> F"
      "\<forall>(a,b)\<in>set cs. funas_term (a \<cdot> sigma) \<subseteq> F \<and> funas_term (b \<cdot> sigma) \<subseteq> F"
    by (cases rule: native_conditional_inference.cases) auto
  have new: "native_conditional_inference F R (False,D\<langle>s\<rangle>,D\<langle>t\<rangle>) gs"
    using native_conditional_inference.apply_rule[OF mem, of "D \<circ>\<^sub>c C" F sigma]
      eq wf ctx by simp
  show ?thesis using native_conditional_success.conclude[OF new pre]
    by (simp add: ranked_cstep_def)
qed

text \<open>The additional finite guard records the declared signature throughout
an existing native proof. Rule references are exact members of the input list;
no variant or signature-extension premise is left to the caller.\<close>
fun ranked_cproof_guard where
  "ranked_cproof_guard F R (Cstep_step ((l,r),cs) p sigma s t pss) =
    (((l,r),cs) \<in> set R \<and>
      funas_ctxt (ctxt_of_pos_term p s) \<subseteq> F \<and>
      (\<forall>x. funas_term (sigma x) \<subseteq> F) \<and>
      funas_term s \<subseteq> F \<and> funas_term t \<subseteq> F \<and>
      (\<forall>(a,b)\<in>set cs. funas_term (a \<cdot> sigma) \<subseteq> F \<and> funas_term (b \<cdot> sigma) \<subseteq> F) \<and>
      list_all (list_all (ranked_cproof_guard F R)) pss)"

lemma native_isOK_unit: "isOK (c :: 'a + unit) \<longleftrightarrow> c = Inr ()"
  by (cases c) auto

lemma ranked_check_cstep_and_csteps:
  fixes R :: "('f::showl,'v::{infinite,showl}) crule list"
  shows "isOK (check_cstep R p) \<Longrightarrow> ranked_cproof_guard F R p \<Longrightarrow>
      native_conditional_success F (set R) (False,cstep_src p,cstep_trg p)"
    and "isOK (check_csteps R s t ps) \<Longrightarrow>
      funas_term s \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow>
      list_all (ranked_cproof_guard F R) ps \<Longrightarrow>
      native_conditional_success F (set R) (True,s,t)"
proof (induct R p and R s t ps rule: check_cstep_check_csteps.induct)
  case (1 R l r cs p sigma s t pss)
  have mem: "((l,r),cs) \<in> set R" and ctxt: "funas_ctxt (ctxt_of_pos_term p s) \<subseteq> F"
    and sub: "\<forall>x. funas_term (sigma x) \<subseteq> F"
    and wf: "funas_term s \<subseteq> F" "funas_term t \<subseteq> F"
    and cswf: "\<forall>(a,b)\<in>set cs. funas_term (a \<cdot> sigma) \<subseteq> F \<and> funas_term (b \<cdot> sigma) \<subseteq> F"
    using "1.prems" by auto
  have src: "s=replace_at s p (l \<cdot> sigma)" and trg: "t=replace_at s p (r \<cdot> sigma)"
    using "1.prems" by (auto simp: check_eq_Inr)
  have pre: "native_conditional_success F (set R) (True,fst (cs!i) \<cdot> sigma,snd (cs!i) \<cdot> sigma)"
    if "i<length cs" for i
    proof -
    have ci: "cs!i \<in> set cs" using that by simp
    have pi: "pss!i \<in> set pss" using that "1.prems" by (auto simp: check_eq_Inr)
    have vok: "isOK (check_variant_in_ctrs R ((l,r),cs))"
      and len: "length pss=length cs"
      and checked: "isOK (check_csteps R (fst (cs!i) \<cdot> sigma) (snd (cs!i) \<cdot> sigma) (pss!i))"
      using "1.prems" that by (auto simp: check_eq_Inr)
    have veq: "check_variant_in_ctrs R ((l,r),cs)=Inr ()"
      using vok by (cases "check_variant_in_ctrs R ((l,r),cs)") auto
    have ends: "funas_term (fst (cs!i) \<cdot> sigma) \<subseteq> F"
      "funas_term (snd (cs!i) \<cdot> sigma) \<subseteq> F"
      using cswf ci by (cases "cs!i"; auto)+
    have guards: "list_all (ranked_cproof_guard F R) (pss!i)"
      using "1.prems" pi by (auto simp: list_all_iff)
    show ?thesis using "1.hyps" veq len src trg that checked ends guards by (auto simp: check_eq_Inr)
  qed
  have pres: "list_all (native_conditional_success F (set R))
    (map (\<lambda>(a,b). (True,a \<cdot> sigma,b \<cdot> sigma)) cs)"
    using pre by (auto simp: list_all_iff in_set_conv_nth; metis fst_conv snd_conv)
  have inf: "native_conditional_inference F (set R) (False,s,t)
    (map (\<lambda>(a,b). (True,a \<cdot> sigma,b \<cdot> sigma)) cs)"
    using native_conditional_inference.apply_rule[OF mem ctxt sub] src trg wf cswf by simp
  show ?case using native_conditional_success.conclude[OF inf pres] by simp
next
  case (2 R s t)
  then show ?case by (auto intro: native_reach_refl)
next
  case (3 R s t p)
  have src: "cstep_src p=s" and trg: "cstep_trg p=t"
    and checked: "isOK (check_cstep R p)" and guard: "ranked_cproof_guard F R p"
    using "3.prems" by auto
  have "native_conditional_success F (set R) (False,s,t)"
    using "3.hyps" checked guard src trg by (auto simp: check_eq_Inr)
  then show ?case by (rule native_reach_single)
next
  case (4 R s t p v va)
  have src: "cstep_src p=s" and checked: "isOK (check_cstep R p)"
    and rest: "isOK (check_csteps R (cstep_trg p) t (v#va))"
    and guard: "ranked_cproof_guard F R p"
    and guards: "list_all (ranked_cproof_guard F R) (v#va)"
    using "4.prems" by auto
  have first: "native_conditional_success F (set R) (False,s,cstep_trg p)"
    using "4.hyps"(1) checked guard src by (auto simp: check_eq_Inr)
  have wf: "funas_term (cstep_trg p) \<subseteq> F"
    using native_success_correct[OF first] by simp
  have eq: "check_cstep R p=Inr ()" using checked native_isOK_unit by blast
  have last: "native_conditional_success F (set R) (True,cstep_trg p,t)"
    using "4.hyps"(2) src eq rest wf guards "4.prems" by (auto simp: check_eq_Inr)
  show ?case by (rule native_reach_cons[OF first last])
qed
end
