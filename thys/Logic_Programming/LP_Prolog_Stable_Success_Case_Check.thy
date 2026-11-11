theory LP_Prolog_Stable_Success_Case_Check
 imports LP_Prolog_Stable_Success_Case_Expansion
begin

fun lpp_success_case_guard_allowed where
 "lpp_success_case_guard_allowed gs (LPPSOpaque t) = True"
| "lpp_success_case_guard_allowed gs g = (g\<in>set gs)"

fun lpp_success_case_weaken where
 "lpp_success_case_weaken ((h,ps,b,gs),os) ((h',ps',b',gs'),os') =
   (h=h' \<and> b=b' \<and> list_all (\<lambda>p. p\<in>set ps') ps \<and>
    list_all (lpp_success_case_guard_allowed gs') gs \<and>
    list_all (\<lambda>observation. observation\<in>set os') os)"

lemma lpp_success_case_guard_allowed_sound:
 "lpp_success_case_guard_allowed gs g \<Longrightarrow>
   list_all (lpp_success_guard_holds E eta) gs \<Longrightarrow>
   lpp_success_guard_holds E eta g"
 by (cases g) (auto simp: list_all_iff)

lemma lpp_success_case_weaken_sound:
 assumes "lpp_success_case_weaken child parent"
 shows "lpp_stable_observed_calls operation {parent} P \<subseteq>
   lpp_stable_observed_calls operation {child} P"
proof -
 obtain h ps b gs os where parent: "parent=((h,ps,b,gs),os)" by (cases parent) auto
 obtain h' ps' b' gs' os' where child: "child=((h',ps',b',gs'),os')" by (cases child) auto
 show ?thesis using assms
   unfolding parent child lpp_success_case_weaken.simps lpp_stable_observed_calls_def
   by (fastforce simp: list_all_iff dest: lpp_success_case_guard_allowed_sound[unfolded list_all_iff])
qed

fun lpp_check_success_case_step where
 "lpp_check_success_case_step P i k ((h,ps,b,gs),os) children =
  (i<length ps \<and> lpp_context_short k (h#b#ps,gs,os) \<and>
    list_all2 lpp_success_case_weaken children
     (map (lpp_success_case_row k (ps!i) ((h,ps,b,gs),os))
       (filter (\<lambda>(ch,bs,cgs). fst ch=fst (ps!i) \<and> length (snd ch)=length (snd (ps!i))) P)))"

lemma lpp_success_case_list_weaken:
 assumes "list_all2 lpp_success_case_weaken children parents"
 shows "lpp_stable_observed_calls operation (set parents) P \<subseteq>
   lpp_stable_observed_calls operation (set children) P"
 using assms
proof (induct rule: list_all2_induct)
 case Nil
 then show ?case by (simp add: lpp_stable_observed_calls_def)
next
 case (Cons child parent children parents)
 have one: "lpp_stable_observed_calls operation {parent} P \<subseteq>
   lpp_stable_observed_calls operation {child} P"
   by (rule lpp_success_case_weaken_sound[OF Cons.hyps(1)])
 have insert_calls: "lpp_stable_observed_calls operation (insert source_row rows) P =
   lpp_stable_observed_calls operation {source_row} P \<union> lpp_stable_observed_calls operation rows P" for source_row rows
   by (unfold lpp_stable_observed_calls_def; blast)
 show ?case using one Cons.hyps(3)
   by (simp only: list.set insert_calls[of parent "set parents"] insert_calls[of child "set children"]; blast)
qed

lemma lpp_check_success_case_step_sound:
 assumes "lpp_check_success_case_step P i k source_row children"
 shows "lpp_stable_observed_calls operation {source_row} P \<subseteq>
   lpp_stable_observed_calls operation (set children) P"
proof -
 obtain h ps b gs os where source_row: "source_row=((h,ps,b,gs),os)" by (cases source_row) auto
 have index: "i<length ps" and short: "lpp_context_short k (h#b#ps,gs,os)"
   and weaken: "list_all2 lpp_success_case_weaken children
     (map (lpp_success_case_row k (ps!i) ((h,ps,b,gs),os))
       (filter (\<lambda>(ch,bs,cgs). fst ch=fst (ps!i) \<and> length (snd ch)=length (snd (ps!i))) P))"
   using assms by (auto simp: source_row)
 show ?thesis unfolding source_row
   by (rule subset_trans[OF lpp_success_case_row_sound[OF nth_mem[OF index] short]
       lpp_success_case_list_weaken[OF weaken]])
qed

ML \<open>
val checked = [@{thm lpp_check_success_case_step_sound}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted successful-helper case checker dependency" else ();
\<close>
end
