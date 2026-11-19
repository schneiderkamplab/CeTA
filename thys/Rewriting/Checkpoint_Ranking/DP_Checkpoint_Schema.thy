theory DP_Checkpoint_Schema
 imports DP_Checkpoint_Summary
begin

type_synonym ('f,'v) checkpoint_schema_witness = "(nat \<times> ('f,'v) term list) option"

fun check_checkpoint_schema_rule where
 "check_checkpoint_schema_rule restricted schemas (l,r) None =
   (case l of Var x \<Rightarrow> False | Fun f ts \<Rightarrow> f\<notin>restricted)"
| "check_checkpoint_schema_rule restricted schemas (l,r) (Some (i,images)) =
   (i<length schemas \<and>
    (let (a,b)=schemas!i in
      vars_term a \<union> vars_term b \<subseteq> {..<length images} \<and>
      l=a\<cdot>(nth images) \<and> r=b\<cdot>(nth images)))"

lemma checkpoint_schema_rule_sound:
 fixes A :: "'f \<Rightarrow> ('f,unit) term list \<Rightarrow> 'a set list \<Rightarrow> 'a set"
 and schemas :: "('f,nat) rule list" and sigma :: "'v \<Rightarrow> ('f,'v) term"
 assumes schemas: "\<And>a b tau. (a,b)\<in>set schemas \<Longrightarrow>
   checkpoint_interpret C A (b\<cdot>(tau::nat \<Rightarrow> ('f,'v) term)) \<subseteq> checkpoint_interpret C A (a\<cdot>tau)"
 and unrestricted: "\<And>f ts. f\<notin>restricted \<Longrightarrow> checkpoint_interpret C A (Fun f (ts::('f,'v) term list))=UNIV"
 and checked: "check_checkpoint_schema_rule restricted schemas (l,r) witness"
 shows "checkpoint_interpret C A (r\<cdot>sigma) \<subseteq> checkpoint_interpret C A (l\<cdot>sigma)"
proof (cases witness)
 case None
 then obtain f ts where l: "l=Fun f ts" and f: "f\<notin>restricted"
  using checked by (cases l) auto
 have lhs: "checkpoint_interpret C A (l\<cdot>sigma)=UNIV"
  using unrestricted[OF f, of "map (\<lambda>x. x\<cdot>sigma) ts"] by (simp only: l eval_term.simps)
 show ?thesis by (simp only: lhs subset_UNIV)
next
 case (Some p)
 obtain i images where p: "p=(i,images)" by (cases p) auto
 obtain a b where ab: "schemas!i=(a,b)" by (cases "schemas!i") auto
 have bound: "i<length schemas" and l: "l=a\<cdot>(nth images)" and r: "r=b\<cdot>(nth images)"
  using checked by (simp_all add: Some p ab Let_def)
 have rule: "(a,b)\<in>set schemas" using nth_mem[OF bound] ab by simp
 have "checkpoint_interpret C A (b\<cdot>((nth images)\<circ>\<^sub>s sigma)) \<subseteq>
       checkpoint_interpret C A (a\<cdot>((nth images)\<circ>\<^sub>s sigma))"
  by (rule schemas[OF rule])
 then show ?thesis by (simp add: l r)
qed

lemma checkpoint_schema_table_sound:
 fixes A :: "'f \<Rightarrow> ('f,unit) term list \<Rightarrow> 'a set list \<Rightarrow> 'a set"
 and schemas :: "('f,nat) rule list" and sigma :: "'v \<Rightarrow> ('f,'v) term"
 assumes schemas: "\<And>a b tau. (a,b)\<in>set schemas \<Longrightarrow>
   checkpoint_interpret C A (b\<cdot>(tau::nat \<Rightarrow> ('f,'v) term)) \<subseteq> checkpoint_interpret C A (a\<cdot>tau)"
 and unrestricted: "\<And>f ts. f\<notin>restricted \<Longrightarrow> checkpoint_interpret C A (Fun f (ts::('f,'v) term list))=UNIV"
 and checked: "list_all2 (check_checkpoint_schema_rule restricted schemas) rules witnesses"
 and member: "(l,r)\<in>set rules"
 shows "checkpoint_interpret C A (r\<cdot>sigma) \<subseteq> checkpoint_interpret C A (l\<cdot>sigma)"
proof -
 obtain i where i: "i<length rules" and pair: "rules!i=(l,r)" using member by (meson in_set_conv_nth)
 have local: "check_checkpoint_schema_rule restricted schemas (l,r) (witnesses!i)"
  using list_all2_nthD[OF checked i] by (simp add: pair)
 show ?thesis by (rule checkpoint_schema_rule_sound[OF schemas unrestricted local])
qed

ML \<open>
val checked = @{thms checkpoint_schema_rule_sound checkpoint_schema_table_sound};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted residual schema checker" else ();
\<close>
end
