theory LP_Cut_Failed_Clause_Sequence
 imports LP_Cut_Control
begin

text \<open>Compose checked failures without losing the active continuation or
changing the saved alternative stack. The relation is a parameter, permitting
both ordinary LP-with-cut and Prolog source instantiations.\<close>

lemma lpc_failed_clause_sequence:
 assumes failed: "\<And>d saved. d\<in>set earlier \<Longrightarrow>
   (LPCClause goals d mark#saved,saved)\<in>R\<^sup>+"
 shows "(map (\<lambda>d. LPCClause goals d mark) earlier @ es,es)\<in>R\<^sup>*"
 using failed
proof (induct earlier)
 case Nil show ?case by simp
next
 case (Cons d earlier)
 have head: "(LPCClause goals d mark#(map (\<lambda>d. LPCClause goals d mark) earlier @ es),
     map (\<lambda>d. LPCClause goals d mark) earlier @ es)\<in>R\<^sup>+"
   by (rule Cons.prems) simp
 have tail: "(map (\<lambda>d. LPCClause goals d mark) earlier @ es,es)\<in>R\<^sup>*"
   by (rule Cons.hyps) (use Cons.prems in auto)
 show ?case using rtrancl_trans[OF trancl_into_rtrancl[OF head] tail] by simp
qed
end
