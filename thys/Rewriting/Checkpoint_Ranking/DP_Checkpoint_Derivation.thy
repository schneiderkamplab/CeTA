theory DP_Checkpoint_Derivation
 imports DP_Checkpoint_Fact_Return
begin

text \<open>Sequential derivations expose every successful-return dependency.
The step checker sees only facts established earlier in the same alternative.
A certificate cannot initialize a fact by referring to itself or a later step.\<close>
fun check_checkpoint_derivation where
 "check_checkpoint_derivation checker known [] = True"
| "check_checkpoint_derivation checker known ((w,claim)#rest) =
 (checker known w claim \<and> check_checkpoint_derivation checker (claim#known) rest)"

definition checkpoint_derived where
 "checkpoint_derived known derivation = rev (map snd derivation) @ known"

lemma checked_checkpoint_derivation:
 assumes sound: "\<And>known w claim. checker known w claim \<Longrightarrow> list_all P known \<Longrightarrow> P claim"
 and checked: "check_checkpoint_derivation checker known derivation"
 and known: "list_all P known"
 shows "list_all P (checkpoint_derived known derivation)"
 using checked known
proof (induct derivation arbitrary: known)
 case Nil then show ?case by (simp add: checkpoint_derived_def)
next
 case (Cons entry rest)
 obtain w claim where entry: "entry=(w,claim)" by (cases entry) auto
 have claim: "P claim" using Cons.prems sound by (auto simp: entry)
 have tail: "list_all P (checkpoint_derived (claim#known) rest)"
  by (rule Cons.hyps) (use Cons.prems claim in \<open>auto simp: entry\<close>)
 show ?case using tail by (simp add: checkpoint_derived_def entry)
qed

definition check_checkpoint_clause_derivation where
 "check_checkpoint_clause_derivation checker antecedents ss derivation after ts =
 (list_all (checkpoint_atom_bounded (length ss)) antecedents \<and>
 list_all (checkpoint_atom_bounded (length ts)) after \<and>
 check_checkpoint_derivation checker (map (\<lambda>a. checkpoint_fact a ss) antecedents) derivation \<and>
 list_all (\<lambda>a. check_checkpoint_fact_copy
 (checkpoint_derived (map (\<lambda>b. checkpoint_fact b ss) antecedents) derivation)
 (checkpoint_fact a ts)) after)"

lemma checked_checkpoint_clause_derivation:
 assumes sound: "\<And>known w claim. checker known w claim \<Longrightarrow>
 list_all (checkpoint_fact_holds C L N Z S R old sigma) known \<Longrightarrow>
 checkpoint_fact_holds C L N Z S R old sigma claim"
 and checked: "check_checkpoint_clause_derivation checker antecedents ss derivation after ts"
 and holds: "checkpoint_clause_holds C L N Z S R old antecedents (map (\<lambda>t. t\<cdot>sigma) ss)"
 shows "checkpoint_clause_holds C L N Z S R old after (map (\<lambda>t. t\<cdot>sigma) ts)"
proof -
 let ?seed = "map (\<lambda>a. checkpoint_fact a ss) antecedents"
 let ?final = "checkpoint_derived ?seed derivation"
 have bounds: "list_all (checkpoint_atom_bounded (length ss)) antecedents"
 "list_all (checkpoint_atom_bounded (length ts)) after"
 and derivation: "check_checkpoint_derivation checker ?seed derivation"
 and copies: "\<And>a. a\<in>set after \<Longrightarrow> check_checkpoint_fact_copy ?final (checkpoint_fact a ts)"
 using checked by (auto simp: check_checkpoint_clause_derivation_def list_all_iff)
 have initial: "list_all (checkpoint_fact_holds C L N Z S R old sigma) ?seed"
 using bounds(1) holds
 by (auto simp: list_all_iff checkpoint_clause_holds_def checkpoint_fact_instance)
 have final: "list_all (checkpoint_fact_holds C L N Z S R old sigma) ?final"
 by (rule checked_checkpoint_derivation[OF sound derivation initial])
 have result: "\<And>a. a\<in>set after \<Longrightarrow>
 checkpoint_atom_holds C L N Z S R old a (map (\<lambda>t. t\<cdot>sigma) ts)"
 proof -
  fix a assume member: "a\<in>set after"
  have claim: "checkpoint_fact_holds C L N Z S R old sigma (checkpoint_fact a ts)"
   by (rule checked_checkpoint_fact_copy[OF copies[OF member] final])
  have bound: "checkpoint_atom_bounded (length ts) a" using member bounds(2) by (simp add: list_all_iff)
  show "checkpoint_atom_holds C L N Z S R old a (map (\<lambda>t. t\<cdot>sigma) ts)"
   using claim by (simp add: checkpoint_fact_instance[OF bound])
 qed
 show ?thesis using result bounds(2) by (auto simp: checkpoint_clause_holds_def list_all_iff)
qed

ML \<open>
val thms = @{thms checked_checkpoint_derivation checked_checkpoint_clause_derivation};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted sequential derivation checker" else ();
\<close>
end
