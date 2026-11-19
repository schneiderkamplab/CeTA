theory DP_Checkpoint_Fact
 imports DP_Checkpoint_Annotation
begin

text \<open>Rule-local facts contain terms from the unchanged pair. Their
variables are interpreted by one common substitution. Canonical coordinates
make syntactic equality an executable, sufficient implication check.\<close>
primrec checkpoint_fact where
 "checkpoint_fact (CP_Exact i) ts = (CP_Exact 0,[ts!i])"
| "checkpoint_fact (CP_Split i j) ts = (CP_Split 0 1,[ts!i,ts!j])"
| "checkpoint_fact (CP_Prefix i) ts = (CP_Prefix 0,[ts!i])"
| "checkpoint_fact (CP_Strict i) ts = (CP_Strict 0,[ts!i])"
| "checkpoint_fact (CP_Guard i) ts = (CP_Guard 0,[ts!i])"
| "checkpoint_fact (CP_Arguments f i) ts = (CP_Arguments f 0,[ts!i])"
| "checkpoint_fact (CP_Ground f i j) ts = (CP_Ground f 0 1,[ts!i,ts!j])"
| "checkpoint_fact (CP_List f i j) ts = (CP_List f 0 1,[ts!i,ts!j])"

definition checkpoint_fact_holds where
 "checkpoint_fact_holds C L N Z S R old sigma claim =
 checkpoint_atom_holds C L N Z S R old (fst claim) (map (\<lambda>t. t\<cdot>sigma) (snd claim))"

lemma checkpoint_fact_instance:
 assumes bound: "checkpoint_atom_bounded (length ts) atom"
 shows "checkpoint_fact_holds C L N Z S R old sigma (checkpoint_fact atom ts) =
 checkpoint_atom_holds C L N Z S R old atom (map (\<lambda>t. t\<cdot>sigma) ts)"
 using bound by (cases atom) (simp_all add: checkpoint_fact_holds_def checkpoint_atom_bounded_def)

definition check_checkpoint_fact_copy where
 "check_checkpoint_fact_copy known claim = (claim\<in>set known)"

lemma checked_checkpoint_fact_copy:
 assumes copy: "check_checkpoint_fact_copy known claim"
 and known: "list_all (checkpoint_fact_holds C L N Z S R old sigma) known"
 shows "checkpoint_fact_holds C L N Z S R old sigma claim"
 using assms by (auto simp: check_checkpoint_fact_copy_def list_all_iff)

definition check_checkpoint_clause_copy where
 "check_checkpoint_clause_copy antecedents ss after ts =
 (list_all (checkpoint_atom_bounded (length ss)) antecedents \<and>
 list_all (checkpoint_atom_bounded (length ts)) after \<and>
 list_all (\<lambda>a. check_checkpoint_fact_copy (map (\<lambda>b. checkpoint_fact b ss) antecedents)
 (checkpoint_fact a ts)) after)"

lemma checked_checkpoint_clause_copy:
 assumes checked: "check_checkpoint_clause_copy antecedents ss after ts"
 and holds: "checkpoint_clause_holds C L N Z S R old antecedents (map (\<lambda>t. t\<cdot>sigma) ss)"
 shows "checkpoint_clause_holds C L N Z S R old after (map (\<lambda>t. t\<cdot>sigma) ts)"
proof -
 have bounds: "list_all (checkpoint_atom_bounded (length ss)) antecedents"
 "list_all (checkpoint_atom_bounded (length ts)) after"
 and copies: "\<And>a. a\<in>set after \<Longrightarrow>
 check_checkpoint_fact_copy (map (\<lambda>b. checkpoint_fact b ss) antecedents) (checkpoint_fact a ts)"
 using checked by (auto simp: check_checkpoint_clause_copy_def list_all_iff)
 have known: "list_all (checkpoint_fact_holds C L N Z S R old sigma)
 (map (\<lambda>b. checkpoint_fact b ss) antecedents)"
 using bounds(1) holds
 by (auto simp: list_all_iff checkpoint_clause_holds_def checkpoint_fact_instance)
 have result: "\<And>a. a\<in>set after \<Longrightarrow>
 checkpoint_atom_holds C L N Z S R old a (map (\<lambda>t. t\<cdot>sigma) ts)"
 proof -
  fix a assume member: "a\<in>set after"
  have claim: "checkpoint_fact_holds C L N Z S R old sigma (checkpoint_fact a ts)"
   by (rule checked_checkpoint_fact_copy[OF copies[OF member] known])
  have bound: "checkpoint_atom_bounded (length ts) a" using member bounds(2) by (simp add: list_all_iff)
  show "checkpoint_atom_holds C L N Z S R old a (map (\<lambda>t. t\<cdot>sigma) ts)"
   using claim by (simp add: checkpoint_fact_instance[OF bound])
 qed
 show ?thesis using result bounds(2) by (auto simp: checkpoint_clause_holds_def list_all_iff)
qed

ML \<open>
val thms = @{thms checkpoint_fact_instance checked_checkpoint_fact_copy checked_checkpoint_clause_copy};
val _ = if Thm_Deps.has_skip_proof thms orelse not(null(Thm_Deps.all_oracles thms)) then error "Untrusted claim copy checker" else ();
\<close>
end
