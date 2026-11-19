theory Native_Structural_Encoding_Check
 imports Global_Arithmetic_Contract_Check
 "../../thys/Logic_Programming/LP_Prolog_Integer_Encoding"
begin

text \<open>The input label is the shared source's arity-qualified label, not
an unqualified Prolog name. Byte strings are serialized exactly as in the
projection and LP data naming layers. This does not establish that arbitrary
runtime labels satisfy the source parser's signature discipline.\<close>

definition native_structural_data_name :: "string \<Rightarrow> nat \<Rightarrow> string" where
 "native_structural_data_name tag_text arity =
  ''lp_c_'' @ concat (map lpp_hex_char
   (''__prolog_symbol_'' @ concat (map lpp_hex_char
    (char_of_nat 0 # (''prolog.structure.'' @ tag_text))))) @ ''_'' @ show arity"

fun native_source_label :: "string lp_cut_symbol \<Rightarrow> string" where
 "native_source_label (LPCUser s) = s"
| "native_source_label LPCBang = ''0:!''"
| "native_source_label LPCComma = ''2:,''"
| "native_source_label LPCEquals = ''2:=''"
| "native_source_label LPCTruth = ''0:true''"
| "native_source_label LPCFailure = ''0:fail''"
| "native_source_label LPCCallSymbol = ''1:call''"

fun native_structural_symbol :: "(string lp_cut_symbol) lpp_structure_symbol \<Rightarrow> string lp_cut_symbol" where
 "native_structural_symbol LPPStructureLeaf = LPCUser (native_structural_data_name ''leaf'' 0)"
| "native_structural_symbol LPPStructureNode = LPCUser (native_structural_data_name ''node'' 2)"
| "native_structural_symbol LPPStructureNil = LPCUser (native_structural_data_name ''nil'' 0)"
| "native_structural_symbol LPPStructureCons = LPCUser (native_structural_data_name ''cons'' 2)"
| "native_structural_symbol (LPPStructureLabel f) = LPCUser (native_structural_data_name (''label:'' @ native_source_label f) 0)"
| "native_structural_symbol LPPStructureArguments = LPCUser (native_structural_data_name ''arguments'' 1)"

definition native_structural_expression where
 "native_structural_expression t = map_term native_structural_symbol id (lpp_reify_structure t)"

lemma native_structural_expression_substitution:
 "native_structural_expression (t \<cdot> theta) =
  native_structural_expression t \<cdot> (native_structural_expression \<circ> theta)"
proof -
 have transport: "map_term native_structural_symbol id (u \<cdot> sigma) =
   map_term native_structural_symbol id u \<cdot> (\<lambda>x. map_term native_structural_symbol id (sigma x))" for u sigma
  by (induct u) (auto simp: map_map o_def intro!: map_cong)
 show ?thesis unfolding native_structural_expression_def
  by (simp add: lpp_reify_structure_substitution transport o_def)
qed

lemma native_structural_equation:
 assumes "s \<cdot> eta = t \<cdot> eta_next"
 shows "native_structural_expression s \<cdot> (native_structural_expression \<circ> eta) =
  native_structural_expression t \<cdot> (native_structural_expression \<circ> eta_next)"
 using arg_cong[OF assms, of native_structural_expression]
 by (simp add: native_structural_expression_substitution)

lemma native_observation_from_runtime:
 assumes observed: "lpp_runtime_structure runtime_value tree"
 and effect: "lpp_leaf_effect A initial_tree tree"
 shows "observed_leaf_coordinate native_structural_symbol A initial_tree runtime_value
  (lp_ieval (native_structural_expression tree) (\<lambda>_. LPIVar undefined))"
 using assms unfolding observed_leaf_coordinate_def native_structural_expression_def by blast

lemma native_substituted_observation:
 assumes observed: "lpp_runtime_structure runtime_value (tree \<cdot> theta)"
 and effect: "lpp_leaf_effect A initial_tree (tree \<cdot> theta)"
 shows "observed_leaf_coordinate native_structural_symbol A initial_tree runtime_value
  (lp_ieval (native_structural_expression tree \<cdot> (native_structural_expression \<circ> theta)) (\<lambda>_. LPIVar undefined))"
 using native_observation_from_runtime[OF assms]
 by (simp add: native_structural_expression_substitution)


lemma native_evaluated_observation:
 fixes rho :: "'v \<Rightarrow> (string lp_cut_symbol,'w) lp_iterm"
 assumes observed: "\<And>x. x \<in> vars_term t \<Longrightarrow> lpp_runtime_structure (rho x) (eta x)"
 and effect: "lpp_leaf_effect A initial_tree (map_term Inl id t \<cdot> eta)"
 shows "observed_leaf_coordinate native_structural_symbol A initial_tree (lp_ieval t rho)
  (lp_ieval (native_structural_expression (map_term Inl id t) \<cdot>
   (native_structural_expression \<circ> eta)) (\<lambda>_. LPIVar undefined))"
 by (rule native_substituted_observation[OF lpp_structural_projection_eval[OF observed] effect])

lemma native_symbolic_variable_positive:
 "native_structural_expression (Var x) = Var x"
 by (simp add: native_structural_expression_def)

lemma native_symbolic_variable_not_leaf:
 "native_structural_expression (Var x) \<noteq>
  native_structural_expression (Fun (Inr ()) [])"
 by (simp add: native_structural_expression_def)

text \<open>The prior arithmetic/equality theorem now has this explicit
encoding instance. Its runtime representation, incoming observation and caller
continuation premises remain required.\<close>
lemmas native_arithmetic_equality_answer_contract =
 global_arithmetic_equality_answer_contract[where encode=native_structural_symbol]

ML \<open>
val checked = @{thms native_structural_expression_substitution native_structural_equation
 native_observation_from_runtime native_substituted_observation native_evaluated_observation
 native_symbolic_variable_positive native_symbolic_variable_not_leaf
 native_arithmetic_equality_answer_contract};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted native structural encoding" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-native-structural-encoding/kernel-receipt.txt")
 ("Kernel checked; no skipped proofs or oracles. Source signature correspondence and full-family assembly remain open.\n" ^ cat_lines (map (Thm.string_of_thm @{context}) checked));

val symbol_cases = [
 (@{term "LPPStructureLeaf :: (string lp_cut_symbol) lpp_structure_symbol"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f3030373037323666366336663637326537333734373237353633373437353732363532653663363536313636_0"),
 (@{term "LPPStructureNode :: (string lp_cut_symbol) lpp_structure_symbol"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f3030373037323666366336663637326537333734373237353633373437353732363532653665366636343635_2"),
 (@{term "LPPStructureNil :: (string lp_cut_symbol) lpp_structure_symbol"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f303037303732366636633666363732653733373437323735363337343735373236353265366536393663_0"),
 (@{term "LPPStructureCons :: (string lp_cut_symbol) lpp_structure_symbol"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f3030373037323666366336663637326537333734373237353633373437353732363532653633366636653733_2"),
 (@{term "(LPPStructureLabel (LPCUser ''0:prolog_data_5b5d''))"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f303037303732366636633666363732653733373437323735363337343735373236353265366336313632363536633361333033613730373236663663366636373566363436313734363135663335363233353634_0"),
 (@{term "(LPPStructureLabel (LPCUser ''0:prolog_data_766172''))"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f30303730373236663663366636373265373337343732373536333734373537323635326536633631363236353663336133303361373037323666366336663637356636343631373436313566333733363336333133373332_0"),
 (@{term "(LPPStructureLabel (LPCUser ''2:prolog_data_2e''))"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f3030373037323666366336663637326537333734373237353633373437353732363532653663363136323635366333613332336137303732366636633666363735663634363137343631356633323635_0"),
 (@{term "(LPPStructureLabel (LPCUser ''2:prolog_data_2f''))"}, "lp_c_5f5f70726f6c6f675f73796d626f6c5f3030373037323666366336663637326537333734373237353633373437353732363532653663363136323635366333613332336137303732366636633666363735663634363137343631356633323636_0")];
val _ = List.app (fn (symbol, expected) =>
 let val expression = @{term native_structural_symbol} $ symbol;
     val expected_term = @{term "LPCUser :: string => string lp_cut_symbol"} $ HOLogic.mk_string expected;
     val result = Code_Evaluation.dynamic_value @{context} (HOLogic.mk_eq (expression, expected_term));
 in if result = SOME @{term True} then () else error "Native structural name mismatch"
 end) symbol_cases;
val _ = if Code_Evaluation.dynamic_value @{context}
 @{term "native_structural_symbol (LPPStructureLabel (LPCUser ''0:prolog_data_66'')) = native_structural_symbol (LPPStructureLabel (LPCUser ''3:prolog_data_66''))"}
 = SOME @{term False} then () else error "Constructor arity collision";
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-native-structural-encoding/symbol-checks.txt")
 "Eight executable exact-name checks passed against retained original XML names; distinct constructor arities remain distinct. These comparisons are not kernel theorems.\n";
val _ = writeln "NATIVE_STRUCTURAL_ENCODING_KERNEL_CHECKED";
\<close>
end
