theory LP_Prolog_Reified_Structure
 imports LP_Prolog_Structural_Univ
begin

text \<open>Constructor labels are data. A fixed node/list vocabulary handles
arbitrary labels and arities without enumerating the source signature. Only
previously justified finite structural observations may enter this encoding.\<close>

datatype 'f lpp_structure_symbol = LPPStructureLeaf | LPPStructureNode
 | LPPStructureNil | LPPStructureCons | LPPStructureLabel 'f | LPPStructureArguments

fun lpp_reified_spine where
 "lpp_reified_spine [] = Fun LPPStructureNil []"
| "lpp_reified_spine (t#ts) = Fun LPPStructureCons [t,lpp_reified_spine ts]"

fun lpp_reify_structure :: "('f + unit,'v) term \<Rightarrow> ('f lpp_structure_symbol,'v) term" where
 "lpp_reify_structure (Var x) = Var x"
| "lpp_reify_structure (Fun (Inr u) ts) = Fun LPPStructureLeaf []"
| "lpp_reify_structure (Fun (Inl f) ts) =
    Fun LPPStructureNode [Fun (LPPStructureLabel f) [],lpp_reified_spine (map lpp_reify_structure ts)]"

fun lpp_reified_arguments where
 "lpp_reified_arguments [] = Fun LPPStructureNode
   [Fun (LPPStructureLabel (LPCUser ''0:prolog_data_5b5d'')) [],lpp_reified_spine []]"
| "lpp_reified_arguments (t#ts) = Fun LPPStructureNode
   [Fun (LPPStructureLabel (LPCUser ''2:prolog_data_2e'')) [],
    lpp_reified_spine [t,lpp_reified_arguments ts]]"

lemma lpp_reify_argument_list:
 "lpp_reify_structure (lpp_structural_argument_list ts) =
   lpp_reified_arguments (map lpp_reify_structure ts)"
 by (induct ts) auto

definition lpp_reified_argument_rules ::
 "((string lp_cut_symbol) lpp_structure_symbol,nat) trs" where
 "lpp_reified_argument_rules = {
  (Fun LPPStructureArguments [lpp_reified_spine []],lpp_reified_arguments []),
  (Fun LPPStructureArguments [Fun LPPStructureCons [Var 0,Var 1]],
   Fun LPPStructureNode [Fun (LPPStructureLabel (LPCUser ''2:prolog_data_2e'')) [],
    lpp_reified_spine [Var 0,Fun LPPStructureArguments [Var 1]]])}"

lemma lpp_reified_argument_conversion:
 "(Fun LPPStructureArguments [lpp_reified_spine ts],lpp_reified_arguments ts)
   \<in> (Trs.rstep lpp_reified_argument_rules)\<^sup>*"
proof (induction ts)
 case Nil
 have step: "(Fun LPPStructureArguments [lpp_reified_spine []],lpp_reified_arguments [])
   \<in> Trs.rstep lpp_reified_argument_rules"
  by (rule rstep_rule) (simp add: lpp_reified_argument_rules_def)
 show ?case by (rule r_into_rtrancl[OF step])
next
 case (Cons t ts)
 let ?C = "More LPPStructureNode [Fun (LPPStructureLabel (LPCUser ''2:prolog_data_2e'')) []]
   (More LPPStructureCons [t] (More LPPStructureCons [] Hole [Fun LPPStructureNil []]) []) []"
 let ?subst = "\<lambda>x. if x=0 then t else lpp_reified_spine ts"
 have rule: "(Fun LPPStructureArguments [Fun LPPStructureCons [Var 0,Var 1]],
   Fun LPPStructureNode [Fun (LPPStructureLabel (LPCUser ''2:prolog_data_2e'')) [],
    lpp_reified_spine [Var 0,Fun LPPStructureArguments [Var 1]]]) \<in> lpp_reified_argument_rules"
  by (simp add: lpp_reified_argument_rules_def)
 have step: "(Fun LPPStructureArguments [lpp_reified_spine (t#ts)],
   ?C\<langle>Fun LPPStructureArguments [lpp_reified_spine ts]\<rangle>) \<in> Trs.rstep lpp_reified_argument_rules"
  using rstep_subst[OF rstep_rule[OF rule], of ?subst] by simp
 have tail: "(?C\<langle>Fun LPPStructureArguments [lpp_reified_spine ts]\<rangle>,
    ?C\<langle>lpp_reified_arguments ts\<rangle>) \<in> (Trs.rstep lpp_reified_argument_rules)\<^sup>*"
  by (rule ctxt.closedD[OF ctxt_closed_rsteps Cons.IH])
 show ?case using rtrancl_trans[OF r_into_rtrancl[OF step] tail] by simp
qed

definition lpp_reified_observation where
 "lpp_reified_observation t = map_term id (\<lambda>_. 0::nat) (lpp_reify_structure t)"

lemma lpp_reified_spine_map:
 "map_term id rename (lpp_reified_spine ts) = lpp_reified_spine (map (map_term id rename) ts)"
 by (induct ts) auto

lemma lpp_reified_arguments_map:
 "map_term id rename (lpp_reified_arguments ts) = lpp_reified_arguments (map (map_term id rename) ts)"
 by (induct ts) auto

theorem lpp_actual_univ_reified_conversion:
 assumes actual: "lpp_constructor_arguments value f arguments"
 and node: "lpp_runtime_structure value node_structure"
 and argument_shape: "lpp_runtime_structure arguments arguments_structure"
 shows "\<exists>children. lpp_reified_observation node_structure =
   Fun LPPStructureNode [Fun (LPPStructureLabel f) [],lpp_reified_spine children] \<and>
   (Fun LPPStructureArguments [lpp_reified_spine children],lpp_reified_observation arguments_structure)
    \<in> (Trs.rstep lpp_reified_argument_rules)\<^sup>*"
proof -
 have relation: "lpp_structural_univ node_structure f arguments_structure"
  by (rule lpp_constructor_arguments_structural_univ[OF actual node argument_shape])
 obtain ts where shape: "node_structure=Fun (Inl f) ts"
 and argument_shape: "arguments_structure=lpp_structural_argument_list ts"
  using relation by (cases "(node_structure,f,arguments_structure)" rule: lpp_structural_univ.cases) auto
 let ?children = "map (\<lambda>t. map_term id (\<lambda>_. 0::nat) (lpp_reify_structure t)) ts"
 have converted: "lpp_reified_observation arguments_structure=lpp_reified_arguments ?children"
  by (simp add: argument_shape lpp_reified_observation_def lpp_reify_argument_list lpp_reified_arguments_map map_map o_def)
 show ?thesis
  by (rule exI[of _ ?children])
    (simp add: shape lpp_reified_observation_def lpp_reified_spine_map map_map o_def
      argument_shape lpp_reify_argument_list lpp_reified_arguments_map lpp_reified_argument_conversion)
qed

lemma lpp_reified_spine_substitution:
 "lpp_reified_spine ts \<cdot> theta = lpp_reified_spine (map (\<lambda>t. t \<cdot> theta) ts)"
 by (induct ts) auto

lemma lpp_reify_structure_substitution:
 "lpp_reify_structure (t \<cdot> theta) =
   lpp_reify_structure t \<cdot> (lpp_reify_structure \<circ> theta)"
proof (induct t)
 case (Var x) then show ?case by simp
next
 case (Fun f ts)
 have mapped: "map (\<lambda>t. lpp_reify_structure (t \<cdot> theta)) ts =
    map (\<lambda>t. lpp_reify_structure t \<cdot> (lpp_reify_structure \<circ> theta)) ts"
  by (rule map_cong) (use Fun.hyps in auto)
 show ?case by (cases f)
  (simp_all add: lpp_reified_spine_substitution map_map o_def mapped[simplified o_def])
qed

lemma lpp_reified_structural_equation:
 assumes equation: "s \<cdot> eta = t \<cdot> eta_next"
 shows "lpp_reify_structure s \<cdot> (lpp_reify_structure \<circ> eta) =
   lpp_reify_structure t \<cdot> (lpp_reify_structure \<circ> eta_next)"
 using arg_cong[OF equation, of lpp_reify_structure]
 by (simp add: lpp_reify_structure_substitution)

ML \<open>
val checked = @{thms lpp_reify_argument_list lpp_reified_argument_conversion
 lpp_reified_spine_map lpp_reified_arguments_map lpp_actual_univ_reified_conversion
 lpp_reified_spine_substitution lpp_reify_structure_substitution lpp_reified_structural_equation};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted reified structural conversion" else ();
\<close>
end
