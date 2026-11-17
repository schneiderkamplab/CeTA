theory LP_Prolog_Spine_Shape
 imports LP_Prolog_Spine_Context LP_Prolog_Functor_Shape_Context
begin

lemma lpp_list_length_return_shape:
 "lpp_list_length t n \<Longrightarrow>
   lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) t"
proof (induct rule: lpp_list_length.induct)
 case nil
 show ?case by (rule lp_return_shape_holds.node[where shapes="[]"])
   (simp_all add: lpp_spine_grammar_def)
next
 case (cons t n h)
 show ?case by (rule lp_return_shape_holds.node[where shapes="[LPReturnAny,LPReturnShape 0]"])
   (use cons in \<open>auto simp: lpp_spine_grammar_def less_Suc_eq_0_disj
     intro: lp_return_shape_holds.any\<close>)
qed

lemma lpp_return_shape_list_length:
 assumes shape: "lp_return_shape_holds lpp_spine_grammar descriptor t"
 shows "descriptor=LPReturnShape 0 \<Longrightarrow> \<exists>n. lpp_list_length t n"
 using shape
proof (induct rule: lp_return_shape_holds.induct)
 case (any t) then show ?case by simp
next
 case (ground t) then show ?case by simp
next
 case (node i f shapes ts)
 then have index: "i=0" by simp
 have alternatives: "(f,shapes)=(LPCUser ''0:prolog_data_5b5d'',[]) \<or>
   (f,shapes)=(LPCUser ''2:prolog_data_2e'',[LPReturnAny,LPReturnShape 0])"
   using node.hyps index by (simp add: lpp_spine_grammar_def)
 show ?case
 proof (cases "shapes=[]")
  case True
  then have "ts=[]" "f=LPCUser ''0:prolog_data_5b5d''" using node.hyps alternatives by auto
  then show ?thesis by (auto intro: exI[of _ 0] lpp_list_length.intros)
 next
  case False
  then have fields: "shapes=[LPReturnAny,LPReturnShape 0]" "f=LPCUser ''2:prolog_data_2e''"
    using alternatives by auto
  have len: "length ts=2" using node.hyps fields by auto
  obtain h rest where first: "ts=h#rest" "length rest=1" using len by (cases ts) auto
  obtain tail_term where rest: "rest=[tail_term]" using first(2) by (cases rest) auto
  have ts: "ts=[h,tail_term]" using first rest by simp
  obtain n where tail: "lpp_list_length tail_term n"
    using node.hyps(5)[of 1] fields ts by auto
  show ?thesis using lpp_list_length.cons[OF tail, of h] by (auto simp: fields ts)
 qed
qed

lemma lpp_spine_shape_exact:
 "lpp_spine_holds eta t =
   lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lp_ieval t eta)"
 unfolding lpp_spine_holds_def
 using lpp_list_length_return_shape lpp_return_shape_list_length by blast


lemma lpp_actual_return_spine_shapes:
 assumes actual: "lp_actual_answer (lpp_domain_answers P B U D) ss eta"
 and initialized: "list_all (\<lambda>frame. list_all (\<lambda>t.
   lp_return_shape_holds lpp_spine_grammar (LPReturnShape 0) (lp_ieval t (snd frame))) spines) ss"
 shows "list_all (\<lambda>t. lp_return_shape_holds lpp_spine_grammar
   (LPReturnShape 0) (lp_ieval t eta)) spines"
proof -
 have init: "list_all (\<lambda>frame. list_all (lpp_spine_holds (snd frame)) spines) ss"
   using initialized by (auto simp: list_all_iff lpp_spine_shape_exact)
 show ?thesis using lpp_actual_return_preserves_spine_context[OF actual init]
   by (auto simp: list_all_iff lpp_spine_shape_exact)
qed

ML \<open>
val checked = @{thms lpp_spine_shape_exact lpp_functor_argument_return_shape lpp_actual_return_spine_shapes};
val oracles = map (fst o fst) o Thm_Deps.all_oracles;
val inherited = oracles [@{thm check_trs_termination_proof}];
val _ = if Thm_Deps.has_skip_proof checked orelse
 exists (fn n => not (member (op =) inherited n)) (oracles checked)
 then error "Untrusted spine shape bridge" else ();
\<close>
end
