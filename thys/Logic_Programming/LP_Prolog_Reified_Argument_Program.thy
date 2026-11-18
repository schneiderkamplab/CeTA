theory LP_Prolog_Reified_Argument_Program
 imports LP_Prolog_Reified_Structure LP_Dependency_Triples
begin

text \<open>The relational residual uses the shared LP answer semantics. Its
successful output stays in the prefix and is shared with the continuation.
This avoids interpreting fresh LP output variables as unrestricted TRS data.\<close>

definition lpp_reified_argument_program ::
 "string lp_cut_symbol lpp_structure_symbol \<Rightarrow>
   (string lp_cut_symbol lpp_structure_symbol,nat) lp_clause list" where
 "lpp_reified_argument_program predicate = [
  ((predicate,[lpp_reified_spine [],lpp_reified_arguments []]),[]),
  ((predicate,[Fun LPPStructureCons [Var 0,Var 1],
    Fun LPPStructureNode [Fun (LPPStructureLabel (LPCUser ''2:prolog_data_2e'')) [],
     lpp_reified_spine [Var 0,Var 2]]]),[(predicate,[Var 1,Var 2])])]"

lemma lpp_reified_argument_program_success:
 "(([lp_atom_eval (predicate,[lpp_reified_spine ts,lpp_reified_arguments ts]) LPIVar],env),([],env))
   \<in> (lp_seg_answer_step (lpp_reified_argument_program predicate))\<^sup>*"
proof (induction ts)
 case Nil
 have step: "(([lp_atom_eval (predicate,[lpp_reified_spine [],lpp_reified_arguments []]) LPIVar],env),([],env))
    \<in> lp_seg_answer_step (lpp_reified_argument_program predicate)"
  using lp_seg_answer_step.resolve[where P="lpp_reified_argument_program predicate" and c=0
    and a="lp_atom_eval (predicate,[lpp_reified_spine [],lpp_reified_arguments []]) LPIVar"
    and \<sigma>=LPIVar and \<nu>="\<lambda>_. env undefined" and gs="[]" and \<rho>=env]
  by (simp add: lpp_reified_argument_program_def lp_atom_eval_def lp_iatom_subst_def)
 show ?case by (rule r_into_rtrancl[OF step])
next
 case (Cons t ts)
 let ?nu = "\<lambda>n. if n=0 then lp_ieval t LPIVar else
   if n=1 then lp_ieval (lpp_reified_spine ts) LPIVar else lp_ieval (lpp_reified_arguments ts) LPIVar"
 have step: "(([lp_atom_eval (predicate,[lpp_reified_spine (t#ts),lpp_reified_arguments (t#ts)]) LPIVar],env),
    ([lp_atom_eval (predicate,[lpp_reified_spine ts,lpp_reified_arguments ts]) LPIVar],env))
    \<in> lp_seg_answer_step (lpp_reified_argument_program predicate)"
  using lp_seg_answer_step.resolve[where P="lpp_reified_argument_program predicate" and c=1
    and a="lp_atom_eval (predicate,[lpp_reified_spine (t#ts),lpp_reified_arguments (t#ts)]) LPIVar"
    and \<sigma>=LPIVar and \<nu>="?nu" and gs="[]" and \<rho>=env]
  by (simp add: lpp_reified_argument_program_def lp_atom_eval_def lp_iatom_subst_def)
 show ?case by (rule rtrancl_trans[OF r_into_rtrancl[OF step] Cons.IH])
qed

ML \<open>
val checked = @{thms lpp_reified_argument_program_success};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted relational argument conversion" else ();
\<close>
end
