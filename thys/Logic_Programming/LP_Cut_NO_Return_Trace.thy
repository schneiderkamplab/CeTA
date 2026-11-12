theory LP_Cut_NO_Return_Trace
 imports LP_Cut_NO_Return_Control LP_Cut_NO_Return_Swap LP_Cut_NO_Return_Unify
begin

text \<open>The existing NO action language is checked against finite answer
rows. Unsupported actions are rejected. Reserved scopes cover the attached
continuation; successful returns cannot be silently traversed.\<close>

fun lpc_no_return_step where
 "lpc_no_return_step fuel P reserved ss LPCNOAdmin tt =
   (lpc_return_admin ss=Some (None,tt))"
| "lpc_no_return_step fuel P reserved ((LPCGoals (LPCAtom (Fun (LPCUser f) call_args)#gs),payload)#saved) (LPCNOCase m) tt =
   (
     m\<notin>set reserved \<and>
     lp_cut_fresh m (LPCGoals (LPCAtom (Fun (LPCUser f) call_args)#gs)#map fst saved) \<and>
     tt=map (\<lambda>c. (LPCClause (LPCAtom (Fun (LPCUser f) call_args)#gs) c m,payload))
       (lp_cut_slice P (LPCUser f) (length call_args)) @ (LPCBarrier m,payload)#saved)"
| "lpc_no_return_step fuel P reserved ((LPCClause (LPCAtom a#gs) c m,payload)#saved) (LPCNOResolve k V images) tt =
     (let sigma=lpc_mgu_substitution V images;
          hs=map (lp_cut_bind m (\<lambda>t. t\<cdot>(\<lambda>v. sigma (lp_prefix k v)))) (snd (P!c)) @
             map (lp_cut_map (\<lambda>t. t\<cdot>sigma)) gs;
          result=map (\<lambda>t. t\<cdot>sigma) payload
      in lpc_no_return_resolve fuel P a gs c m saved payload k V images hs result \<and>
         tt=(LPCGoals hs,result)#saved)"
| "lpc_no_return_step fuel P reserved ((LPCClause (LPCAtom a#gs) c m,payload)#saved) (LPCNOResolveSwap k V images x y) tt =
     (let sigma=lpc_mgu_substitution V images;
          hs=map (lp_cut_bind m (\<lambda>t. (t\<cdot>(\<lambda>v. sigma (lp_prefix k v)))\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) (snd (P!c)) @
             map (lp_cut_map (\<lambda>t. (t\<cdot>sigma)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v)))) gs;
          result=map (\<lambda>t. (t\<cdot>sigma)\<cdot>(\<lambda>v. Var (lpc_no_swap x y v))) payload
      in lpc_no_return_resolve_swap fuel P a gs c m saved payload k V images x y hs result \<and>
         tt=(LPCGoals hs,result)#saved)"
| "lpc_no_return_step fuel P reserved ((LPCGoals (LPCUnify a b#gs),payload)#saved) (LPCNOUnify V images) tt =
   (
     lpc_check_mgu fuel [(a,b)] V images \<and>
     tt=(LPCGoals (map (lp_cut_map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images)) gs),
       map (\<lambda>t. t\<cdot>lpc_mgu_substitution V images) payload)#saved)"
| "lpc_no_return_step fuel P reserved ((LPCClause (LPCAtom a#gs) c m,payload)#saved)
     (LPCNOBacktrack k) tt =
   (c<length P \<and> lp_cut_check_clash fuel k a (fst (P!c)) \<and> tt=saved)"
| "lpc_no_return_step fuel P reserved ((LPCGoals (LPCUnify a b#gs),payload)#saved)
     LPCNOUnifyFail tt =
   (lp_cut_check_equality fuel a b LPCAlwaysFailure \<and> tt=saved)"
| "lpc_no_return_step fuel P reserved ss action tt = False"

lemma lpc_no_return_step_attach_sound:
 assumes checked: "lpc_no_return_step fuel P reserved ss action tt"
   and scopes: "lpc_rest_scopes rest \<subseteq> set reserved"
 shows "lpc_answer_transition P
   (lpc_attach_answers rest (lpc_return_eval LPIVar ss)) None
   (lpc_attach_answers rest (lpc_return_eval LPIVar tt))"
 using checked scopes
 by (induct fuel P reserved ss action tt rule: lpc_no_return_step.induct)
   (auto simp: Let_def intro: lpc_no_return_admin_attach_sound lpc_no_return_case_attach_sound
     lpc_no_return_resolve_attach_sound lpc_no_return_resolve_swap_attach_sound
     lpc_no_return_unify_attach_sound lpc_no_return_backtrack_attach_sound
     lpc_no_return_unify_fail_attach_sound split: list.splits prod.splits lp_cut_entry.splits lp_cut_goal.splits term.splits lp_cut_symbol.splits)

fun lpc_no_return_trace where
 "lpc_no_return_trace fuel P reserved ss [] tt = (ss=tt)"
| "lpc_no_return_trace fuel P reserved ss ((action,uu)#steps) tt =
   (lpc_no_return_step fuel P reserved ss action uu \<and>
    lpc_no_return_trace fuel P reserved uu steps tt)"

lemma lpc_no_return_trace_attach_sound:
 assumes checked: "lpc_no_return_trace fuel P reserved ss steps tt"
   and scopes: "lpc_rest_scopes rest \<subseteq> set reserved"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>(lp_cut_mgu_source P)\<^sup>*"
 using checked
proof (induct steps arbitrary: ss)
 case Nil then show ?case by simp
next
 case (Cons entry steps)
 obtain action uu where entry: "entry=(action,uu)" by (cases entry) auto
 have local_step: "lpc_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpc_no_return_trace fuel P reserved uu steps tt"
   using Cons.prems entry by simp_all
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar ss),
     lpc_attach rest (lpc_return_eval LPIVar uu))\<in>lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF lpc_no_return_step_attach_sound[OF local_step scopes]]
   by (simp add: lpc_attach_answers_erases)
 show ?case using actual Cons.hyps[OF local_tail] by (meson r_into_rtrancl rtrancl_trans)
qed

lemma lpc_no_return_trace_attach_progress:
 assumes checked: "lpc_no_return_trace fuel P reserved ss steps tt"
   and scopes: "lpc_rest_scopes rest \<subseteq> set reserved"
   and nonempty: "steps\<noteq>[]"
 shows "(lpc_attach rest (lpc_return_eval LPIVar ss),
   lpc_attach rest (lpc_return_eval LPIVar tt))\<in>(lp_cut_mgu_source P)\<^sup>+"
proof -
 obtain action uu tail where shape: "steps=(action,uu)#tail"
   using nonempty by (cases steps) auto
 have local_step: "lpc_no_return_step fuel P reserved ss action uu"
   and local_tail: "lpc_no_return_trace fuel P reserved uu tail tt"
   using checked shape by simp_all
 have actual: "(lpc_attach rest (lpc_return_eval LPIVar ss),
     lpc_attach rest (lpc_return_eval LPIVar uu))\<in>lp_cut_mgu_source P"
   using lpc_answer_transition_erases[OF lpc_no_return_step_attach_sound[OF local_step scopes]]
   by (simp add: lpc_attach_answers_erases)
 show ?thesis using actual lpc_no_return_trace_attach_sound[OF local_tail scopes]
   by (rule rtrancl_into_trancl2)
qed

ML \<open>
val checked = [@{thm lpc_no_return_step_attach_sound}, @{thm lpc_no_return_trace_attach_sound},
 @{thm lpc_no_return_trace_attach_progress}];
val _ = if Thm_Deps.has_skip_proof checked orelse not (null (Thm_Deps.all_oracles checked))
 then error "Untrusted return-aware trace dependency" else ();
\<close>
end
