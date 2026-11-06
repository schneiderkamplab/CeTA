theory LP_Cut_Fresh_Head_Controls
  imports LP_Cut_Fresh_Head_Resolution
begin

text \<open>Reusing a caller variable for an otherwise fresh clause-local variable
is not a most-general resolution. The caller continuation and the fresh body
must admit independent subsequent values.\<close>
lemma lpc_captured_body_variable_is_not_mgu:
  "\<not>lpc_mgu_resolve (LPIFun False [LPIVar ''a'']) [LPCAtom (LPIVar ''z'')]
    (Fun False [Var ''h'']) [LPCAtom (Var ''z'')]
    LPIVar (LPIVar(''h'':=LPIVar ''a''))"
proof
  assume bad: "lpc_mgu_resolve (LPIFun False [LPIVar ''a'']) [LPCAtom (LPIVar ''z'')]
    (Fun False [Var ''h'']) [LPCAtom (Var ''z'')]
    LPIVar (LPIVar(''h'':=LPIVar ''a''))"
  let ?caller_values = "\<lambda>x::string. LPIFun False [] :: (bool,string) lp_iterm"
  let ?local_values = "\<lambda>x::string. if x=''h'' then LPIFun False [] else LPIFun True [] :: (bool,string) lp_iterm"
  note universal = conjunct2[OF bad[unfolded lpc_mgu_resolve_def]]
  note selected = spec[OF spec[OF universal, of "?caller_values"], of "?local_values"]
  have impossible: "\<exists>delta. delta ''z''=LPIFun False [] \<and> delta ''z''=LPIFun True []"
    using selected by (auto; metis lp_iterm.inject)
  then show False by (metis lp_iterm.inject)
qed

ML \<open>
val checked = [@{thm lpc_captured_body_variable_is_not_mgu}];
val _ = if Thm_Deps.has_skip_proof checked orelse
  not (null (Thm_Deps.all_oracles checked))
  then error "Untrusted fresh head negative control" else ();
\<close>
end
