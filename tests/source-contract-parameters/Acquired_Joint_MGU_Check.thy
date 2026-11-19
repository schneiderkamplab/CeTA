theory Acquired_Joint_MGU_Check
 imports "../../thys/Logic_Programming/LP_Prolog_Acquired_Univ_Joint_MGU"
begin

lemma empty_prefix_mgu_positive:
 "lpc_mgu_resolve (LPIFun f []) [] (Fun f []) []
   (\<lambda>_::string. LPIFun f []) (\<lambda>_::string. LPIFun f [])"
 by (simp add: lpc_mgu_resolve_def)

lemma reverse_projection_negative:
 fixes f :: "'a"
 shows
 "\<not>lpc_mgu_resolve (LPIFun f []) [LPCAtom (LPIVar ''caller'')] (Fun f []) []
   (\<lambda>_::string. LPIFun f []) (\<lambda>_::string. LPIFun f [])"
proof
 assume full: "lpc_mgu_resolve (LPIFun f []) [LPCAtom (LPIVar ''caller'')] (Fun f []) []
   (\<lambda>_::string. LPIFun f []) (\<lambda>_::string. LPIFun f [])"
 have universal: "\<forall>tau::string\<Rightarrow>('a,string) lp_iterm. LPIFun f []=tau ''caller''"
  using full by (simp add: lpc_mgu_resolve_def)
 show False using universal[rule_format, of LPIVar] by simp

qed

ML \<open>
val checked = @{thms lpp_attached_resolution_common_mgu empty_prefix_mgu_positive reverse_projection_negative};
val _ = if Thm_Deps.has_skip_proof checked orelse not(null(Thm_Deps.all_oracles checked))
 then error "Untrusted common MGU" else ();
val _ = File.write (Path.explode "/work/dfm/festschrift/CeTA-prolog-release/target/source-acquired-joint-mgu/kernel-receipt.txt")
 ("Isabelle checked; no skipped proofs or oracles. Same actual MGU projects to helper; reverse projection rejected. Block and returns remain open.\n" ^
 cat_lines (map (Thm.string_of_thm @{context}) checked));
val _ = writeln "ACQUIRED_JOINT_MGU_RECEIPT_CHECKED";
\<close>
end
