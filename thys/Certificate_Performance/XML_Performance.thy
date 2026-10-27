theory XML_Performance
  imports "Proof_Checker.CPF_Parser"
begin

text \<open>Prepare fixed tag representations at the call site, rather than
reconstructing them inside each invocation of the generic parser.\<close>
definition xml_do_prepared :: "string \<Rightarrow> ltag \<Rightarrow> 'a xmlst \<Rightarrow> 'a xmlt" where
  "xml_do_prepared name tag p x = (case x of
    (XML nam atts xmls, _, flag, cands, trail) \<Rightarrow>
      if nam = name then p (xmls,atts,False,[],tag#trail)
      else mismatch tag ([fst x], snd x)
    | _ \<Rightarrow> mismatch tag ([fst x], snd x))"

lemma xml_do_prepare [code_unfold]:
  "xml_do tag p = xml_do_prepared (String.explode tag) tag p"
  by (rule ext) (simp add: xml_do_def xml_do_prepared_def)

text \<open>A failed tag test can advance directly to the alternative, keeping
exactly the same accumulated expected tags and fatal-error behavior.\<close>
definition xml_do_or_prepared :: "string \<Rightarrow> ltag \<Rightarrow> 'a xmlst \<Rightarrow> 'a xmlt \<Rightarrow> 'a xmlt" where
  "xml_do_or_prepared name tag p q x = (case x of (node,atts,flag,cands,trail) \<Rightarrow>
    (case node of XML nam attrs children \<Rightarrow>
      if nam = name then
        bind2 (p (children,attrs,False,[],tag#trail))
          (\<lambda>e. case e of TagMismatch cs \<Rightarrow> q (node,atts,flag,cs,trail) | e \<Rightarrow> Left e) Right
      else q (node,atts,flag,tag#cands,trail)
    | XML_text _ \<Rightarrow> q (node,atts,flag,tag#cands,trail)))"

lemma xml_do_or_prepare [code_unfold]:
  "xml_or (xml_do_prepared name tag p) q = xml_do_or_prepared name tag p q"
  by (rule ext) (auto simp: xml_or_def xml_do_prepared_def xml_do_or_prepared_def
      mismatch_def bind2_def split: prod.splits xml.splits)


text \<open>Fuse adjacent tag alternatives into a single dispatch on the node.
A matched parser may still signal a mismatch: retain the original fallback in
that case, rather than assuming a property of arbitrary parser callbacks.\<close>
datatype xml_two_choice = XML_First | XML_Second | XML_Other
definition classify_xml_two where
  "classify_xml_two n1 n2 actual = (if actual = n1 then XML_First else
     if actual = n2 then XML_Second else XML_Other)"
definition xml_dispatch_two :: "string \<Rightarrow> ltag \<Rightarrow> 'a xmlst \<Rightarrow>
    string \<Rightarrow> ltag \<Rightarrow> 'a xmlst \<Rightarrow> 'a xmlt \<Rightarrow> 'a xmlt" where
  "xml_dispatch_two n1 t1 p1 n2 t2 p2 q x = (case x of (node,atts,flag,cands,trail) \<Rightarrow>
    case node of XML actual attrs children \<Rightarrow>
      (case classify_xml_two n1 n2 actual of
        XML_First \<Rightarrow> bind2 (p1 (children,attrs,False,[],t1#trail))
          (\<lambda>e. case e of TagMismatch cs \<Rightarrow>
             xml_do_or_prepared n2 t2 p2 q (node,atts,flag,cs,trail) | e \<Rightarrow> Left e) Right
      | XML_Second \<Rightarrow> bind2 (p2 (children,attrs,False,[],t2#trail))
          (\<lambda>e. case e of TagMismatch cs \<Rightarrow> q (node,atts,flag,cs,trail) | e \<Rightarrow> Left e) Right
      | XML_Other \<Rightarrow> q (node,atts,flag,t2#t1#cands,trail))
    | XML_text _ \<Rightarrow> q (node,atts,flag,t2#t1#cands,trail))"
lemma xml_dispatch_two_eq [code_unfold]:
  "xml_do_or_prepared n1 t1 p1 (xml_do_or_prepared n2 t2 p2 q) =
    xml_dispatch_two n1 t1 p1 n2 t2 p2 q"
  by (rule ext) (auto simp: xml_do_or_prepared_def xml_dispatch_two_def classify_xml_two_def
      split: prod.splits xml.splits)

lemma normalize_special_plain:
  "CHR ''&'' \<notin> set xs \<Longrightarrow> normalize_special xs = xs"
  by (induction xs) auto

definition normalize_text :: "string \<Rightarrow> string" where
  "normalize_text xs = (if CHR ''&'' \<in> set xs then normalize_special xs else xs)"
lemma normalize_text_eq:
  "normalize_text xs = normalize_special xs"
  by (auto simp: normalize_text_def normalize_special_plain)

text \<open>The parser-map refinements below fuse normalization with node
construction, avoiding a second XML tree and preserving every error result.\<close>
definition parser_map :: "('a \<Rightarrow> 'b) \<Rightarrow> ('t,'a) gen_parser \<Rightarrow> ('t,'b) gen_parser" where
  "parser_map f p s = map_sum id (\<lambda>(a,s). (f a,s)) (p s)"
lemma parser_map_return:
  "parser_map f (Parser_Monad.return x) = Parser_Monad.return (f x)"
  by (rule ext) (simp add: parser_map_def Parser_Monad.return_def)
lemma parser_map_bind:
  "parser_map f (Parser_Monad.bind p q) = Parser_Monad.bind p (\<lambda>x. parser_map f (q x))"
  by (rule ext) (auto simp: parser_map_def Parser_Monad.bind_def Error_Monad.bind_def split: sum.splits prod.splits)
lemma parser_map_bind_before:
  "Parser_Monad.bind (parser_map f p) q = Parser_Monad.bind p (\<lambda>x. q (f x))"
  by (rule ext) (auto simp: parser_map_def Parser_Monad.bind_def Error_Monad.bind_def split: sum.splits prod.splits)



lemma parser_map_result_bind:
  "map_sum id (\<lambda>(a,s). (f a,s)) (Parser_Monad.bind p q ts) =
    Parser_Monad.bind p (\<lambda>x. parser_map f (q x)) ts"
  by (simp only: parser_map_def[symmetric] parser_map_bind)
lemma parser_map_result_return:
  "map_sum id (\<lambda>(a,s). (f a,s)) (Parser_Monad.return x ts) = Parser_Monad.return (f x) ts"
  by (simp add: Parser_Monad.return_def)
lemma parser_map_if [simp]:
  "parser_map f (if b then p else q) = (if b then parser_map f p else parser_map f q)"
  by (cases b) simp_all
lemma parser_map_oneof:
  "parser_map f (oneof_closed_combined p q) = oneof_closed_combined (parser_map f p) (parser_map f q)"
  by (simp add: oneof_closed_combined parser_map_bind fun_eq_iff split: if_splits)
lemma parser_map_result_oneof:
  "map_sum id (\<lambda>(a,s). (f a,s)) (oneof_closed_combined p q ts) =
    oneof_closed_combined (parser_map f p) (parser_map f q) ts"
  by (simp only: parser_map_def[symmetric] parser_map_oneof)

definition normalized_nodes :: "xml list parser" where
  "normalized_nodes = parser_map (map (map_xml_text normalize_special)) parse_nodes"

lemma normalized_nodes_code [code]:
  "normalized_nodes [] = Parser_Monad.return [] []"
  "normalized_nodes (c # cs) =
    (if integer_of_char c = 60 then
       if (case cs of [] \<Rightarrow> False | d # _ \<Rightarrow> d = CHR ''/'') then Parser_Monad.return [] (c # cs)
       else (parse_name \<bind>
                     (\<lambda>n. parse_attributes \<bind>
                          (\<lambda>atts.
                              oneof_closed_combined (normalized_nodes \<bind> (\<lambda>xs. Parser_Monad.return (XML n atts [] # xs)))
                                  (normalized_nodes \<bind>
                                        (\<lambda>xs. exactly_end \<bind>
                                              (\<lambda>_. exactly n \<bind>
                                                   (\<lambda>_. exactly_close \<bind>
                                                        (\<lambda>_. normalized_nodes \<bind> (\<lambda>ns. Parser_Monad.return (XML n atts xs # ns))))))))))
                (trim cs)
    else (parse_text \<bind> (\<lambda>t. normalized_nodes \<bind> (\<lambda>ns. Parser_Monad.return (XML_text (normalize_text (the t)) # ns)))) (c # cs))"

  unfolding normalized_nodes_def
  apply (simp add: parser_map_def parse_nodes_code Parser_Monad.return_def)
  apply (subst parser_map_def)
  apply (subst parse_nodes_code)
  apply (cases "integer_of_char c = 60"; cases "case cs of [] \<Rightarrow> False | d # _ \<Rightarrow> d = CHR ''/''")
  apply (simp_all only: if_True if_False eq_refl list.map parser_map_result_bind parser_map_result_return
    parser_map_result_oneof parser_map_bind parser_map_return parser_map_oneof
    parser_map_bind_before normalize_text_eq map_xml_text.simps map.simps)
  apply (simp_all add: parser_map_result_bind parser_map_result_return
    parser_map_result_oneof parser_map_bind parser_map_return parser_map_oneof
    parser_map_bind_before normalize_text_eq)
  done


definition normalized_node :: "xml parser" where
  "normalized_node = parser_map (map_xml_text normalize_special) parse_node"
lemma normalized_node_code [code]:
  "normalized_node = do {
    exactly ''<'';
    n \<leftarrow> parse_name;
    atts \<leftarrow> parse_attributes;
    e \<leftarrow> oneof [''/>'', ''>''];
    if e = ''/>'' then Parser_Monad.return (XML n atts [])
    else do {
      cs \<leftarrow> normalized_nodes;
      exactly ''</'';
      exactly n;
      exactly ''>'';
      Parser_Monad.return (XML n atts cs)
    }
  }"
  by (simp add: normalized_node_def normalized_nodes_def parse_node_def
      parser_map_bind parser_map_return parser_map_bind_before cong: if_cong)

fun normalize_doc :: "xmldoc \<Rightarrow> xmldoc" where
  "normalize_doc (XMLDOC h x) = XMLDOC h (map_xml_text normalize_special x)"
definition normalized_doc :: "xmldoc parser" where
  "normalized_doc = parser_map normalize_doc parse_doc"
lemma normalized_doc_code [code]:
  "normalized_doc = do {
    update_tokens remove_comments;
    h \<leftarrow> parse_header;
    x \<leftarrow> normalized_node;
    eoi;
    Parser_Monad.return (XMLDOC h x)
  }"
  by (simp add: normalized_doc_def normalized_node_def parse_doc_def
      parser_map_bind parser_map_return parser_map_bind_before cong: if_cong)

definition normalized_doc_of_string :: "string \<Rightarrow> string + xmldoc" where
  "normalized_doc_of_string s = map_sum id normalize_doc (doc_of_string s)"
lemma normalized_doc_of_string_code [code]:
  "normalized_doc_of_string s = (case normalized_doc s of
     Inl e \<Rightarrow> Inl e | Inr (d,rest) \<Rightarrow> Inr d)"
  by (auto simp: normalized_doc_of_string_def normalized_doc_def parser_map_def
    doc_of_string_def Error_Monad.bind_def split: sum.splits prod.splits)

declare parse_xml_string_def[code del]
lemma parse_xml_string_fused_code [code]:
  "parse_xml_string p s = (case normalized_doc_of_string s of
    Inl e \<Rightarrow> Left e | Inr (XMLDOC h x) \<Rightarrow> parse_xml p x)"
  by (auto simp: parse_xml_string_def normalized_doc_of_string_def split: sum.splits xmldoc.splits)

end
