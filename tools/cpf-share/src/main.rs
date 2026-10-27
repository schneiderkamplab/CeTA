//! Share byte-identical CPF terms through the existing sequential term table.
//! This is an exporter transformation, never an acceptance path in a checker.
use std::collections::HashMap;
use std::fmt::Write as _;
use std::io::Write as _;

#[derive(Hash, PartialEq, Eq)]
enum Part<'a> { Raw(&'a str), Term(usize) }
#[derive(Hash, PartialEq, Eq)]
struct Key<'a>(Vec<Part<'a>>);
struct Term<'a> { parts: Vec<Part<'a>>, count: usize, bytes: usize }

fn emit(id: usize, terms: &[Term<'_>], selected: &[bool], out: &mut String) {
    // Explicit stack avoids imposing a term-depth limit in the exporter.
    let mut stack: Vec<&Part<'_>> = terms[id].parts.iter().rev().collect();
    while let Some(part) = stack.pop() {
        match part {
            Part::Raw(raw) => out.push_str(raw),
            Part::Term(child) if selected[*child] => {
                write!(out, "<termIndex>t{child}</termIndex>").unwrap();
            }
            Part::Term(child) => stack.extend(terms[*child].parts.iter().rev()),
        }
    }
}

fn share(input: &str) -> Result<(String, usize), String> {
    let doc = roxmltree::Document::parse(input).map_err(|e| e.to_string())?;
    let root = doc.root_element();
    if root.tag_name().name() != "certificationProblem" {
        return Ok((input.to_owned(), 0));
    }
    // The relative-ADP integration reparses proof fragments with fresh lookup
    // maps. Retain the whole document until that adapter threads the tables.
    if doc.descendants().any(|n| n.has_tag_name("relativeAdpTerminationProof")) {
        return Ok((input.to_owned(), 0));
    }
    let tables: Vec<_> = root.children().filter(|n| n.has_tag_name("lookupTables")).collect();
    if tables.len() != 1 || doc.descendants().any(|n| n.is_element() && n.tag_name().namespace().is_some()) { return Ok((input.to_owned(), 0)); }
    let table = tables[0];
    if table.attributes().len() != 0 || doc.descendants().any(|n| n.has_tag_name("termIndex") || n.has_tag_name("ruleIndex")) { return Ok((input.to_owned(), 0)); }
    if table.children().any(|n| n.is_element() || n.is_text() && !n.text().unwrap_or("").trim().is_empty()) {
        // Existing tables have their own binding order; retain them verbatim.
        return Ok((input.to_owned(), 0));
    }
    let mut ids = vec![usize::MAX; doc.descendants().count()];
    let mut intern: HashMap<Key<'_>, usize> = HashMap::new();
    let mut terms: Vec<Term<'_>> = Vec::new();
    // Node ids are in document order; reverse order visits children first.
    for node in doc.descendants().collect::<Vec<_>>().into_iter().rev() {
        if !(node.has_tag_name("funapp") || node.has_tag_name("var")) { continue; }
        let span = node.range();
        let mut cursor = span.start;
        let mut parts = Vec::new();
        for child in node.children().filter(|n| n.is_element()) {
            let child_id = ids[child.id().get_usize()];
            if child_id == usize::MAX { continue; }
            let range = child.range();
            parts.push(Part::Raw(&input[cursor..range.start]));
            parts.push(Part::Term(child_id));
            cursor = range.end;
        }
        parts.push(Part::Raw(&input[cursor..span.end]));
        let key = Key(parts);
        let id = match intern.get(&key) {
            Some(&id) => { terms[id].count += 1; id }
            None => {
                let id = terms.len();
                let copy = key.0.iter().map(|p| match p { Part::Raw(s) => Part::Raw(*s), Part::Term(i) => Part::Term(*i) }).collect();
                terms.push(Term { parts: copy, count: 1, bytes: span.len() });
                intern.insert(key, id); id
            }
        };
        ids[node.id().get_usize()] = id;
    }
    // Never replace a term whose original spelling is shorter than its reference.
    let selected: Vec<_> = terms.iter().map(|t| t.count > 1 && t.bytes >= 80).collect();
    let mut table_xml = String::from("<lookupTables><termIndexTable>");
    for id in 0..terms.len() {
        if selected[id] {
            write!(table_xml, "<indexToTerm><index>t{id}</index>").unwrap();
            emit(id, &terms, &selected, &mut table_xml);
            table_xml.push_str("</indexToTerm>");
        }
    }
    table_xml.push_str("</termIndexTable></lookupTables>");
    let mut edits: Vec<(std::ops::Range<usize>, Option<usize>)> = vec![(table.range(), None)];
    let mut covered_until = 0;
    for node in doc.descendants() {
        let id = ids[node.id().get_usize()];
        if id == usize::MAX || !selected[id] { continue; }
        let span = node.range();
        if span.start < covered_until { continue; }
        covered_until = span.end;
        edits.push((span, Some(id)));
    }
    edits.sort_unstable_by_key(|(r,_)| r.start);
    let mut output = String::new();
    let mut cursor = 0;
    for (span, term) in edits {
        output.push_str(&input[cursor..span.start]);
        match term {
            None => output.push_str(&table_xml),
            Some(id) => write!(output, "<termIndex>t{id}</termIndex>").unwrap(),
        }
        cursor = span.end;
    }
    output.push_str(&input[cursor..]);
    if output.len() >= input.len() { return Ok((input.to_owned(), 0)); }
    Ok((output, selected.iter().filter(|&&x| x).count()))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 3 { return Err("usage: cpf-share INPUT.xml NEW-OUTPUT.xml".into()); }
    let input = std::fs::read_to_string(&args[1])?;
    let (output, terms) = share(&input).map_err(std::io::Error::other)?;
    let mut f = std::fs::OpenOptions::new().write(true).create_new(true).open(&args[2])?;
    f.write_all(output.as_bytes())?;
    println!("{{\"original_bytes\":{},\"shared_bytes\":{},\"table_entries\":{}}}", input.len(), output.len(), terms);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn small_and_existing_tables_stay_unchanged() {
        for text in ["<certificationProblem><lookupTables/><var>x</var></certificationProblem>",
          "<certificationProblem><lookupTables><termIndexTable/></lookupTables><var>x</var></certificationProblem>"] {
            assert_eq!(share(text).unwrap(), (text.to_string(), 0));
        }
    }
    #[test]
    fn never_binds_existing_references_or_rewrites_other_formats() {
        for text in [
            "<certificationProblem><lookupTables/><termIndex>t0</termIndex></certificationProblem>",
            "<certificationProblem><lookupTables/><ruleIndex>r0</ruleIndex></certificationProblem>",
            "<certificationProblem xmlns=\"urn:other\"><lookupTables/></certificationProblem>",
            "<other><lookupTables/></other>",
        ] { assert_eq!(share(text).unwrap(), (text.to_string(), 0)); }
        assert!(share("<unclosed>").is_err());
    }
    #[test]
    fn relative_adp_documents_keep_explicit_terms() {
        let term = "<funapp><name>long_symbol_name_which_is_intentionally_not_a_specific_benchmark</name><var>x</var></funapp>";
        let input=format!("<certificationProblem><lookupTables/>{}<relativeAdpTerminationProof/></certificationProblem>",term.repeat(20));
        assert_eq!(share(&input).unwrap(),(input,0));
    }
    #[test]
    fn distinct_leaf_text_remains_distinct() {
        let a = "<funapp><name>long_symbol_name_which_is_intentionally_not_a_specific_benchmark</name><var>x</var></funapp>";
        let b = a.replace("<var>x</var>", "<var> x </var>");
        let input = format!("<certificationProblem><lookupTables/>{}{}</certificationProblem>", a.repeat(20), b.repeat(20));
        let (out,n)=share(&input).unwrap(); assert!(n>=2);
        assert!(out.contains("<var>x</var>") && out.contains("<var> x </var>"));
        assert_eq!(share(&input).unwrap().0, out);
    }
    #[test]
    fn shares_only_identical_syntax_in_dependency_order() {
        let t = "<funapp><name>long_symbol_name_which_is_intentionally_not_a_specific_benchmark</name><var> x </var></funapp>";
        let input = format!("<certificationProblem><lookupTables/><rules>{}</rules></certificationProblem>", t.repeat(20));
        let (out,n) = share(&input).unwrap(); assert!(n>0); assert!(out.len()<input.len());
        let doc = roxmltree::Document::parse(&out).unwrap();
        assert!(doc.descendants().any(|x| x.has_tag_name("var") && x.text()==Some(" x ")));
        let mut known = std::collections::HashSet::new();
        for entry in doc.descendants().filter(|x| x.has_tag_name("indexToTerm")) {
            for reference in entry.descendants().filter(|x| x.has_tag_name("termIndex")) { assert!(known.contains(reference.text().unwrap())); }
            known.insert(entry.children().find(|x| x.has_tag_name("index")).unwrap().text().unwrap());
        }
    }
}
