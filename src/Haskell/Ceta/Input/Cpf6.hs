-- CPF 6 LP envelope decoding only. Mathematical checks remain generated Isabelle.
module Ceta.Input.Cpf6 (logicProgramming, prologCertificate) where
import qualified Ceta.Input.Cpf4 as X
import Control.Monad (unless, zipWithM, mapM_)
import Data.Char (isSpace)
import Data.List (isPrefixOf)

label (X.Element n _ _) = n
label _ = ""
assert b message = unless b (Left message)

-- Only inspect the root name for routing. Do not impose this envelope parser's
-- syntax/resource limits on legacy fragments accepted by generated parsers.
through end [] = []
through end source | end `isPrefixOf` source = drop (length end) source
through end (_:rest) = through end rest
prolog source = let s = dropWhile isSpace source in
  if "<?" `isPrefixOf` s then prolog (through "?>" (drop 2 s))
  else if "<!--" `isPrefixOf` s then prolog (through "-->" (drop 4 s))
  else s
isEnvelope source = takeWhile (\c -> not (isSpace c) && c /= '>' && c /= '/') source == "<certificationProblem"

-- Existing fragment roots remain available during the staged migration.
-- New CPF roots must bind the source and claim before reaching any checker.
logicProgramming :: String -> Either String String
logicProgramming source
  | not (isEnvelope (prolog source)) = Right source
  | otherwise = do
    (version,input,property,answer,proof) <- X.envelope (prolog source)
    assert (version == "6.0") "logic-programming additions require CPF 6"
    if label input == "logicProgramWithCutInput"
      then cutCertificate input property answer proof
      else if label input == "logicProgramTriplesInput"
        then tripleCertificate input property answer proof
      else do
        assert (label input == "logicProgramInput") "expected logicProgramInput"
        assert (property == "termination") "LP proof requires a termination property"
        fields <- X.elems input
        assert (map label fields == ["resolutionSemantics","program","query"]) "invalid LP input fields"
        let [semantics,program,query] = fields
        mode <- X.scalar semantics
        let spec = case label proof of
              "lpInitialDependencyTriplesProof" -> Just ("infiniteTrees","yes",["returns","fallback","programContinuations","marks","argumentFilter","ranks","components","triples","tripleContinuations"],5)
              "lpSymbolicGraphTerminationProof" -> Just ("infiniteTrees","yes",["fuel","root","nodes","rules","trsTerminationProof"],1)
              "lpFiniteTerminationProof" -> Just ("finiteTerms","yes",["returns","fallback","continuations","argumentFilter","trsTerminationProof"],4)
              "lpTocl09TerminationProof" -> Just ("infiniteTrees","yes",["returns","fallback","continuations","argumentFilter","trsTerminationProof"],4)
              "lpTocl09SourceLoopProof" -> Just ("infiniteTrees","no",["clauseIndex","seed","substitution"],1)
              "lpTocl09SourceTraceProof" -> Just ("infiniteTrees","no",["seed","initial","steps","substitution"],1)
              "lpTocl09SourceUnifyProof" -> Just ("infiniteTrees","no",["initial","prefix","steps","substitution"],1)
              "lpTocl09SourceNeutralProof" -> Just ("infiniteTrees","no",["initial","prefix","clauseIndex","neutral","substitution","substitution"],1)
              "lpTocl09RecurrentPairProof" -> Just ("infiniteTrees","no",["atomContext","termContext","firstHole","secondHole","seed","stride","pumpBase","resetBase","pumpGrowth","resetGrowth","resetOffset","keepFirst","steps","steps"],1)
              "lpTocl09AffineLoopProof" -> Just ("infiniteTrees","no",["constructor","zero","environment","atomContext","steps","prefixes","affine","affine"],1)
              "lpTocl09PatternLoopProof" -> Just ("infiniteTrees","no",["atomContext","substitution","substitution","steps","prefixes"],1)
              "lpTocl09PiDpTerminationProof" -> Just ("infiniteTrees","yes",["returns","fallback","continuations","marks","argumentFilter","ranks","components"],5)
              "lpTocl09ModeTerminationProof" -> Just ("infiniteTrees","yes",["modes","lpTocl09TerminationProof"],1)
              "lpTocl09PiDpModeTerminationProof" -> Just ("infiniteTrees","yes",["modes","lpTocl09PiDpTerminationProof"],1)
              "lpTocl09SimplificationProof" -> Just ("infiniteTrees","yes",["lpTocl09PiDpModeTerminationProof"],1)
              "lpTocl09SourceGraphProof" -> Just ("infiniteTrees","yes",["fuel","root","nodes"],1)
              "lpAnswerGraphTerminationProof" -> Just ("infiniteTrees","yes",["fuel","root","nodes","lpTerminationChild"],1)
              "lpConstructorQDpTerminationProof" -> Just ("infiniteTrees","yes",["returns","fallback","continuations","marks","argumentFilter","seed","dpProof"],5)
              _ -> Nothing
        (expectedMode,expectedAnswer,baseNames,queryIndex) <- maybe (Left "unsupported LP constructor") Right spec
        assert (mode == expectedMode && answer == expectedAnswer) "LP proof/semantics/answer mismatch"
        evidence <- X.elems proof
        let names = if label proof == "lpConstructorQDpTerminationProof" && "normalSubstitutions" `elem` map label evidence
              then init baseNames ++ ["normalSubstitutions",last baseNames] else baseNames
            childTags = ["lpTocl09TerminationProof","lpTocl09PiDpTerminationProof","lpTocl09PiDpModeTerminationProof","lpTerminationChild"]
            cpfName name = if name `elem` childTags then "certificationProblem" else name
            expected = map cpfName names
        assert (map label evidence == expected ||
          (label proof == "lpTocl09PatternLoopProof" && map label evidence == expected ++ ["acceleration"])) "invalid LP proof fields"
        let decodeChild name node = if name `elem` childTags then do
              child <- logicProgramming (X.renderXML node) >>= X.parseXML
              assert (if name == "lpTerminationChild" then label child `elem` ["lpTocl09TerminationProof","lpConstructorQDpTerminationProof"]
                else label child == name) "LP child constructor mismatch"
              return child
              else return node
        nativeEvidence <- zipWithM decodeChild (names ++ ["acceleration"]) evidence
        let nativeFields = program : (take (queryIndex-1) nativeEvidence ++ [query] ++ drop (queryIndex-1) nativeEvidence)
        let result = if label proof == "lpInitialDependencyTriplesProof"
              then [X.Element "lpDependencyTriplesPiDpProof" [] (map (nativeFields !!) [9,0,1,2,10,3,4,5,6,7,8])]
              else nativeFields
        return (X.renderXML (X.Element (label proof) [] result))

-- Source and query occur only in the CPF input; rebuild the unchanged native
-- parser's argument tuple before calling its generated sound checker.
cutCertificate input property answer proof = do
  assert (property == "termination") "cut property mismatch"
  let spec = case label proof of
        "lpCutReturnConstructorGraphTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","root","nodes","returnStates","returnSymbol","returnArity","actions","residual","predicateEncoding","dataEncoding","lpConstructorQDpTerminationProof"])
        "lpCutReturnDependencyTriplesProof" -> Just ("orderedCutMgu","yes",["fuel","root","nodes","returnStates","returnSymbol","returnArity","actions","residual","predicateEncoding","dataEncoding","lpDependencyTriplesPiDpProof"])
        "lpCutReturnModuleConstructorGraphTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","root","nodes","returnStates","returnSymbol","returnArity","actions","residual","predicateEncoding","dataEncoding","lpConstructorQDpTerminationProof"])
        "lpCutReturnModuleDependencyTriplesProof" -> Just ("orderedCutMgu","yes",["fuel","root","nodes","returnStates","returnSymbol","returnArity","actions","residual","predicateEncoding","dataEncoding","lpDependencyTriplesPiDpProof"])
        "lpCutReturnComposedConstructorGraphTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","root","nodes","returnStates","returnSymbol","returnArity","actions","residual","predicateEncoding","dataEncoding","lpConstructorQDpTerminationProof"])
        "lpCutReturnComposedDependencyTriplesProof" -> Just ("orderedCutMgu","yes",["fuel","root","nodes","returnStates","returnSymbol","returnArity","actions","residual","predicateEncoding","dataEncoding","lpDependencyTriplesPiDpProof"])
        "lpCutReturnNestedConstructorGraphTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","root","height","moduleRoot","modules","moduleActions","residual","predicateEncoding","dataEncoding","lpConstructorQDpTerminationProof"])
        "lpCutReturnNestedDependencyTriplesProof" -> Just ("orderedCutMgu","yes",["fuel","root","height","moduleRoot","modules","moduleActions","residual","predicateEncoding","dataEncoding","lpDependencyTriplesPiDpProof"])
        "lpCutProjectedGraphTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","root","height","moduleRoot","modules","moduleActions","residual","rules","encoding","fallback","argumentFilter","trsTerminationProof"])
        "lpCutSEGDependencyTriplesProof" -> Just ("orderedCutMgu","yes",["fuel","chainPredicate","triples","successProgram","roots","components","predicateEncoding","dataEncoding","lpDependencyTriplesPiDpProof"])
        "lpCutSEGTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","roots","regions","continuations","controlEncoding","dataEncoding","fallback","constructors","rules","trsTerminationProof"])
        "lpCutSEGFreeTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","roots","rootFree","regions","continuations","controlEncoding","dataEncoding","fallback","constructors","rules","trsTerminationProof"])
        "lpCutSEGProjectedTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","roots","rootFree","regions","continuations","controlEncoding","dataEncoding","fallback","argumentFilter","rules","trsTerminationProof"])
        "lpCutUniformRecursionProof" -> Just ("orderedCutMgu","no",["clause","variables","callArguments","arguments"])
        "lpCutSourceNonterminationProof" -> Just ("orderedCutMgu","no",["fuel","arguments","core","before","after","prefix","loop"])
        "lpCutGraphTerminationProof" -> Just ("orderedCut","yes",["fuel","root","nodes","actions","residual","predicateEncoding","dataEncoding","lpTocl09TerminationProof"])
        "lpCutConstructorGraphTerminationProof" -> Just ("orderedCut","yes",["fuel","root","nodes","actions","residual","predicateEncoding","dataEncoding","lpConstructorQDpTerminationProof"])
        "lpCutMguConstructorGraphTerminationProof" -> Just ("orderedCutMgu","yes",["fuel","root","nodes","freeBlocks","actions","residual","predicateEncoding","dataEncoding","lpConstructorQDpTerminationProof"])
        _ -> Nothing
  (expectedMode,expectedAnswer,names) <- maybe (Left "unsupported cut constructor") Right spec
  assert (answer == expectedAnswer) "cut answer mismatch"
  fields <- X.elems input
  assert (map label fields == ["executionSemantics","program","query"]) "invalid cut input"
  let [semantics,program,query] = fields
  mode <- X.scalar semantics
  assert (mode == expectedMode) "cut execution semantics mismatch"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid cut query"
  evidence <- X.elems proof
  let isChild n = n `elem` ["lpTocl09TerminationProof","lpConstructorQDpTerminationProof","lpDependencyTriplesPiDpProof"]
  assert (map label evidence == map (\n -> if isChild n then "certificationProblem" else n) names) "invalid cut fields"
  let decodeChild name n = if isChild name then do
        child <- logicProgramming (X.renderXML n) >>= X.parseXML
        if label proof `elem` ["lpCutReturnDependencyTriplesProof","lpCutReturnModuleDependencyTriplesProof","lpCutReturnComposedDependencyTriplesProof","lpCutReturnNestedDependencyTriplesProof"] && name == "lpDependencyTriplesPiDpProof" then do
          assert (label child == "lpInitialDependencyTriplesProof") "return triples require initial-triples child"
          fields <- X.elems child
          assert (map label fields == ["lpDependencyTriplesPiDpProof"]) "invalid initial-triples wrapper"
          return (head fields)
        else do
          assert (label child == name) "cut child constructor mismatch"
          return child
        else returnResiduals n
  native <- zipWithM decodeChild names evidence
  return (X.renderXML (X.Element (label proof) [] (program : queryFields ++ native)))

-- A dependency-triple residual has its own input: its support program need
-- not terminate. The generated triple checker retains the chain semantics.
tripleCertificate input property answer proof = do
  assert (property == "termination" && answer == "yes") "triple claim mismatch"
  assert (label proof `elem` ["lpDependencyTriplesPiDpProof","lpDependencyTriplesConstructorProof"]) "triple constructor mismatch"
  fields <- X.elems input
  assert (map label fields == ["resolutionSemantics","triples","program","query"]) "invalid triple input"
  let [semantics,triples,program,query] = fields
  mode <- X.scalar semantics
  assert (mode == "infiniteTrees") "triple semantics mismatch"
  evidence <- X.elems proof
  let constructor = label proof == "lpDependencyTriplesConstructorProof"
      hasNfs = any ((== "normalSubstitutions") . label) evidence
      ending = if constructor then ["seed"] ++ (if hasNfs then ["normalSubstitutions"] else []) ++ ["dpProof"] else ["ranks","components"]
  assert (map label evidence == ["returns","fallback","tripleContinuations","programContinuations","marks","argumentFilter"] ++ ending) "invalid triple evidence"
  return (X.renderXML (X.Element (label proof) []
    ([triples,program] ++ take 5 evidence ++ [query] ++ drop 5 evidence)))

-- Independent return residuals carry complete CPF LP children too.
returnResiduals node@(X.Element name attrs _) = do
  if name == "residualCertificate" then do
    fields <- X.elems node
    assert (map label fields == ["residual","predicateEncoding","dataEncoding","certificationProblem"]) "invalid return residual fields"
    child <- logicProgramming (X.renderXML (last fields)) >>= X.parseXML
    assert (label child == "lpConstructorQDpTerminationProof") "return residual child constructor mismatch"
    return (X.Element name attrs (take 3 fields ++ [child]))
  else case node of
    X.Element _ _ children -> do
      children' <- mapM returnResiduals children
      return (X.Element name attrs children')
returnResiduals node = Right node


-- Compare source trees without losing scalar whitespace or entity fragments.
sourceTree n@(X.Element tag [] cs) =
  if any (\c -> case c of X.Element _ _ _ -> True; _ -> False) cs
  then do es <- X.elems n; cleaned <- mapM sourceTree es; return (X.Element tag [] cleaned)
  else do value <- X.scalar n; return (X.Element tag [] [X.Text value])
sourceTree _ = Left "invalid source tree"

prologCertificate :: String -> Either String String
prologCertificate source
  | not (isEnvelope (prolog source)) = Right source
  | otherwise = do
    (version,input,property,answer,proof) <- X.envelope (prolog source)
    assert (version == "6.0" && label input == "prologInput" && property == "termination") "expected CPF6 Prolog source claim"
    fields <- X.elems input
    assert (map label fields == ["executionProfile","program","query"]) "invalid Prolog source fields"
    let [profile,program,query] = fields
    mode <- X.scalar profile
    if maybe False (const True) (prologSourceSpec (label proof)) then
      prologSourceCertificate mode program query answer proof
    else if label proof == "prologUndefinedQueryProof" then
      undefinedCertificate mode program query answer proof
    else if label proof == "prologEstablishedStableSEGGuardedProof" then
      prologStableGuardedCertificate mode program query answer proof
    else if label proof == "prologEstablishedFiniteDirectProof" then
      prologFiniteDirectCertificate mode program query answer proof
    else if label proof `elem` ["prologContextDependencyTriplesProof", "prologContextComposedDependencyTriplesProof"] then
      prologContextCertificate mode program query answer proof
    else if label proof `elem` ["prologEstablishedSEGDependencyTriplesProof","prologEstablishedSEGConstructorTriplesProof","prologEstablishedFiniteSEGDependencyTriplesProof","prologEstablishedFiniteSEGConstructorTriplesProof"] then
      prologEstablishedCertificate mode program query answer proof
    else if label proof `elem` ["prologVarReturnDependencyTriplesProof","prologModularReturnDependencyTriplesProof"] then
      prologReturnCertificate mode program query answer proof
    else if label proof `elem` ["prologIntegerSourceNonterminationProof","prologGroundIntegerSourceNonterminationProof"] then
      prologIntegerNoCertificate mode program query answer proof
    else if label proof `elem` ["prologTestSourceNonterminationProof","prologRationalSourceNonterminationProof"] then
      prologTestNoCertificate mode program query answer proof
    else do
      let spec = case label proof of
            "prologStaticSEGProof" -> Just ("yes","lpCutSEGDependencyTriplesProof")
            "prologStaticNonterminationProof" -> Just ("no","lpCutSourceNonterminationProof")
            "prologStaticUniformRecursionProof" -> Just ("no","lpCutUniformRecursionProof")
            _ -> Nothing
      (expected,childTag) <- maybe (Left "unsupported Prolog CPF6 constructor") Right spec
      assert (answer == expected) "Prolog answer mismatch"
      evidence <- X.elems proof
      assert (map label evidence == ["predicates","certificationProblem"]) "invalid Prolog evidence"
      let [predicates,childCPF] = evidence
      raw <- logicProgramming (X.renderXML childCPF)
      child <- X.parseXML raw
      assert (label child == childTag) "Prolog child constructor mismatch"
      childFields <- X.elems child
      assert (take 3 (map label childFields) == ["program","predicate","modes"]) "invalid Prolog child source"
      queryFields <- X.elems query
      assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
      outer <- mapM sourceTree (program:queryFields)
      inner <- mapM sourceTree (take 3 childFields)
      assert (outer == inner) "Prolog source/child mismatch"
      return (X.renderXML (X.Element (label proof) [] [X.Element "profile" [] [X.Text mode],predicates,child]))


-- Validate the complete typed program before deriving its definition list.
-- Clause bodies may contain arbitrary supported source goals: they are unreachable.
cutTerm n = case label n of
  "var" -> X.scalar n >> return ()
  "funapp" -> do
    fields <- X.elems n
    assert (not (null fields)) "missing cut function symbol"
    let symbol = head fields
    if label symbol == "user" then X.scalar symbol >> return ()
    else do
      assert (label symbol `elem` ["bangSymbol","commaSymbol","equalsSymbol","trueSymbol","failSymbol","callSymbol"]) "unknown cut symbol"
      empty <- X.elems symbol
      assert (null empty) "nonempty cut symbol"
    mapM_ cutTerm (tail fields)
  _ -> Left "expected cut term"

cutGoal n = case label n of
  "cut" -> do
    value <- X.scalar n
    assert (not (null value) && all (`elem` ['0'..'9']) value) "expected cut natural"
  tag | tag `elem` ["true","fail"] -> X.elems n >>= \cs -> assert (null cs) "nonempty cut constant"
  tag | tag `elem` ["atom","meta","unify"] -> do
    cs <- X.elems n
    assert (length cs == if tag == "unify" then 2 else 1) "invalid cut goal operands"
    mapM_ cutTerm cs
  _ -> Left "unknown cut goal"

programDefinitions program = do
  clauses <- X.elems program
  entries <- mapM clause clauses
  return (concat entries)
  where
    clause n = do
      assert (label n == "clause") "expected cut clause"
      cs <- X.elems n
      assert (map label cs == ["head","body"]) "invalid source clause"
      hs <- X.elems (head cs)
      assert (length hs == 1) "invalid clause head"
      cutTerm (head hs)
      X.elems (last cs) >>= mapM_ cutGoal
      if label (head hs) /= "funapp" then return [] else do
        terms <- X.elems (head hs)
        if label (head terms) /= "user" then return [] else do
          name <- X.scalar (head terms)
          return [X.Element "signature" [] [X.Element "name" [] [X.Text name],
            X.Element "arity" [] [X.Text (show (length (tail terms)))]]]

undefinedCertificate mode program query answer proof = do
  assert (answer == "yes") "undefined entry requires YES"
  evidence <- X.elems proof
  assert (map label evidence == ["definitions"]) "invalid undefined-entry evidence"
  derived <- programDefinitions program
  supplied <- X.elems (head evidence) >>= mapM sourceTree
  expected <- mapM sourceTree derived
  assert (supplied == expected) "definition signatures do not match complete source"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  return (X.renderXML (X.Element "prologUndefinedQueryProof" []
    ([X.Element "profile" [] [X.Text mode],head evidence] ++ queryFields)))

-- Primitive Prolog return tables expose a full initial-LP triple obligation.
prologContextCertificate mode program query answer proof = do
  assert (answer == "yes") "contextual Prolog proof requires YES"
  fields <- X.elems proof
  assert (map label fields == ["fuel","root","nodes","returnStates","contexts","typings",
    "prologSuccessTransferContract","returnSymbol","returnArity","actions","residual",
    "predicateEncoding","dataEncoding","certificationProblem"]) "invalid contextual Prolog fields"
  child <- logicProgramming (X.renderXML (last fields)) >>= X.parseXML
  assert (label child == "lpDependencyTriplesPiDpProof") "contextual Prolog requires dependency-triples child"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  let moduleTag = if label proof == "prologContextComposedDependencyTriplesProof" then "prologContextComposed" else "prologContextModule"
      contextModule = X.Element moduleTag [] (program : take 11 fields)
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode]] ++ queryFields ++ [contextModule] ++ take 2 (drop 11 fields) ++ [child])))

prologStableGuardedCertificate mode program query answer proof = do
  assert (answer == "yes") "stable guarded Prolog proof requires YES"
  fields <- X.elems proof
  assert (map label fields == ["fuel","chainPredicate","triples","successProgram","prologSuccessTransferContract",
    "contexts","roots","components","observedTriples","guardedDescents","argumentProjection","prologStableNumericComponent"])
    "invalid stable guarded Prolog fields"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode],program] ++ queryFields ++ fields)))

prologFiniteDirectCertificate mode program query answer proof = do
  assert (answer == "yes") "finite direct Prolog proof requires YES"
  fields <- X.elems proof
  assert (map label fields == ["signatures","prologEvaluationControl","freeKnowledge"]) "invalid finite direct Prolog fields"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode],program] ++ queryFields ++ fields)))

prologEstablishedCertificate mode program query answer proof = do
  assert (answer == "yes") "established Prolog proof requires YES"
  fields <- X.elems proof
  assert (map label fields == ["fuel","chainPredicate","triples","successProgram","prologSuccessTransferContract",
    "contexts","roots","components","predicateEncoding","dataEncoding","certificationProblem"]) "invalid established Prolog fields"
  child <- logicProgramming (X.renderXML (last fields)) >>= X.parseXML
  let expectedChild = if label proof `elem` ["prologEstablishedSEGConstructorTriplesProof","prologEstablishedFiniteSEGConstructorTriplesProof"] then "lpDependencyTriplesConstructorProof" else "lpDependencyTriplesPiDpProof"
  assert (label child == expectedChild) "established Prolog child constructor mismatch"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode],program] ++ queryFields ++ take 10 fields ++ [child])))

prologReturnCertificate mode program query answer proof = do
  assert (answer == "yes") "Prolog return proof requires YES"
  fields <- X.elems proof
  assert (map label fields == ["fuel","root","nodes","returnStates","returnSymbol","returnArity",
    "actions","residual","predicateEncoding","dataEncoding","certificationProblem"]) "invalid Prolog return fields"
  child <- logicProgramming (X.renderXML (last fields)) >>= X.parseXML
  assert (label child == "lpInitialDependencyTriplesProof") "Prolog return requires initial-triples child"
  inner <- X.elems child
  assert (map label inner == ["lpDependencyTriplesPiDpProof"]) "invalid initial-triples child"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode],program] ++ queryFields ++ take 10 fields ++ inner)))

prologTestNoCertificate mode program query answer proof = do
  assert (answer == "no") "Prolog test nontermination requires NO"
  fields <- X.elems proof
  let expected = if label proof == "prologRationalSourceNonterminationProof"
        then ["predicates","fuel","arguments","graph","anchors","variable","rhs","bindingRoot","call","callRoot","before","after","prefix","loop"]
        else ["predicates","fuel","arguments","core","before","after","prefix","loop"]
  assert (map label fields == expected) "invalid Prolog nontermination fields"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode],head fields,program] ++ queryFields ++ tail fields)))

prologIntegerNoCertificate mode program query answer proof = do
  assert (answer == "no") "Prolog integer nontermination requires NO"
  fields <- X.elems proof
  assert (map label fields == ["fuel","arguments","core","before","after","prefix","loop"]) "invalid Prolog integer nontermination fields"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode],program] ++ queryFields ++ fields)))

-- Remaining source forms, in the field order of their Isabelle XML parsers.
prologSourceSpec tag = lookup tag
  [("prologBinary64SourceNonterminationProof",("no",["fuel", "arguments", "core|coreGoals", "before", "after", "prefix", "loop"])),
   ("prologContextITSProof",("yes",["fuel", "roots", "regions", "prologNumericComponent"])),
   ("prologDomainGraphNonterminationProof",("no",["version", "fuel", "arguments", "prefix", "corePredicate", "coreArguments", "pending", "saved", "observations", "initialRecipes", "entry", "modules"])),
   ("prologEstablishedFiniteSEGGuardedProof",("yes",["fuel", "chainPredicate", "triples", "successProgram", "prologSuccessTransferContract", "contexts", "roots", "components", "observedTriples", "guardedDescents", "argumentProjection", "prologNumericComponent"])),
   ("prologEstablishedFiniteLocalSEGMixedProof",("yes",["signatures", "fuel", "chainPredicate", "triples", "successProgram", "prologSuccessTransferContract", "contexts", "roots", "components", "observedTriples", "guardedDescents", "routing", "backends"])),
   ("prologGuardedDomainGraphNonterminationProof",("no",["version", "fuel", "arguments", "prefix", "corePredicate", "coreArguments", "pending", "saved", "observations", "initialRecipes", "entry", "modules"])),
   ("prologHelperIntegerCallsProof",("no",["observations", "interfaces", "callEdges", "numericChild"])),
   ("prologIntegerCallsProof",("no",["interfaces", "callEdges", "numericChild"])),
   ("prologIntegerRecurrenceProof",("no",["clause", "variables", "operations", "outputs", "coordinates", "location", "numericChild"])),
   ("prologCallTraceNonterminationProof",("no",["version", "fuel", "arguments", "prefix", "core", "pending", "saved", "reserved", "interface", "calls", "traces"])),
   ("prologPartialIntegerCallsProof",("no",["observations", "interfaces", "callEdges", "numericChild"])),
   ("prologScalarDomainRecurrenceNonterminationProof",("no",["version", "fuel", "arguments", "prefix", "corePredicate", "coreArguments", "pending", "saved", "observations", "initialRecipes", "selection", "variables", "actions", "outputs", "recipes", "failures"])),
   ("prologScalarRecurrenceNonterminationProof",("no",["observations", "selection", "variables", "actions", "outputs", "recipes", "failures"])),
   ("prologEstablishedStableSEGMixedProof",("yes",["fuel", "chainPredicate", "triples", "successProgram", "prologSuccessTransferContract", "contexts", "roots", "components", "observedTriples", "routing", "backends"])),
   ("prologEstablishedStoppedSEGMixedProof",("yes",["fuel", "chainPredicate", "triples", "successProgram", "prologSuccessTransferContract", "contexts", "roots", "components", "observedTriples", "successCases?", "equationNormalizationFuel?", "normalizedTriples?", "routing", "backends"]))]

sourceNames [] [] = True
sourceNames [] _ = False
sourceNames (s:ss) ns =
  let optional = not (null s) && last s == '?'
      field = if optional then init s else s
      alternatives = case break (=='|') field of (a,[]) -> [a]; (a,_:b) -> [a,b]
  in case ns of
       n:rest | n `elem` alternatives -> sourceNames ss rest
       _ -> optional && sourceNames ss ns

prologSourceCertificate mode program query answer proof = do
  (expected,names) <- maybe (Left "unknown Prolog source form") Right (prologSourceSpec (label proof))
  assert (answer == expected) "Prolog source answer mismatch"
  evidence <- X.elems proof
  assert (sourceNames names (map label evidence)) "invalid Prolog source evidence fields"
  queryFields <- X.elems query
  assert (map label queryFields == ["predicate","modes"]) "invalid Prolog query"
  let (version,body) = if take 1 names == ["version"] then splitAt 1 evidence else ([],evidence)
  return (X.renderXML (X.Element (label proof) []
    ([X.Element "profile" [] [X.Text mode]] ++ version ++ [program] ++ queryFields ++ body)))
