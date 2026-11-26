"""Structured evidence from LP_Prolog_{Success_Types,Success_Transfer,
Numeric_Row,Context,Context_Module,Triple}_XML; schema validity is not proof checking.
"""
import copy

def extend(s, cut, node, element, sequence, group):
    ns = '{http://www.w3.org/2001/XMLSchema}'
    many = dict(minOccurs='0', maxOccurs='unbounded')
    def typ(name): return node(node(s, 'complexType', name=name), 'sequence')
    def choice(name): return node(node(s, 'group', name=name), 'choice')
    def rows(p, name, item, kind): element(sequence(p, name), item, kind, **many)
    def groups(p, name, ref): group(sequence(p, name), ref, **many)
    def vars(p, name): rows(p, name, 'var', 'xs:string')
    def nat(p, name): element(p, name, 'xs:nonNegativeInteger')
    def term(p, count=1):
        for _ in range(count):group(p, 'lp6CutTerm')
    def expr(p, count=1):
        for _ in range(count):group(p, 'lp6IntegerExpression')
    def links(p, count=1): element(p, 'link', 'lp6CutLink', minOccurs=str(count), maxOccurs=str(count))
    def continuation(p):
        groups(p, 'goals', 'lp6CutGoal'); groups(p, 'active', 'lp6CutTerm')
        element(p, 'returnState', 'lp6CutReturnState')
    a=typ('lp6PrologSuccessAtom');element(a,'predicate','xs:string');groups(a,'arguments','lp6CutTerm')
    g=choice('lp6PrologSuccessGuard')
    for tag in ['integerGuard','opaqueGuard']: term(sequence(g,tag))
    term(sequence(g,'evaluationGuard'),2)
    a=sequence(g,'numericSuccessGuard');nat(a,'comparison');term(a,2)
    g=choice('lp6PrologIntegerFact')
    for tag,fields in [('guardFact',['guard']),('helperFact',['call','argument'])]:
        a=sequence(g,tag)
        for f in fields:nat(a,f)
        element(a,'var','xs:string')
    a=sequence(g,'evaluationFact');nat(a,'guard');expr(a);element(a,'result','xs:string')
    g=choice('lp6PrologIntegerOutput');element(g,'var','xs:string');element(g,'integer','xs:integer')
    g=choice('lp6PrologTransferFact')
    a=sequence(g,'inputFact');nat(a,'argument');element(a,'var','xs:string')
    group(sequence(g,'baseFact'),'lp6PrologIntegerFact')
    a=sequence(g,'helperTransferFact')
    for f in ['call','rule','argument']:nat(a,f)
    element(a,'var','xs:string');groups(a,'inputs','lp6PrologIntegerOutput')
    a=typ('lp6PrologTransferContext')
    for f in ['required','outputs']:rows(a,f,'position','xs:nonNegativeInteger')
    a=typ('lp6PrologTransferSummary');element(a,'predicate','xs:string');nat(a,'arity');rows(a,'contexts','context','lp6PrologTransferContext')
    a=typ('lp6PrologSuccessClause');element(sequence(a,'head'),'atom','lp6PrologSuccessAtom');rows(a,'body','atom','lp6PrologSuccessAtom');groups(a,'guards','lp6PrologSuccessGuard')
    a=typ('lp6PrologTransferReceipt');groups(a,'facts','lp6PrologTransferFact');groups(a,'outputs','lp6PrologIntegerOutput')
    a=typ('lp6PrologTransferProof');rows(a,'contexts','context','lp6PrologTransferReceipt')
    a=typ('lp6PrologTransferContract');rows(a,'summaries','summary','lp6PrologTransferSummary');rows(a,'successProgram','clause','lp6PrologSuccessClause');rows(a,'proofs','clause','lp6PrologTransferProof')
    g=choice('lp6PrologComparison')
    for tag in ['less','lessEqual','equal','notEqual']:element(g,tag,'lp6CutEmpty')
    g=choice('lp6PrologReturnShape')
    for tag in ['any','ground']:element(g,tag,'lp6CutEmpty')
    nat(g,'node')
    a=typ('lp6PrologShapeProduction');group(sequence(a,'symbol'),'lp6CutSymbol');groups(a,'arguments','lp6PrologReturnShape')
    a=typ('lp6PrologShapeNode');element(a,'production','lp6PrologShapeProduction',**many)
    g=choice('lp6PrologObservation')
    for tag in ['integerGuard','groundGuard','comparisonGuard']:term(sequence(g,tag))
    for tag in ['sourceEquation','evaluationGuard']:term(sequence(g,tag),2)
    a=sequence(g,'returnShape');rows(a,'grammar','shapeNode','lp6PrologShapeNode');group(sequence(a,'shape'),'lp6PrologReturnShape');term(sequence(a,'term'))
    a=typ('lp6PrologSourceContext');rows(a,'facts','atom','lp6PrologSuccessAtom');groups(a,'guards','lp6PrologSuccessGuard');groups(a,'observations','lp6PrologObservation')
    g=choice('lp6PrologContextAction');group(sequence(g,'cut'),'lp6CutReturnAction')
    a=sequence(g,'integerTest');term(a);continuation(a);links(a,2)
    a=sequence(g,'integerComparison');vars(a,'known');element(a,'predicate','xs:string');group(a,'lp6PrologComparison');element(a,'reversed','xs:boolean');term(a,2);expr(a,2);continuation(a);links(a,2)
    a=sequence(g,'integerEvaluation');vars(a,'known');expr(a);term(a,2);continuation(a);element(a,'resultVariable','xs:string');nat(a,'activePrefix');nat(a,'clausePrefix');groups(a,'goals','lp6CutGoal');group(a,'lp6CutCoverage');groups(a,'outputs','lp6CutTerm');links(a,2)
    for tag,known,result,action in [('stagedIntegerEvaluation',True,True,True),('constantIntegerEvaluation',False,False,True),('normalizedIntegerEvaluation',True,True,False),('normalizedConstantIntegerEvaluation',False,False,False)]:
        a=sequence(g,tag)
        if known:vars(a,'known')
        expr(a);term(a,2);continuation(a)
        if result:element(a,'resultVariable','xs:string')
        links(a)
        if action:group(a,'lp6CutReturnAction')
    a=sequence(g,'identityTest');element(a,'predicate','xs:string');term(a,2);continuation(a);links(a,2)
    a=sequence(g,'finiteComparison');element(a,'predicate','xs:string');group(a,'lp6PrologComparison');element(a,'reversed','xs:boolean');term(a,2);continuation(a);links(a,3)
    a=sequence(g,'trimBarriers');element(a,'returnState','lp6CutReturnState',minOccurs='2',maxOccurs='2');links(a)
    rows(sequence(g,'parallelAlternatives'),'links','link','lp6CutLink')
    a=typ('lp6PrologTyping');group(a,'lp6PrologTransferFact',**many)
    a=typ('lp6PrologRank');group(sequence(a,'symbol'),'lp6CutSymbol');nat(a,'value')
    a=typ('lp6PrologEstablishedControl');element(a,'program','lp6CutProgram');nat(a,'fuel');nat(a,'root');rows(a,'nodes','node','lp6CutNode');rows(a,'returnStates','returnState','lp6CutReturnState');rows(a,'contexts','sourceContext','lp6PrologSourceContext');rows(a,'typings','facts','lp6PrologTyping');element(a,'prologSuccessTransferContract','lp6PrologTransferContract');group(sequence(a,'returnSymbol'),'lp6CutSymbol');nat(a,'returnArity')
    ac=node(sequence(a,'actions'),'choice',**many);element(ac,'boundary','lp6CutEmpty');group(ac,'lp6PrologContextAction')
    rows(a,'residual','clause','lp6CutResidualClause');rows(a,'ranks','rank','lp6PrologRank')
    region=copy.deepcopy(cut.find(ns+"complexType[@name='lp6TripleRegion']"));region.set('name','lp6PrologTripleRegion')
    first=region.find(ns+'sequence')[0];first.set('name','prologContextControl');first.set('type','lp6PrologEstablishedControl');s.append(region)
    a=typ('lp6PrologSourceReturnModel');rows(a,'predicates','predicate','xs:string');element(a,'prologSuccessTransferContract','lp6PrologTransferContract')
    a=typ('lp6PrologSourceIntegerReturn');element(a,'sourceReturnModel','lp6PrologSourceReturnModel');groups(a,'facts','lp6PrologTransferFact');vars(a,'integers')
    a=typ('lp6PrologSourceGroundReturn');element(a,'sourceReturnModel','lp6PrologSourceReturnModel');rows(a,'groundModes','groundMode','lp6CutGroundMode');vars(a,'ground')
    g=choice('lp6PrologTripleComponent');element(g,'prologTripleRegion','lp6PrologTripleRegion')
    a=sequence(g,'prologTripleSplit');rows(a,'staticPredicates','signature','lp6PrologSignature');element(a,'tripleSplit','lp6TripleSplit')
    for kind in ['Integer','Ground']:
        a=sequence(g,'prologTriple'+kind+'Split');element(a,'tripleSplit','lp6TripleSplit');element(a,'source'+kind+'Return','lp6PrologSource'+kind+'Return')
    proof=copy.deepcopy(cut.find(ns+"element[@name='lpCutSEGDependencyTriplesProof']"));proof.set('name','prologEstablishedSEGDependencyTriplesProof')
    seq=proof.find(ns+'complexType/'+ns+'sequence')
    transfer=element(seq,'prologSuccessTransferContract','lp6PrologTransferContract');seq.remove(transfer);seq.insert(4,transfer)
    contexts=sequence(seq,'contexts');element(contexts,'sourceContext','lp6PrologSourceContext',**many)
    outer=contexts.getparent().getparent();seq.remove(outer);seq.insert(5,outer)
    for n in proof.iter(ns+'group'):
        if n.get('ref')=='lp6TripleComponent':n.set('ref','lp6PrologTripleComponent')
    s.append(proof)

    # The ordinary contextual certificate carries one module, whose source
    # program is supplied only by the CPF input envelope.
    context=sequence(s,'prologContextDependencyTriplesProof')
    control=s.find(ns+"complexType[@name='lp6PrologEstablishedControl']/"+ns+'sequence')
    for field in control:
        if field.get('name') not in ['program','ranks']:
            context.append(copy.deepcopy(field))
    # Ordinary modules have no boundary rows. Normalization forms retain their
    # syntax, but the mathematical ordinary-module checker rejects them.
    actions=context.find(ns+"element[@name='actions']/"+ns+'complexType/'+ns+'sequence')
    for field in list(actions):actions.remove(field)
    group(actions,'lp6PrologContextAction',**many)
    for tag in ['predicateEncoding','dataEncoding']:
        rows(context,tag,'encoding','lp6CutEncoding')
    node(context,'element',ref='certificationProblem')

    # Composed contextual actions retain ordinary module rows and add a full
    # prefix/continuation split with independently checked module tables.
    module=typ('lp6PrologContextModuleData')
    for field in context:
        if field.get('name') in ['nodes','returnStates','contexts','typings','returnSymbol','returnArity','actions']:
            module.append(copy.deepcopy(field))
    composed=choice('lp6PrologContextComposedAction')
    group(composed,'lp6PrologContextAction')
    split=sequence(composed,'returnSplit')
    route=sequence(sequence(split,'routing'),'route')
    for key,value in many.items():route.getparent().getparent().set(key,value)
    element(route,'var','xs:string');nat(route,'index')
    rows(split,'projection','index','xs:nonNegativeInteger')
    groups(split,'prefix','lp6CutGoal');groups(split,'continuation','lp6CutGoal')
    groups(split,'interface','lp6CutTerm')
    element(split,'contextModule','lp6PrologContextModuleData');links(split)
    vars(split,'returnVariables')
    element(split,'contextModule','lp6PrologContextModuleData');links(split)
    proof=copy.deepcopy(context.getparent().getparent());proof.set('name','prologContextComposedDependencyTriplesProof')
    for field in proof.iter():
        if field.get('ref')=='lp6PrologContextAction':field.set('ref','lp6PrologContextComposedAction')
    s.append(proof)

    constructor=copy.deepcopy(s.find(ns+"element[@name='prologEstablishedSEGDependencyTriplesProof']"))
    constructor.set('name','prologEstablishedSEGConstructorTriplesProof')
    s.append(constructor)
