-- Transport tests only: generated Isabelle retains mathematical checking.
import qualified Ceta.Input.Cpf6 as C
import System.Exit (die)
wrap inp ans proof = "<certificationProblem><cpfVersion>6.0</cpfVersion><lookupTables/><input>" ++ inp ++ "</input><property><termination/></property><answer><" ++ ans ++ "/></answer><proof>" ++ proof ++ "</proof></certificationProblem>"
child = wrap "<logicProgramTriplesInput><resolutionSemantics>infiniteTrees</resolutionSemantics><triples/><program/><query><name>q</name><arity>0</arity><ground/></query></logicProgramTriplesInput>" "yes" "<lpDependencyTriplesConstructorProof><returns/><fallback><name>u</name></fallback><tripleContinuations/><programContinuations/><marks/><argumentFilter/><seed><name>seed</name></seed><dpProof><pIsEmpty/></dpProof></lpDependencyTriplesConstructorProof>"
source = "<prologInput><executionProfile>iso-rational-libraries-v1</executionProfile><program/><query><predicate>0:p</predicate><modes/></query></prologInput>"
fields = "<fuel>8</fuel><chainPredicate><user>chain</user></chainPredicate><triples/><successProgram/><prologSuccessTransferContract><summaries/><successProgram/><proofs/></prologSuccessTransferContract><contexts/><roots/><components/><predicateEncoding/><dataEncoding/>"
proof body = "<prologEstablishedSEGConstructorTriplesProof>" ++ body ++ "</prologEstablishedSEGConstructorTriplesProof>"
main = do
 let valid = wrap source "yes" (proof (fields ++ child))
 case C.prologCertificate valid of
  Left e -> die e
  Right decoded -> case C.prologCertificate decoded of
    Right same | same == decoded -> return ()
    _ -> die "native transport changed"
 mapM_ (\x -> case C.prologCertificate x of Left _ -> return (); Right _ -> die "invalid established envelope accepted")
   [wrap source "no" (proof (fields ++ child)),wrap source "yes" (proof fields),wrap source "yes" (proof (fields ++ child ++ "<extra/>")),wrap source "yes" (proof (fields ++ "<certificationProblem><invalid/></certificationProblem>"))]
 putStrLn "6 established-triple transport checks passed"
