-- Strict CPF 4 data parsing. No mathematical acceptance lives in this module.
module Ceta.Input.Cpf4 (native, parseXML, renderXML, XML(..), elems, scalar, field, envelope) where
import Ceta.Input.Cpf4Grammar
import Control.Monad (guard, unless)
import Data.Char (isSpace, isAlphaNum, chr)
import Data.List (isPrefixOf, intercalate)
import Numeric (readHex)
import Text.ParserCombinators.ReadP
import Text.Read (readMaybe)

data XML = Element String [(String,String)] [XML] | Text String deriving (Eq,Show)
name = munch1 (\c -> isAlphaNum c || c `elem` "_:-.")
entity = do
 char '&'; value <- munch1 (/=';'); char ';'
 case value of
  "amp" -> return '&'; "lt" -> return '<'; "gt" -> return '>'; "quot" -> return '"'; "apos" -> return '\''
  '#':'x':xs -> case readHex xs of [(i,"")] | valid i -> return (chr i); _ -> pfail
  '#':xs -> case readMaybe xs of Just i | valid i -> return (chr i); _ -> pfail
  _ -> pfail
 where valid i = i==9 || i==10 || i==13 || (i>=32 && i<=0x10ffff && not (i>=0xd800 && i<=0xdfff))
textChar = entity <++ satisfy (\c -> c/='<' && c/='&')
quoted = do q <- satisfy (`elem` "\"'"); s <- many (entity <++ satisfy (\c->c/=q && c/='&' && c/='<')); char q; return s
attribute = do skipSpaces; n<-name; skipSpaces; char '='; skipSpaces; v<-quoted; return (n,v)
node d | d>1024 = pfail
node d = do
 char '<'; n<-name; as<-many attribute; skipSpaces
 (string "/>" >> return (Element n as [])) <++ do
  char '>'; cs<-many ((Text <$> munch1 (\c -> c/='<' && c/='&')) <++ (Text . (:[]) <$> entity) <++ node (d+1))
  string "</"; string n; skipSpaces; char '>'; return (Element n as cs)
parseXML s = case readP_to_S (skipSpaces >> optional (string "<?xml" >> munch (/='?') >> string "?>" >> skipSpaces) >> node 0 <* skipSpaces <* eof) s of
 [(n,"")] -> Right n
 _ -> Left "invalid XML document"
escape = concatMap (\c->case c of '&'->"&amp;"; '<'->"&lt;"; '>'->"&gt;"; '"'->"&quot;"; '\''->"&apos;"; _->[c])
renderXML (Text s)=escape s
renderXML (Element n as cs)="<"++n++concatMap (\(k,v)->" "++k++"=\""++escape v++"\"") as++">"++concatMap renderXML cs++"</"++n++">"
elems (Element _ [] cs) | all clean cs = Right [c | c@(Element _ _ _) <- cs]
 where clean (Text s)=all isSpace s; clean _=True
elems _ = Left "attributes or mixed content are not permitted"
scalar (Element _ [] cs) | all isText cs = Right (concat [s | Text s<-cs])
 where isText (Text _)=True; isText _=False
scalar _=Left "expected scalar"
label (Element n _ _)=n
label _=""
field n x = do cs<-elems x; case cs of [c] | label c==n -> Right c; _->Left ("expected "++n)
assert b msg=unless b (Left msg)
empty x=do cs<-elems x;assert (null cs) "expected empty element"
-- Return the input and proof only after checking all claim fields.
envelope source = do
 root<-parseXML source;assert (label root=="certificationProblem") "expected CPF document"
 cs<-elems root;assert (map label cs==["cpfVersion","lookupTables","input","property","answer","proof"]) "CPF envelope fields"
 let [version,tables,inp,prop,ans,prf]=cs
 v<-scalar version;assert (v=="4.0") "expected CPF 4.0";empty tables
 ps<-elems prop;as<-elems ans;qs<-elems prf;is<-elems inp
 case (is,ps,as,qs) of
  ([i],[p],[a],[q])->do empty p;empty a;return (i,label p,label a,q)
  _->Left "ambiguous input, property, answer or proof"

native expected ordinary source
 | not ("<" `isPrefixOf` dropWhile isSpace source) = Right source
 | otherwise = do
  (inp,prop,ans,proof)<-envelope source
  let kind=label proof
  spec<-maybe (Left "unknown certificate constructor") Right (lookup kind roots)
  assert (category spec==expected && label inp==expected++"Input") "wrong category"
  assert (prop=="termination" || (expected=="conditional" && prop=="operationalTermination")) "wrong property"
  case ordinary of Nothing->return ();Just b->assert (prop==if b then "termination" else "operationalTermination") "conditional property mismatch"
  assert (ans==if yes spec then "yes" else "no") "wrong answer"
  ins<-elems inp;ps<-elems proof
  let fs=fields spec
      inputFields=filter ((`elem` inputs spec).fst) fs
      proofFields=filter (not . (`elem` inputs spec).fst) fs
  assert (map label ins==map fst inputFields && map label ps==map fst proofFields) "missing, duplicate or reordered fields"
  vs<-mapM (\(n,t)->do x<-maybe (Left "missing field") Right (lookup n [(label x,x)|x<-ins++ps]);decode 0 (wire spec) t x) fs
  return (unwords (kind:vs)++"\n")

decode d w _ _ | d>1024 = Left "certificate nesting limit"
decode d w (Ref n) x = maybe (Left "unknown schema") (\s->decode (d+1) w s x) (lookup n types)
decode _ _ Natural x = do s<-scalar x;assert (not(null s)&&all (`elem` ['0'..'9']) s) "natural required";return s
decode _ _ Boolean x = do s<-scalar x;assert (s=="True"||s=="False") "boolean required";return s
decode _ _ StringValue x = show <$> scalar x
decode d w (ListOf t) x = do
 cs<-elems x;assert (all ((=="item").label) cs) "list item required";vs<-mapM (decode (d+1) w t) cs
 return (if w=="prefix" then unwords (show(length vs):vs) else "["++intercalate "," vs++"]")
decode d w (TupleOf fs) x = do
 vs<-decodeFields d w fs x
 return (if w=="prefix" then unwords vs else "("++intercalate "," vs++")")
decode d w (Choice cases) x = do
 cs<-elems x
 case cs of
  [c]->do
   let tag=label c
   fs<-maybe (Left "unknown constructor") Right (lookup tag cases)
   vs<-decodeFields d w fs c
   return (if w=="prefix" then unwords (tag:vs) else "("++unwords(tag:vs)++")")
  _->Left "one constructor required"
decodeFields d w fs x = do
 cs<-elems x;assert (map label cs==map fst fs) "constructor fields"
 sequence [decode (d+1) w t c | ((_,t),c)<-zip fs cs]
