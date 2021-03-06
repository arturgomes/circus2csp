{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-  Author: Tobias C. Rittweiler and Florian Haftmann, TU Muenchen

Adaption tables and their application.
-}

module Importer.Adapt (Adaption(..), AdaptionTable(AdaptionTable),
  readAdapt, makeAdaptionTable_FromHsModule, extractHskEntries,
  adaptGlobalEnv, adaptModules
) where

import Importer.Library
import qualified Importer.AList as AList
import Data.Maybe (mapMaybe, fromMaybe, catMaybes, isJust)
import Data.List (partition, sort, group)

import Control.Monad.State (State, get, put, foldM, evalState, runState, liftM2)

import System.FilePath (combine)

import qualified Importer.Msg as Msg
import qualified Importer.Ident_Env as Ident_Env

import qualified Language.Haskell.Exts as Hsx
import qualified Importer.Hsx as Hsx
import qualified Importer.Isa as Isa


{- Fundamental data structures -}

data RawClassInfo = RawClassInfo
    { superclasses :: [String],
      methods      :: [(String, String)],
      classVar     :: String
    }

data OpKind = Type
            | Variable
            | Function
            | RawHskOp          -- placeholder
            | UnaryOp Int
            | InfixOp Assoc Int
            | Class RawClassInfo

data Assoc = RightAssoc | LeftAssoc | NoneAssoc

data AdaptionEntry = Haskell String OpKind
                   | Isabelle String OpKind

data Adaption = Adaption {
  rawAdaptionTable :: [(AdaptionEntry, AdaptionEntry)],
  reservedKeywords :: [String],
  usedConstNames :: [String],
  usedThyNames :: [String],
  preludeFile :: FilePath
}

data AdaptionTable = AdaptionTable [(Ident_Env.Identifier, Ident_Env.Identifier)]


{- Haskell Prelude data -}

hsk_infix_ops :: [(String, OpKind)]
hsk_infix_ops = [
  ("Prelude.(.)",  InfixOp RightAssoc 9),
  ("Prelude.(!!)", InfixOp LeftAssoc 9),
  ("Prelude.(^)",  InfixOp RightAssoc 8),
  ("Prelude.(^^)",  InfixOp RightAssoc 8),
  ("Prelude.(**)",  InfixOp RightAssoc 8),
  ("Prelude.(*)",  InfixOp LeftAssoc 7),
  ("Prelude.(/)",  InfixOp LeftAssoc 7),
  ("Prelude.quot",  InfixOp LeftAssoc 7),
  ("Prelude.rem",  InfixOp LeftAssoc 7),
  ("Prelude.div",  InfixOp LeftAssoc 7),
  ("Prelude.mod",  InfixOp LeftAssoc 7),
  ("Prelude.(+)",  InfixOp LeftAssoc 6),
  ("Prelude.(-)",  InfixOp LeftAssoc 6),
  ("Prelude.(:)",  InfixOp RightAssoc 5),
  ("Prelude.(++)", InfixOp RightAssoc 5),
  ("Prelude.(==)", InfixOp NoneAssoc 4),
  ("Prelude.(/=)", InfixOp NoneAssoc 4),
  ("Prelude.(<)",  InfixOp NoneAssoc 4),
  ("Prelude.(<=)", InfixOp NoneAssoc 4),
  ("Prelude.(>=)", InfixOp NoneAssoc 4),
  ("Prelude.(>)",  InfixOp NoneAssoc 4),
  ("Prelude.elem",  InfixOp NoneAssoc 4),
  ("Prelude.notElem",  InfixOp NoneAssoc 4),
  ("Prelude.(&&)", InfixOp LeftAssoc 3),
  ("Prelude.(||)", InfixOp LeftAssoc 2),
  ("Prelude.(>>)", InfixOp LeftAssoc 1),
  ("Prelude.(>>=)", InfixOp LeftAssoc 1),
  ("Prelude.(=<<)", InfixOp RightAssoc 1),
  ("Prelude.($)", InfixOp RightAssoc 0),
  ("Prelude.($!)", InfixOp RightAssoc 0),
  ("Prelude.seq", InfixOp RightAssoc 0)]

{- Reading adaption file -}

readError :: forall a. FilePath -> String -> a
readError file msg =
  error ("An error occurred while reading adaption file \"" ++ file ++ "\": " ++ msg)

parseAdapt :: FilePath -> IO [Hsx.Decl]
parseAdapt file = do
  result <- Hsx.parseFile file
    `catchIO` (\ioError-> readError file (show ioError))
  case result of
    Hsx.ParseFailed loc msg ->
      readError file (Msg.failed_parsing loc msg)
    Hsx.ParseOk (Hsx.Module _ _ _ _ _ _ decls) ->
      return decls

indexify :: [Hsx.Decl] -> [(String, Hsx.Exp)]
indexify decls = fold idxify decls [] where
  idxify (Hsx.PatBind _ (Hsx.PVar (Hsx.Ident name)) _ (Hsx.UnGuardedRhs rhs) _) xs =
      (name, rhs) : xs
  idxify _ xs = xs

evaluateString :: Hsx.Exp -> String
evaluateString (Hsx.Lit (Hsx.String s)) = s

evaluateList :: (Hsx.Exp -> a) -> Hsx.Exp -> [a]
evaluateList eval (Hsx.List ts) = map eval ts

evaluatePair :: (Hsx.Exp -> a) -> (Hsx.Exp -> b) -> Hsx.Exp -> (a, b)
evaluatePair eval1 eval2 (Hsx.Tuple [t1, t2]) = (eval1 t1, eval2 t2)

evaluateEntryClass :: Hsx.Exp -> RawClassInfo
evaluateEntryClass (Hsx.Paren (Hsx.RecConstr (Hsx.UnQual (Hsx.Ident "RawClassInfo"))
  [Hsx.FieldUpdate (Hsx.UnQual (Hsx.Ident "superclasses")) superclasses,
    Hsx.FieldUpdate (Hsx.UnQual (Hsx.Ident "classVar")) classVar,
      Hsx.FieldUpdate (Hsx.UnQual (Hsx.Ident "methods")) methods])) =
  RawClassInfo {
    superclasses = evaluateList evaluateString superclasses,
    classVar = evaluateString classVar,
    methods = evaluateList (evaluatePair evaluateString evaluateString) methods }

evaluateEntryKind :: Hsx.Exp -> OpKind
evaluateEntryKind (Hsx.Paren (Hsx.App (Hsx.Con (Hsx.UnQual (Hsx.Ident "Class"))) cls)) =
  Class (evaluateEntryClass cls)
evaluateEntryKind (Hsx.Con (Hsx.UnQual (Hsx.Ident "Type"))) = Type
evaluateEntryKind (Hsx.Con (Hsx.UnQual (Hsx.Ident "Function"))) = Function
evaluateEntryKind (Hsx.Paren (Hsx.App (Hsx.App (Hsx.Con (Hsx.UnQual (Hsx.Ident "InfixOp")))
  (Hsx.Con (Hsx.UnQual (Hsx.Ident assc)))) (Hsx.Lit (Hsx.Int pri)))) =
    InfixOp assoc (fromInteger pri) where
    assoc = case assc of
      "LeftAssoc" -> LeftAssoc
      "RightAssoc" -> RightAssoc
      "NoneAssoc" -> NoneAssoc

evaluateEntry :: Hsx.Exp -> AdaptionEntry
evaluateEntry (Hsx.App (Hsx.App (Hsx.Con (Hsx.UnQual (Hsx.Ident kind))) (Hsx.Lit (Hsx.String name))) entry)
  | (kind == "Haskell") = Haskell name (evaluateEntryKind entry)
  | (kind == "Isabelle") = Isabelle name (evaluateEntryKind entry)

evaluate dir decls = Adaption {
  rawAdaptionTable = evaluateList (evaluatePair evaluateEntry evaluateEntry)
    (lookupFunbind "raw_adaption_table"),
  reservedKeywords = lookupStringList "reserved_keywords",
  usedConstNames = lookupStringList "used_const_names",
  usedThyNames = lookupStringList "used_thy_names",
  preludeFile = combine dir "Prelude.thy" } where
    lookupFunbind name = case lookup name decls of
      Nothing -> error ("No entry for " ++ name ++ " in adaption file")
      Just rhs -> rhs
    lookupStringList name = evaluateList evaluateString (lookupFunbind name)

readAdapt :: FilePath -> IO Adaption
readAdapt dir = do
  decls <- parseAdapt (combine dir "Generated_Adapt.hs")
  return (evaluate dir (indexify decls))


{- Building adaption table -}

mkAdaptionTable :: Adaption -> AdaptionTable
mkAdaptionTable adapt = AdaptionTable
  $ map (\(hEntry, iEntry) -> (parseEntry hEntry, parseEntry iEntry))
      (check_raw_adaption_table (rawAdaptionTable adapt))

extractHskEntries (AdaptionTable mapping) = map fst mapping
extractIsaEntries (AdaptionTable mapping) = map snd mapping

-- Our predefined `adaptionTable' contains entries for all things that
-- may possibly get adapted; a haskell source file may, however, define
-- their own variants of the Prelude stuff (e.g. define its own `map'.)
--
-- Hence, we have to remove entries from `adaptionTable' which are
-- defined in one of the source files.
makeAdaptionTable_FromHsModule :: Adaption -> Ident_Env.GlobalE -> [Hsx.Module] -> AdaptionTable
makeAdaptionTable_FromHsModule adapt env hsmodules = let
  adaptionTable = mkAdaptionTable adapt
  initial_class_env = makeGlobalEnv_FromAdaptionTable
    (filterAdaptionTable (Ident_Env.isClass . fst) adaptionTable)
  tmp_env = Ident_Env.unionGlobalEnvs initial_class_env env
  defined_names = concatMap (extractDefNames tmp_env) hsmodules
  extractDefNames :: Ident_Env.GlobalE -> Hsx.Module -> [String]
  extractDefNames globalEnv (Hsx.Module _ m _ _ _ _ decls) =
    mapMaybe (\n -> let m'   = Ident_Env.fromHsk m
                        n'   = Ident_Env.fromHsk n
                        ids  = Ident_Env.lookupIdentifiers_OrLose m' n' globalEnv
                        name = Ident_Env.nameOf . Ident_Env.lexInfoOf
                    in  case filter Ident_Env.isType ids of
                                []                       -> Just $ name (head ids)
                                [id] | Ident_Env.isInstance id -> Just $ name id
                                     | otherwise         -> Nothing)
              $ concatMap Hsx.extractBindingNs decls
  in filterAdaptionTable (\(from, to) -> let
    fromN = Ident_Env.nameOf (Ident_Env.lexInfoOf from)
    toN = Ident_Env.nameOf (Ident_Env.lexInfoOf to)
    in fromN `notElem` defined_names && toN `notElem` defined_names) adaptionTable

makeGlobalEnv_FromAdaptionTable :: AdaptionTable -> Ident_Env.GlobalE
makeGlobalEnv_FromAdaptionTable adaptionTable
    = Ident_Env.makeGlobalEnv importNothing exportAll (extractHskEntries adaptionTable)
    where importNothing = const []
          exportAll     = const True

filterAdaptionTable :: ((Ident_Env.Identifier, Ident_Env.Identifier) -> Bool) -> AdaptionTable -> AdaptionTable
filterAdaptionTable predicate (AdaptionTable entries)
    = AdaptionTable (filter predicate entries)


-- Check the Raw Adaption Table for consistency; prohibit duplicate
-- entries, and ensure that class methods have their own entry as
-- function or op.
--
check_raw_adaption_table :: [(AdaptionEntry, AdaptionEntry)] -> [(AdaptionEntry, AdaptionEntry)]
check_raw_adaption_table tbl
    = let (hsk_entries, _)   = unzip tbl
          names              = [ n | Haskell n _ <- hsk_entries ]
          methods            = concatMap (\(Haskell _ (Class (RawClassInfo { methods = m }))) -> fst (unzip m))
                                 $ filter isClassEntry hsk_entries
          functions          = extract_functionoid_names hsk_entries
          missing_fn_entries = filter (`notElem` functions) methods
      in
        if (has_duplicates names)
        then error ("Duplicates in Raw Adaption Table found: "
                    ++ show (filter (flip (>) 1 . length) (group (sort names))))
        else if not (null missing_fn_entries)
             then error ("Inconsistency in Raw Adaption Table: The following methods\n"
                         ++ "don't have a Function entry: " ++ show missing_fn_entries)
             else tbl

    where
      extract_functionoid_names [] = []
      extract_functionoid_names (e:rest_entries)
          = case e of
              Haskell n Function      -> n : extract_functionoid_names rest_entries
              Haskell n RawHskOp      -> n : extract_functionoid_names rest_entries
              Haskell n (UnaryOp _)   -> n : extract_functionoid_names rest_entries
              Haskell n (InfixOp _ _) -> n : extract_functionoid_names rest_entries
              _                       -> extract_functionoid_names rest_entries

      isClassEntry (Haskell _ (Class _))   = True
      isClassEntry _                       = False

explode_identifier :: String -> [String]
explode_identifier = slice ((==) '.')

parseEntry :: AdaptionEntry -> Ident_Env.Identifier

parseEntry (Haskell raw_identifier op)
    = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
          op' = (case op of Function -> fromMaybe Function (lookup raw_identifier hsk_infix_ops)
                            etc      -> etc)
      in makeIdentifier op' moduleID identifierID ([], Ident_Env.TyNone)
parseEntry (Isabelle raw_identifier op)
    -- the raw identifier may look like "Datatype.option.None", where
    -- "Datatype" is the ModuleID, and "None" is the real identifier,
    -- and "option" basically noisy garbage.
    = let (moduleID, identifierID) = parseRawIdentifier raw_identifier
          moduleID'                = (case explode_identifier moduleID of
                                        []  -> moduleID
                                        m:_ -> m)
      in makeIdentifier op moduleID' identifierID ([], Ident_Env.TyNone)

parseRawIdentifier :: String -> (String, String)
parseRawIdentifier string
    = if '(' `elem` string
      then let (modul, identifier) = break (== '(') string -- "Prelude.(:)"
           in assert (last modul == '.' &&
                      last identifier == ')')
                 $ (init modul, tail (init identifier))
      else let parts      = explode_identifier string
               identifier = last parts
               modul      = separate '.' (init parts)
           in (modul, identifier)

makeIdentifier :: OpKind -> Ident_Env.ModuleID -> Ident_Env.IdentifierID -> ([(Ident_Env.Name, [Ident_Env.Name])], Ident_Env.Type) -> Ident_Env.Identifier
makeIdentifier Variable m identifier t
    = Ident_Env.Constant $ Ident_Env.Variable $ Ident_Env.makeLexInfo m identifier t
makeIdentifier Function m identifier t
    = Ident_Env.Constant $ Ident_Env.Function $ Ident_Env.makeLexInfo m identifier t
makeIdentifier (UnaryOp prio) m identifier t
    = Ident_Env.Constant $ Ident_Env.UnaryOp (Ident_Env.makeLexInfo m identifier t) prio
makeIdentifier (InfixOp assoc prio) m identifier t
    = Ident_Env.Constant $ Ident_Env.InfixOp (Ident_Env.makeLexInfo m identifier t) (transformAssoc assoc) prio
makeIdentifier (Class classinfo) m identifier t
    = let supers  = map (Ident_Env.UnqualName . snd . parseRawIdentifier) (superclasses classinfo)
          meths   = map (\(n, tstr) -> let t = Ident_Env.typscheme_of_hsk_typ (parseType tstr)
                                       in makeTypeAnnot (Ident_Env.makeLexInfo m n t))
                        (methods classinfo)
          classV  = Ident_Env.UnqualName (classVar classinfo)
      in
        Ident_Env.TypeDecl $ Ident_Env.Class (Ident_Env.makeLexInfo m identifier t)
                             (Ident_Env.makeClassInfo supers meths classV)
makeIdentifier Type m identifier t
    = Ident_Env.TypeDecl $ Ident_Env.Data (Ident_Env.makeLexInfo m identifier t) []

makeTypeAnnot :: Ident_Env.LexInfo -> Ident_Env.Identifier
makeTypeAnnot lexinfo = Ident_Env.Constant (Ident_Env.TypeAnnotation lexinfo)

parseType :: String -> Hsx.Type
parseType string = case Hsx.parseFileContents ("__foo__ :: " ++ string) of
  (Hsx.ParseOk (Hsx.Module _ _ _ _ _ _ [Hsx.TypeSig _ _ t])) -> t

transformAssoc :: Assoc -> Ident_Env.Assoc
transformAssoc RightAssoc = Ident_Env.AssocRight
transformAssoc LeftAssoc  = Ident_Env.AssocLeft
transformAssoc NoneAssoc  = Ident_Env.AssocNone


{- Applying adaptions -}

data AdptState = AdptState { oldGlobalEnv     :: Ident_Env.GlobalE,
                             adaptedGlobalEnv :: Ident_Env.GlobalE,
                             adaptionTable    :: AdaptionTable,
                             currentModuleID  :: Maybe Ident_Env.ModuleID
                           }

type AdaptM v = State AdptState v

getAdptState :: AdaptM AdptState
getAdptState = do s <- get; return s

query :: (AdptState -> x) -> AdaptM x
query slot = do s <- getAdptState; return (slot s)

set :: (AdptState -> AdptState) -> AdaptM ()
set update = do s <- getAdptState; put (update s); return ()

shadow :: [Ident_Env.Name] -> AdaptM ()
shadow names
    = set (\state
               -> let (AdaptionTable mappings) = adaptionTable state
                      -- Functions (especially data constructors, like []) can't
                      -- be locally bound, so we must not shadow them.
                      (fun_mappings, rest_mappings)
                          = partition (\(id,_) -> Ident_Env.isInfixOp id || Ident_Env.isFunction id )
                              mappings
                  in state { adaptionTable
                                 = AdaptionTable $
                                     fun_mappings ++
                                     filter ((`notElem` names) . Ident_Env.identifier2name . fst)
                                        rest_mappings
                           })

-- shadowing [a, b, c] $ body
--   with appropriate a, b, c.
--
-- Inside `body', do not adapt names `a', `b', and `c'.
--
shadowing :: [Isa.Name] -> AdaptM v -> AdaptM v
shadowing names body
    = do old_tbl <- query adaptionTable
         shadow (map Ident_Env.fromIsa names)
         r <- body
         set (\state -> state { adaptionTable = old_tbl })
         return r

-- nested_binding [(a, computeA), (b, computeB), (c, computeC)] $
--   \([a', b', c']) -> body
--
--     with appropriate a, b, c
-- and with a', b', c' being the results of computeA, computeB, computeC.
--
-- LET like binding construct: while computing `computeB', `a' is shadowed,
-- while computing `computeC', `a' and `b' are shadowed, and so on.
--
-- Inside `body', the identifiers `a', `b' and `c' won't be adapted..
--
nested_binding :: [([Isa.Name], AdaptM b)] -> ([b] -> AdaptM v) -> AdaptM v
nested_binding [] continuation = continuation []
nested_binding bindings continuation
    = do old_tbl <- query adaptionTable
         rs      <- foldM (\result (ns,thunk) -> let ns' = map Ident_Env.fromIsa ns in
                                                 do shadow ns' ; t <- thunk
                                                    return (result ++ [t]))
                    [] bindings
         r       <- continuation rs
         set (\state -> state { adaptionTable = old_tbl })
         return r


runAdaptionWith :: AdaptM v -> AdptState -> v
runAdaptionWith adaption state
    = evalState adaption state

runAdaption :: Ident_Env.GlobalE -> Ident_Env.GlobalE -> AdaptionTable -> AdaptM v -> v
runAdaption oldEnv newEnv tbl adaption
    = runAdaptionWith adaption (AdptState { oldGlobalEnv     = oldEnv,
                                            adaptedGlobalEnv = newEnv,
                                            adaptionTable    = tbl,
                                            currentModuleID  = Nothing
                                          })


qualifyConstantName :: Ident_Env.GlobalE -> Ident_Env.ModuleID -> Ident_Env.Name -> Ident_Env.Name
qualifyConstantName globalEnv mID name
    = fromMaybe (Ident_Env.qualifyName mID name)
        $ Ident_Env.resolveConstantName globalEnv mID name

qualifyTypeName :: Ident_Env.GlobalE -> Ident_Env.ModuleID -> Ident_Env.Name -> Ident_Env.Name
qualifyTypeName globalEnv mID name
    = fromMaybe (Ident_Env.qualifyName mID name)
        $ Ident_Env.resolveTypeName globalEnv mID name


adaptGlobalEnv :: AdaptionTable -> Ident_Env.GlobalE -> Ident_Env.GlobalE
adaptGlobalEnv adaptions env = Ident_Env.updateGlobalEnv (\n ->
  case translateName adaptions n of
    Just new_id -> [new_id]
    Nothing -> adapt_type_in_identifier env adaptions n) env

adapt_type_in_identifier :: Ident_Env.GlobalE -> AdaptionTable -> Ident_Env.Name -> [Ident_Env.Identifier]
adapt_type_in_identifier globalEnv adaptions n@(Ident_Env.QualName mID _)
    = let old_ids = Ident_Env.lookupIdentifiers_OrLose mID n globalEnv
          old_lexinfos = map Ident_Env.lexInfoOf old_ids
          old_types = map Ident_Env.typschemeOf old_lexinfos
          renamings = (case adaptions of AdaptionTable mappings -> mappings)
            |> filter (Ident_Env.isClass . fst)
            |> asserting (all (Ident_Env.isClass . snd))
            |> (map . map_both) Ident_Env.identifier2name
          proto_qualify = qualifyTypeName globalEnv . Ident_Env.moduleOf
          translate_name lexinfo n = case AList.lookup renamings (proto_qualify lexinfo n) of
            Nothing -> n
            Just n' -> n'
          translate_typ lexinfo = translateEnvType adaptions (proto_qualify lexinfo)
          translate (vs, typ) lexinfo = (map (\(v, sort) -> (translate_name lexinfo v,
            map (translate_name lexinfo) sort)) vs, the_default typ (translate_typ lexinfo typ))
          new_types    = zipWith translate old_types old_lexinfos
          new_lexinfos = zipWith (\t lxinf -> lxinf {Ident_Env.typschemeOf = t}) new_types old_lexinfos
      in
        zipWith Ident_Env.updateIdentifier old_ids new_lexinfos

translateName :: AdaptionTable -> Ident_Env.Name -> Maybe Ident_Env.Identifier
translateName (AdaptionTable mappings) name =
  lookupBy (\n1 id2 -> n1 == Ident_Env.identifier2name id2) name mappings where
    lookupBy                :: (a -> b -> Bool) -> a -> [(b, c)] -> Maybe c
    lookupBy eq key []      =  Nothing
    lookupBy eq key ((x,y):xys)
        | key `eq` x        =  Just y
        | otherwise         =  lookupBy eq key xys


translateIdentifier :: AdaptionTable -> Ident_Env.Identifier -> Ident_Env.Identifier
translateIdentifier tbl id
    = case translateName tbl (Ident_Env.identifier2name id) of
        Nothing     -> id
        Just new_id -> new_id

translateEnvType :: AdaptionTable -> (Ident_Env.Name -> Ident_Env.Name) -> Ident_Env.Type -> Maybe Ident_Env.Type
translateEnvType (AdaptionTable mappings) qualify typ = let
    type_renams = mappings
      |> filter (Ident_Env.isData . fst)
      |> asserting (all (Ident_Env.isData . snd))
      |> (map . map_both) Ident_Env.identifier2name
    class_renams  = mappings
      |> filter (Ident_Env.isClass . fst)
      |> asserting (all (Ident_Env.isClass . snd))
      |> (map . map_both) Ident_Env.identifier2name
    renamings = type_renams ++ class_renams
    transl n =
      case AList.lookup renamings (qualify n) of
        Nothing -> return n
        Just n' -> put True >> return n'
    translate :: Ident_Env.Type -> State Bool Ident_Env.Type
    translate typ = case typ of
      Ident_Env.TyNone      -> return Ident_Env.TyNone
      Ident_Env.TyVar n     -> liftM Ident_Env.TyVar (transl n)
      Ident_Env.TyCon n ts  -> do n' <- transl n
                                  ts' <- mapM translate ts
                                  return (Ident_Env.TyCon n' ts')
      Ident_Env.TyFun t1 t2 -> do t1' <- translate t1
                                  t2' <- translate t2
                                  return (Ident_Env.TyFun t1' t2')
  in case runState (translate typ) False of
    (_, False) -> Nothing        -- no match found in AdaptionTable.
    (new_type, True) -> Just new_type

adaptEnvName :: Ident_Env.Name -> AdaptM Ident_Env.Name
adaptEnvName n
    = do Just mID <- query currentModuleID
         tbl      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         newEnv   <- query adaptedGlobalEnv
         case Ident_Env.lookupConstant mID n oldEnv of
           Nothing -> return n
           Just id -> let new_id       = translateIdentifier tbl id
                          new_id_name  = Ident_Env.identifier2name new_id
                      in assert (isJust (Ident_Env.lookupConstant mID new_id_name newEnv))
                           $ return new_id_name

adaptEnvType :: Ident_Env.Type -> AdaptM Ident_Env.Type
adaptEnvType t
    = do Just mID <- query currentModuleID
         adaptions      <- query adaptionTable
         oldEnv   <- query oldGlobalEnv
         let qualify = qualifyTypeName oldEnv mID
         return (fromMaybe t (translateEnvType adaptions qualify t))

adaptName :: Isa.Name -> AdaptM Isa.Name
adaptName n = do
  n' <- adaptEnvName (Ident_Env.fromIsa n)
  return (Ident_Env.toIsa n')

adaptType :: Isa.Type -> AdaptM Isa.Type
adaptType t = do t' <- adaptEnvType (Ident_Env.fromIsa t); return (Ident_Env.toIsa t')

adaptClass :: Isa.Name -> AdaptM Isa.Name
adaptClass classN = do
  Just mID <- query currentModuleID
  AdaptionTable mappings <- query adaptionTable
  let { renamings = mappings |> filter (Ident_Env.isClass . fst)
    |> asserting (all (Ident_Env.isClass . snd)) |> (map . map_both) Ident_Env.identifier2name }
  oldEnv <- query oldGlobalEnv
  let classN' = AList.lookup renamings (qualifyTypeName oldEnv mID (Ident_Env.fromIsa classN))
  let classN'' = case classN' of {
    Nothing -> classN;
    Just classN' -> Ident_Env.toIsa classN' }
  return classN''

adaptModules ::  AdaptionTable  -> Ident_Env.GlobalE -> Ident_Env.GlobalE -> [Isa.Module] -> [Isa.Module]
adaptModules adaptionTable adaptedGlobalEnv globalEnv modules =
  runAdaption globalEnv adaptedGlobalEnv adaptionTable (mapM adapt modules)


not_implemented x = error ("Adaption not implemented yet for\n  " ++ Msg.prettyShow' "thing" x)

class Adapt a where
    adapt  :: a -> AdaptM a

instance Adapt Isa.Module where

    adapt (Isa.Module thy imps cmds)
        = do old_mID <- query currentModuleID
             set (setModuleID $ Just (Ident_Env.fromIsa thy))
             cmds' <- mapM adapt cmds
             set (setModuleID old_mID)
             return (Isa.Module thy imps cmds')
        where setModuleID v state
                  = state { currentModuleID = v }

instance Adapt Isa.Function_Stmt where
    adapt (Isa.Function_Stmt kind sigs eqns) =
        do sigs' <- mapM adapt sigs
           let funNs = map Isa.name_of_type_sign (sigs ++ sigs')
           shadowing (map Isa.name_of_type_sign sigs) $
             do eqns' <- mapM (\(funN, pats, body) ->
                  do funN' <- adaptName funN
                     assert (funN `elem` funNs) $ return ()
                     pats' <- mapM adapt pats
                     shadowing (accumulate (fold add_const_names) pats') $
                       do body' <- adapt body ; return (funN', pats', body')) eqns
                return (Isa.Function_Stmt kind sigs' eqns')

instance Adapt Isa.Stmt where

    adapt (Isa.TypeSynonym aliases) = liftM Isa.TypeSynonym (mapM adpt aliases)
        where adpt (spec,typ) = liftM2 (,) (return spec) (adaptType typ)
    adapt c@(Isa.Record _ _)      = not_implemented c
    adapt c@(Isa.Comment _)          = return c

    adapt (Isa.Datatype decls) = liftM Isa.Datatype $ mapM adaptDecls decls where
      adaptDecls ((sig @ (Isa.TypeSpec tyvarNs tycoN), constrs)) = shadowing (tycoN : tyvarNs) $
        do constrs' <- mapM adaptConstr constrs
           return (sig, constrs')
      adaptConstr (name, types) =
        do types' <- mapM adaptType types
           return (name, types')

    adapt (Isa.Function function_stmt) = liftM Isa.Function (adapt function_stmt)

    adapt (Isa.Class classN supclassNs typesigs)
        = do classN'     <- adaptClass classN
             supclassNs' <- mapM adaptClass supclassNs
             typesigs'   <- mapM adapt typesigs
             return (Isa.Class classN' supclassNs' typesigs')

    adapt (Isa.Instance classN tycoN arities stmt)
        = do classN' <- adaptClass classN
             type' <- adaptType (Isa.Type tycoN (map (Isa.TVar . fst) arities))
             let (tycoN', tvars') = ((map_snd . map) Isa.dest_TVar . Isa.dest_Type) type'
             sorts' <- (mapM . mapM) adaptClass (map snd arities)
             stmt' <- mapM adapt stmt
             return (Isa.Instance classN' tycoN' (zip tvars' sorts') stmt')

instance Adapt Isa.TypeSpec where
    adapt (Isa.TypeSpec tyvarNs tycoN)
        = do (Isa.Type tycoN' tyvars') <- adaptType (Isa.Type tycoN (map Isa.TVar tyvarNs))
             return $ Isa.TypeSpec (map (\(Isa.TVar n) -> n) tyvars') tycoN'

instance Adapt Isa.TypeSign where
    adapt (Isa.TypeSign n arities t) = do
      n' <- adaptName n
      tvars' <- mapM (adaptType . Isa.TVar . fst) arities
      sorts' <- (mapM . mapM) adaptClass (map snd arities)
      t' <- adaptType t
      return (Isa.TypeSign n' (zip (map Isa.dest_TVar tvars') sorts') t')

instance Adapt Isa.Term where
    adapt (Isa.Literal lit)     = return (Isa.Literal lit)

    adapt (Isa.Const n)           = adaptConst n >>= (return . Isa.Const)
      where
        adaptConst n = do
          n' <- adaptEnvName (Ident_Env.fromIsa n)
          return (Ident_Env.toIsa n')

    adapt (Isa.Parenthesized t) = adapt t     >>= (return . Isa.Parenthesized)

    adapt (Isa.App t1 t2)       = do Just mID <- query currentModuleID
                                     oldEnv   <- query oldGlobalEnv
                                     newEnv   <- query adaptedGlobalEnv
                                     t1'      <- adapt t1
                                     t2'      <- adapt t2
                                     -- t1 may have been an InfixOp and was adapted to
                                     -- a function. In this case, we have to make sure that
                                     -- all the arguments passed to this function are
                                     -- parenthesized.
                                     let n1   = find_applied_op t1
                                     let n1'  = find_applied_op t1'
                                     case (n1, n1') of
                                       (Just n1, Just n1')
                                           -> if isInfixOp mID n1 oldEnv && not (isInfixOp mID n1' newEnv)
                                              then return $ Isa.App t1' (Isa.Parenthesized t2')
                                              else return $ Isa.App t1' t2'
                                       _   -> return (Isa.App t1' t2')
        where isInfixOp mID n env
                  = case Ident_Env.lookupConstant mID (Ident_Env.fromIsa n) env of
                      Nothing -> False
                      Just c  -> Ident_Env.isInfixOp c
              find_applied_op :: Isa.Term -> Maybe Isa.Name
              find_applied_op t
                  = case t of
                      Isa.Const n            -> Just n
                      Isa.App t1 t2        -> find_applied_op t1
                      Isa.Parenthesized t' -> find_applied_op t'
                      _                    -> Nothing -- the remaining cases are
                                                      -- too complicated, so we give up.

    adapt (Isa.If c t e)        = do c' <- adapt c ; t' <- adapt t ; e' <- adapt e
                                     return (Isa.If c' t' e')

    adapt (Isa.Abs boundN body)
        = shadowing [boundN] $
            adapt body >>= (return . Isa.Abs boundN)

    adapt (Isa.Let bindings body)
        = do pats' <- mapM adapt (map fst bindings)
             nested_binding (zipWith (\p' t -> (accumulate add_const_names p', adapt t))
                                     pats' (map snd bindings)) $
               \terms' -> do body' <- adapt body
                             return (Isa.Let (zip pats' terms') body')

    adapt (Isa.Case term patterns)
        = do term'     <- adapt term
             patterns' <- mapM (\(pat, body)
                                    -> do pat' <- adapt pat
                                          shadowing (accumulate add_const_names pat') $
                                            do body' <- adapt body
                                               return (pat', body'))
                               patterns
             return (Isa.Case term' patterns')

    adapt (Isa.ListCompr body stmts) = adpt body stmts []
      where
        adpt e [] stmts' = do e' <- adapt e; return (Isa.ListCompr e' (reverse stmts'))
        adpt e (Isa.Guard b : rest) stmts'
            = adapt b >>= (\b' -> adpt e rest (Isa.Guard b':stmts'))
        adpt e (Isa.Generator (pat, exp) : rest) stmts'
            = do pat' <- adapt pat
                 exp' <- adapt exp
                 shadowing (accumulate add_const_names pat') $
                   adpt e rest (Isa.Generator (pat', exp') : stmts')
    adapt (Isa.DoBlock pre stmts post) =
        do stmts' <- mapM adapt stmts
           return $ Isa.DoBlock pre stmts' post

instance Adapt Isa.DoBlockFragment where
    adapt (Isa.DoGenerator pat exp) = liftM2 Isa.DoGenerator (adapt pat) (adapt exp)
    adapt (Isa.DoQualifier exp) = liftM Isa.DoQualifier $ adapt exp


add_const_names :: Isa.Term -> [Isa.Name] -> [Isa.Name]
add_const_names (Isa.Const n) = insert n
add_const_names (Isa.App t1 t2) = add_const_names t1 *> add_const_names t2
add_const_names _ = id
