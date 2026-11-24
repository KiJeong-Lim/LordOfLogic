module LoL.Proof.Protocol where

import Control.Monad (unless)
import Data.Char (isControl)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified LoL.Proof.Json as Json

data Reference
    = Reference
        { referenceDocument    :: String
        , referenceIncarnation :: Integer
        , referenceRevision    :: Integer
        , referenceState       :: Integer
        }
    deriving (Eq, Show)

data Request
    = Request
        { requestId   :: Integer
        , requestBody :: RequestBody
        }
    deriving (Eq, Show)

data RequestBody
    = Open String Integer FilePath String
    | Append Reference Integer String
    | Replace Reference Integer String
    | Next Reference
    | Show Reference
    | Undo Reference Integer
    | Cancel Integer
    | Close Reference
    | Shutdown
    deriving (Eq, Show)

protocolVersion :: Integer
protocolVersion = 2

maximumId :: Integer
maximumId = 9007199254740991

decodeRequest :: String -> Either String Request
decodeRequest source = either (Left . snd) Right (decodeRequestWithId source)

decodeRequestWithId :: String -> Either (Maybe Integer, String) Request
decodeRequestWithId source = case Json.decode source of
    Left message -> Left (Nothing, message)
    Right value -> case request value of
        Left message -> Left (identity value, message)
        Right accepted -> Right accepted
    where
    identity (Json.Object fields) = case Map.lookup "id" fields of
        Just (Json.Integer value)
            | value > 0 && value <= maximumId -> Just value
        _ -> Nothing
    identity _ = Nothing
    request (Json.Object fields) = do
        version <- number fields "protocol"
        unless (version == protocolVersion) (Left "Unsupported protocol version; expected 2.")
        identity <- number fields "id"
        unless (identity > 0) (Left "Request IDs must be positive integers.")
        method <- string fields "method"
        body <- case method of
            "open" -> do
                exact fields ["document", "revision", "path", "source"]
                name <- document fields
                revision <- number fields "revision"
                path <- string fields "path"
                unless (not (null path) && '\0' `notElem` path) (Left "The document path must be nonempty and contain no NUL.")
                Open name revision path <$> string fields "source"
            "append" -> do
                exact fields (referenceFields ++ ["nextRevision", "source"])
                current <- reference fields
                revision <- number fields "nextRevision"
                unless (revision > referenceRevision current) (Left "The appended document revision must increase.")
                Append current revision <$> string fields "source"
            "replace" -> do
                exact fields (referenceFields ++ ["nextRevision", "source"])
                current <- reference fields
                revision <- number fields "nextRevision"
                unless (revision > referenceRevision current) (Left "The replacement document revision must increase.")
                Replace current revision <$> string fields "source"
            "next" -> exact fields referenceFields >> Next <$> reference fields
            "show" -> exact fields referenceFields >> Show <$> reference fields
            "undo" -> do
                exact fields (referenceFields ++ ["target"])
                Undo <$> reference fields <*> number fields "target"
            "cancel" -> do
                exact fields ["target"]
                target <- number fields "target"
                unless (target > 0 && target < identity) (Left "Cancellation must target an earlier positive request ID.")
                return (Cancel target)
            "close" -> exact fields referenceFields >> Close <$> reference fields
            "shutdown" -> exact fields [] >> return Shutdown
            _ -> Left ("Unknown protocol method: " ++ Json.diagnosticName method)
        return (Request identity body)
    request _ = Left "A protocol request must be a JSON object."
    referenceFields = ["document", "incarnation", "revision", "state"]
    reference fields = do
        name <- document fields
        incarnation <- number fields "incarnation"
        unless (incarnation > 0) (Left "The document incarnation must be a positive open request ID.")
        Reference name incarnation <$> number fields "revision" <*> number fields "state"
    document fields = do
        name <- string fields "document"
        unless (not (null name) && length name <= 256 && all (not . isControl) name) (Left "A document ID must contain 1 to 256 non-control characters.")
        return name
    string fields name = case Map.lookup name fields of
        Just (Json.String value) -> Right value
        _ -> Left ("Expected a string field: " ++ name)
    number fields name = case Map.lookup name fields of
        Just (Json.Integer value)
            | value >= 0 && value <= maximumId -> Right value
        _ -> Left ("Expected an integer from 0 to 9007199254740991: " ++ name)
    exact fields additions = unless (Map.keysSet fields == Set.fromList (["protocol", "id", "method"] ++ additions)) (Left "The request contains missing or unknown fields.")

reply :: Maybe Integer -> String -> [(String, Json.Value)] -> Json.Value
reply identity status fields = Json.object ([ ("protocol", Json.Integer protocolVersion), ("id", maybe Json.Null Json.Integer identity), ("status", Json.String status)] ++ fields)

failure :: Maybe Integer -> String -> String -> Json.Value
failure identity code message = reply identity "error" [("error", Json.object [("code", Json.String code), ("message", Json.String message)])]

referenceJson :: Reference -> [(String, Json.Value)]
referenceJson reference =
    [ ("document", Json.String (referenceDocument reference))
    , ("incarnation", Json.Integer (referenceIncarnation reference))
    , ("revision", Json.Integer (referenceRevision reference))
    , ("state", Json.Integer (referenceState reference))
    ]
