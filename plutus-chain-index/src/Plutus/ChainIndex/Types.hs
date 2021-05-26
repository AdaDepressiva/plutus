{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-| Misc. types used in this package
-}
module Plutus.ChainIndex.Types(
    BlockId(..)
    , Page(..)
    , PageSize(..)
    , pageOf
    , Tip(..)
    ) where

import           Data.Aeson        (FromJSON, ToJSON)
import qualified Data.Aeson        as JSON
import qualified Data.Aeson.Extras as JSON
import qualified Data.ByteString   as BS
import           Data.Default      (Default (..))
import           Data.Set          (Set)
import qualified Data.Set          as Set
import qualified Data.Text         as Text
import           GHC.Generics      (Generic)
import           Ledger.Blockchain (BlockId (..))
import           Ledger.Bytes      (LedgerBytes (..))
import           Ledger.Slot       (Slot)
import           Numeric.Natural   (Natural)
import qualified PlutusTx.Prelude  as PlutusTx

-- | Block identifier (usually a hash)
newtype BlockId = BlockId { getBlockId :: BS.ByteString }
    deriving stock (Eq, Ord, Generic)

instance Show BlockId where
    show = Text.unpack . JSON.encodeByteString . getBlockId

instance ToJSON BlockId where
    toJSON = JSON.String . JSON.encodeByteString . getBlockId

instance FromJSON BlockId where
    parseJSON v = BlockId <$> JSON.decodeByteString v

newtype PageSize = PageSize { getPageSize :: Natural }
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Default PageSize where
    def = PageSize 50

-- | Part of a collection
data Page a = Page { pageSize :: PageSize, pageNumber :: Int, totalPages :: Int, pageItems :: [a]}
    deriving stock (Eq, Ord, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | A page with the given size
pageOf :: PageSize -> Set a -> Page a
pageOf (PageSize ps) items =
    let totalPages =
            let (d, m) = Set.size items `divMod` ps'
            in if m == 0 then d else d + 1
        ps' = fromIntegral ps
    in Page
        { pageSize = PageSize ps
        , pageNumber = 1
        , totalPages
        , pageItems = take ps' $ Set.toList items
        }

-- | The tip of the chain index.
data Tip =
      TipAtGenesis
    | Tip
        { tipSlot    :: Slot -- ^ Last slot
        , tipBlockId :: BlockId -- ^ Last block ID
        , tipBlockNo :: Int -- ^ Last block number
        }
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | This mirrors the previously defined Tip which used the Last monoid definition.
instance Semigroup Tip where
    t <> TipAtGenesis = t
    _ <> t            = t

instance Monoid Tip where
    mempty = TipAtGenesis

instance Ord Tip where
    TipAtGenesis <= _            = True
    _            <= TipAtGenesis = False
    (Tip _ _ ln) <= (Tip _ _ rn) = ln <= rn
