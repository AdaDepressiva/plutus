{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-spec-constr #-}
-- | A basic governance contract in Plutus.
module Plutus.Contracts.Governance (
    -- $governance
      contract
    , proposalContract
    , Params(..)
    , Proposal(..)
    , Schema
    , mkTokenName
    , typedValidator
    , mkValidator
    , GovState(..)
    , Voting(..)
    , GovError
    ) where

import           Control.Lens                 (makeClassyPrisms, review)
import           Control.Monad
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.ByteString              (ByteString)
import           Data.Semigroup               (Sum (..))
import           Data.String                  (fromString)
import           Data.Text                    (Text)
import           GHC.Generics                 (Generic)
import           Ledger                       (MintingPolicyHash, POSIXTime, PubKeyHash, TokenName)
import           Ledger.Constraints           (TxConstraints)
import qualified Ledger.Constraints           as Constraints
import qualified Ledger.Interval              as Interval
import qualified Ledger.Typed.Scripts         as Scripts
import qualified Ledger.Value                 as Value
import           Plutus.Contract
import           Plutus.Contract.StateMachine (AsSMContractError, State (..), StateMachine (..), Void)
import qualified Plutus.Contract.StateMachine as SM
import qualified PlutusTx
import qualified PlutusTx.AssocMap            as AssocMap
import           PlutusTx.Prelude
import qualified Prelude                      as Haskell

-- $governance
-- * When the contract starts it produces a number of tokens that represent voting rights.
-- * Holders of those tokens can propose changes to the state of the contract and vote on them.
-- * After a certain period of time the voting ends and the proposal is rejected or accepted.

-- | The paramaters for the proposal contract.
data Proposal = Proposal
    { newLaw         :: BuiltinByteString
    -- ^ The new contents of the law
    , tokenName      :: TokenName
    -- ^ The name of the voting tokens. Only voting token owners are allowed to propose changes.
    , votingDeadline :: POSIXTime
    -- ^ The time when voting ends and the votes are tallied.
    }
    deriving stock (Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data Voting = Voting
    { proposal :: Proposal
    , votes    :: AssocMap.Map TokenName Bool
    }
    deriving stock (Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data GovState = GovState
    { law    :: BuiltinByteString
    , mph    :: MintingPolicyHash
    , voting :: Maybe Voting
    }
    deriving stock (Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

data GovInput
    = MintTokens [TokenName]
    | ProposeChange Proposal
    | AddVote TokenName Bool
    | FinishVoting
    deriving stock (Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | The endpoints of governance contracts are
--
-- * @new-law@ to create a new law and distribute voting tokens
-- * @add-vote@ to vote on a proposal with the name of the voting token and a boolean to vote in favor or against.
type Schema =
    Endpoint "new-law" ByteString
        .\/ Endpoint "add-vote" (TokenName, Bool)

-- | The governace contract parameters.
data Params = Params
    { baseTokenName  :: TokenName
    -- ^ The token names that allow voting are generated by adding an increasing number to the base token name. See `mkTokenName`.
    , initialHolders :: [PubKeyHash]
    -- ^ The public key hashes of the initial holders of the voting tokens.
    , requiredVotes  :: Integer
    -- ^ The number of votes in favor required for a proposal to be accepted.
    }

data GovError =
    GovContractError ContractError
    | GovStateMachineError SM.SMContractError
    deriving stock (Haskell.Eq, Haskell.Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

makeClassyPrisms ''GovError

instance AsContractError GovError where
    _ContractError = _GovContractError

instance AsSMContractError GovError where
    _SMContractError = _GovStateMachineError

type GovernanceMachine = StateMachine GovState GovInput

{-# INLINABLE machine #-}
machine :: Params -> GovernanceMachine
machine params = SM.mkStateMachine Nothing (transition params) isFinal where
    {-# INLINABLE isFinal #-}
    isFinal _ = False

{-# INLINABLE mkValidator #-}
mkValidator :: Params -> Scripts.ValidatorType GovernanceMachine
mkValidator params = SM.mkValidator $ machine params

typedValidator :: Params -> Scripts.TypedValidator GovernanceMachine
typedValidator = Scripts.mkTypedValidatorParam @GovernanceMachine
    $$(PlutusTx.compile [|| mkValidator ||])
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator

client :: Params -> SM.StateMachineClient GovState GovInput
client params = SM.mkStateMachineClient $ SM.StateMachineInstance (machine params) (typedValidator params)

-- | Generate a voting token name by tagging on a number after the base token name.
mkTokenName :: TokenName -> Integer -> TokenName
mkTokenName base ix = fromString (Value.toString base ++ Haskell.show ix)

{-# INLINABLE votingValue #-}
votingValue :: MintingPolicyHash -> TokenName -> Value.Value
votingValue mph tokenName =
    Value.singleton (Value.mpsSymbol mph) tokenName 1

{-# INLINABLE ownsVotingToken #-}
ownsVotingToken :: MintingPolicyHash -> TokenName -> TxConstraints Void Void
ownsVotingToken mph tokenName = Constraints.mustSpendAtLeast (votingValue mph tokenName)

{-# INLINABLE transition #-}
transition :: Params -> State GovState -> GovInput -> Maybe (TxConstraints Void Void, State GovState)
transition Params{..} State{ stateData = s, stateValue} i = case (s, i) of

    (GovState{mph}, MintTokens tokenNames) ->
        let (total, constraints) = foldMap
                (\(pk, nm) -> let v = votingValue mph nm in (v, Constraints.mustPayToPubKey pk v))
                (zip initialHolders tokenNames)
        in Just (constraints <> Constraints.mustMintValue total, State s stateValue)

    (GovState law mph Nothing, ProposeChange proposal@Proposal{tokenName}) ->
        let constraints = ownsVotingToken mph tokenName
        in Just (constraints, State (GovState law mph (Just (Voting proposal AssocMap.empty))) stateValue)

    (GovState law mph (Just (Voting p oldMap)), AddVote tokenName vote) ->
        let newMap = AssocMap.insert tokenName vote oldMap
            constraints = ownsVotingToken mph tokenName
                        <> Constraints.mustValidateIn (Interval.to (votingDeadline p))
        in Just (constraints, State (GovState law mph (Just (Voting p newMap))) stateValue)

    (GovState oldLaw mph (Just (Voting p votes)), FinishVoting) ->
        let Sum ayes = foldMap (\b -> Sum $ if b then 1 else 0) votes
        in Just (mempty, State (GovState (if ayes >= requiredVotes then newLaw p else oldLaw) mph Nothing) stateValue)

    _ -> Nothing

-- | The main contract for creating a new law and for voting on proposals.
contract ::
    AsGovError e
    => Params
    -> Contract () Schema e ()
contract params = forever $ mapError (review _GovError) endpoints where
    theClient = client params
    endpoints = selectList [initLaw, addVote]

    addVote = endpoint @"add-vote" $ \(tokenName, vote) ->
        void $ SM.runStep theClient (AddVote tokenName vote)

    initLaw = endpoint @"new-law" $ \bsLaw -> do
        let mph = Scripts.forwardingMintingPolicyHash (typedValidator params)
        void $ SM.runInitialise theClient (GovState (fromHaskellByteString bsLaw) mph Nothing) mempty
        let tokens = Haskell.zipWith (const (mkTokenName (baseTokenName params))) (initialHolders params) [1..]
        void $ SM.runStep theClient $ MintTokens tokens

-- | The contract for proposing changes to a law.
proposalContract ::
    AsGovError e
    => Params
    -> Proposal
    -> Contract () EmptySchema e ()
proposalContract params proposal = mapError (review _GovError) propose where
    theClient = client params
    propose = do
        void $ SM.runStep theClient (ProposeChange proposal)

        logInfo @Text "Voting started. Waiting for the voting deadline to count the votes."
        void $ awaitTime $ votingDeadline proposal

        logInfo @Text "Voting finished. Counting the votes."
        void $ SM.runStep theClient FinishVoting

PlutusTx.makeLift ''Params
PlutusTx.unstableMakeIsData ''Proposal
PlutusTx.makeLift ''Proposal
PlutusTx.unstableMakeIsData ''Voting
PlutusTx.makeLift ''Voting
PlutusTx.unstableMakeIsData ''GovState
PlutusTx.makeLift ''GovState
PlutusTx.unstableMakeIsData ''GovInput
PlutusTx.makeLift ''GovInput
