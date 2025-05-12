module ZkFold.Cardano.SmartWallet.Api.Batch (
  batchTxs,
) where

import Cardano.Api qualified as CApi
import Cardano.Api.Internal.Fees qualified as CApi
import Cardano.Api.Ledger qualified as Ledger
import Cardano.Api.Shelley qualified as CApi
import Cardano.Ledger.Val qualified as Ledger
import Data.List (elemIndex, union)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (fromJust)
import Data.Set qualified as Set
import GHC.IsList (IsList (fromList), toList)
import GeniusYield.Imports hiding (toList)
import GeniusYield.Transaction
import GeniusYield.Transaction.CoinSelection.Numeric (equipartitionNatural)
import GeniusYield.TxBuilder
import GeniusYield.Types
import ZkFold.Cardano.SmartWallet.Api.Create (initializeWalletScripts)
import ZkFold.Cardano.SmartWallet.Types
import ZkFold.Cardano.UPLC.Wallet.Types (Signature (..))

{- | Combine zk smart-wallet transactions into a single transaction.

Our strategy to make a batch is to combine individually built transactions. It has following benefits:

* Wallets individually pay for their outputs. Otherwise we'll need big overhaul (or rather a custom version) of coin selection algorithm, losing the robustness of existing algorithm.
* We continue exercising robust coin selection algorithm of Atlas.
* Since transactions are already built (and can be built in parallel), combining is now quick.
* Since transactions of users are individually built, they have complete freedom over it, like using different coin selection strategies.

However, fees of combined transaction need not be lower than sum of fees of individual transactions due to the change in execution units of involved scripts as script context is larger now. Though based on testing, it is mostly lower.

__NOTE__: We assume transactions provided are those returned by our API when sending funds from our zk based smart-wallet. This combining function need not necessarily work for other transactions.
-}
batchTxs ::
  ZKWalletQueryMonad m =>
  GYUTxO ->
  NE.NonEmpty ZKBatchWalletInfo ->
  -- | Combined transaction and saved fee.
  m (GYTx, Maybe Natural)
batchTxs collUtxo bwis = do
  {- Following is the high level strategy:
    * We obtain `TxBodyContent` with `BuildTx` parameter.
    * We concatenate the `TxBodyContent`s by adding up the fees and updating redeemers for withdrawals script.
  -}
  -- We ignore for key witnesses since they won't be valid anyway.
  bwisResolvedWithIns <-
    mapM
      ( \ZKBatchWalletInfo {..} -> do
          (txBodyContent, inUtxos) <- obtainTxBodyContentBuildTx' $ getTxBody zkbwiTx
          walletScript <- initializeWalletScripts zkbwiEmail
          pure ((txBodyContent, walletScript, zkbwiPaymentKeyHash), inUtxos)
      )
      bwis
  let bwisResolved = fmap fst bwisResolvedWithIns
      inUtxos = foldMap snd bwisResolvedWithIns
  pp <- protocolParams
  nid <- networkId
  -- Ordered list of required extra-key witnesses.
  let oreqSigs =
        foldMap
          ( (\(a, _b, _c) -> a) >>> CApi.txExtraKeyWits >>> \case
              CApi.TxExtraKeyWitnessesNone -> mempty
              CApi.TxExtraKeyWitnesses _ ks -> Set.fromList ks
          )
          bwisResolved
          & Set.union (Set.fromList $ NE.toList $ fmap (zkbwiPaymentKeyHash >>> paymentKeyHashToApi) bwis)
          & Set.toList
      combinedTxBodyContent =
        fst $
          foldl'
            ( \(accBodyContent, pastOutsNum) (txBodyContent, walletScript, paymentKeyHashToApi -> pkh) ->
                ( accBodyContent
                    { CApi.txMintValue = combineMintValue (CApi.txMintValue accBodyContent) (CApi.txMintValue txBodyContent)
                    , CApi.txCertificates =
                        combineTxCertificates
                          (CApi.txCertificates accBodyContent)
                          (CApi.txCertificates txBodyContent)
                          ( updateCertRedeemer
                              (GYCredentialByScript (scriptHash (zkiwsCheckSig walletScript)) & stakeCredentialToApi)
                              pastOutsNum
                              (findSignatoryIndex oreqSigs pkh)
                          )
                    , CApi.txWithdrawals =
                        combineTxWithdrawals
                          (CApi.txWithdrawals accBodyContent)
                          (CApi.txWithdrawals txBodyContent)
                          ( updateWdrlRedeemer
                              (stakeAddressFromCredential nid (GYCredentialByScript $ scriptHash (zkiwsCheckSig walletScript)) & stakeAddressToApi)
                              pastOutsNum
                              (findSignatoryIndex oreqSigs pkh)
                          )
                    , CApi.txValidityUpperBound = combineValidityUpperBound (CApi.txValidityUpperBound accBodyContent) (CApi.txValidityUpperBound txBodyContent)
                    , CApi.txValidityLowerBound = combineValidityLowerBound (CApi.txValidityLowerBound accBodyContent) (CApi.txValidityLowerBound txBodyContent)
                    , CApi.txOuts = CApi.txOuts accBodyContent <> CApi.txOuts txBodyContent
                    , CApi.txInsReference = combineTxInsReference (CApi.txInsReference accBodyContent) (CApi.txInsReference txBodyContent)
                    , CApi.txIns = CApi.txIns accBodyContent `union` CApi.txIns txBodyContent
                    , CApi.txFee = CApi.txFee accBodyContent `addTxFee` CApi.txFee txBodyContent
                    }
                , pastOutsNum + fromIntegral (length (CApi.txOuts txBodyContent))
                )
            )
            ( let (fstTxBodyContent, fstWalletScript, paymentKeyHashToApi -> pkh) = NE.head bwisResolved
                  stakeCred = GYCredentialByScript $ scriptHash (zkiwsCheckSig fstWalletScript)
                  stakeAddr = stakeAddressFromCredential nid stakeCred
               in ( fstTxBodyContent
                      { CApi.txExtraKeyWits = CApi.TxExtraKeyWitnesses CApi.AlonzoEraOnwardsConway oreqSigs
                      , -- Since we check if scripts are executed correctly, total & return collateral are not needed. It is to be also noted that collateral UTxO used is that of server.
                        CApi.txReturnCollateral = CApi.TxReturnCollateralNone
                      , CApi.txTotalCollateral = CApi.TxTotalCollateralNone
                      , CApi.txInsCollateral = CApi.TxInsCollateral CApi.AlonzoEraOnwardsConway [utxoRef collUtxo & txOutRefToApi]
                      , CApi.txWithdrawals = case CApi.txWithdrawals fstTxBodyContent of
                          CApi.TxWithdrawalsNone -> CApi.TxWithdrawalsNone
                          CApi.TxWithdrawals sbe ls ->
                            CApi.TxWithdrawals
                              sbe
                              ( map
                                  ( updateWdrlRedeemer
                                      (stakeAddressToApi stakeAddr)
                                      0
                                      (findSignatoryIndex oreqSigs pkh)
                                  )
                                  ls
                              )
                      , CApi.txCertificates = case CApi.txCertificates fstTxBodyContent of
                          CApi.TxCertificatesNone -> CApi.TxCertificatesNone
                          CApi.TxCertificates sbe ls ->
                            CApi.TxCertificates
                              sbe
                              ( (fmap . fmap)
                                  ( updateCertRedeemer
                                      (stakeCredentialToApi stakeCred)
                                      0
                                      (findSignatoryIndex oreqSigs pkh)
                                  )
                                  ls
                              )
                      }
                  , fromIntegral (length (CApi.txOuts fstTxBodyContent))
                  )
            )
            (NE.tail bwisResolved)
  eh <- eraHistory
  ss <- systemStart
  let inUtxosWithColl = inUtxos <> utxosFromList [collUtxo]
      inUtxosWithCollApi = utxosToApi inUtxosWithColl
      ppApi = CApi.LedgerProtocolParameters pp
      era = CApi.toCardanoEra CApi.ShelleyBasedEraConway
      ehApi = CApi.toLedgerEpochInfo eh
      ecombinedTxBody = do
        txBodyForExUnits <- CApi.createTransactionBody CApi.ShelleyBasedEraConway combinedTxBodyContent & first CApi.TxBodyError
        exUnitsMapWithLogs <-
          first CApi.TxBodyErrorValidityInterval $
            CApi.evaluateTransactionExecutionUnits
              era
              ss
              ehApi
              ppApi
              inUtxosWithCollApi
              txBodyForExUnits
        let exUnitsMap = Map.map (fmap snd) exUnitsMapWithLogs
        exUnitsMap' <-
          case Map.mapEither id exUnitsMap of
            (failures, exUnitsMap') ->
              CApi.handleExUnitsErrors
                (CApi.txScriptValidityToScriptValidity (CApi.txScriptValidity combinedTxBodyContent))
                failures
                exUnitsMap'
        txBodyContentWithCorrectUnits <- CApi.substituteExecutionUnits exUnitsMap' combinedTxBodyContent
        txBodyWithCorrectUnits <- CApi.createTransactionBody CApi.ShelleyBasedEraConway txBodyContentWithCorrectUnits & first CApi.TxBodyError
        let nkeys = estimateKeyWitnesses combinedTxBodyContent inUtxosWithCollApi
            fee = CApi.calculateMinTxFee CApi.ShelleyBasedEraConway pp inUtxosWithCollApi txBodyWithCorrectUnits nkeys
            oldFee = case CApi.txFee combinedTxBodyContent of CApi.TxFeeExplicit _ f -> f
        -- NOTE: Ideally we should add for extra lovelace (some large number) is auth outputs (i.e. outputs with auth token) before computing fees and execution units for it to be fully accurate (& valid) but very unlikely that one would run into such a case.
        let (finalTxBodyContent, diff) =
              if fee < oldFee
                then
                  let diffN :: Natural = fromIntegral $ oldFee - fee
                      parts = equipartitionNatural diffN bwis
                   in ( txBodyContentWithCorrectUnits
                          { CApi.txFee = CApi.TxFeeExplicit CApi.ShelleyBasedEraConway fee
                          , CApi.txOuts =
                              fst $
                                foldl'
                                  ( \(accOuts, ix) (toAdd, (txBodyContent, _, _)) ->
                                      -- Assuming that first output had the special auth token.
                                      ( updateAt
                                          ix
                                          (\(CApi.TxOut addr val d s) -> CApi.TxOut addr (addVal val toAdd) d s)
                                          accOuts
                                      , ix + length (CApi.txOuts txBodyContent)
                                      )
                                  )
                                  (CApi.txOuts txBodyContentWithCorrectUnits, 0)
                                  (NE.zip parts bwisResolved)
                          }
                      , Just diffN
                      )
                else (txBodyContentWithCorrectUnits, Nothing)
        fmap (,diff) $ CApi.createTransactionBody CApi.ShelleyBasedEraConway finalTxBodyContent & first CApi.TxBodyError
  (combinedTxBody, diff) <- either (throwError . GYBuildTxException . GYBuildTxBodyErrorAutoBalance) pure ecombinedTxBody
  pure (unsignedTx $ txBodyFromApi combinedTxBody, diff)
 where
  updateWitRedeemer outIx sigIx swi sw =
    CApi.ScriptWitness swi $
      case sw of
        CApi.SimpleScriptWitness _ _ -> sw
        CApi.PlutusScriptWitness slie psv psori sd _sr eu ->
          CApi.PlutusScriptWitness slie psv psori sd (Signature outIx sigIx & redeemerFromPlutusData & redeemerToApi) eu
  updateCertRedeemer ::
    CApi.StakeCredential ->
    Integer ->
    Integer ->
    Maybe (CApi.StakeCredential, CApi.Witness CApi.WitCtxStake ApiEra) ->
    Maybe (CApi.StakeCredential, CApi.Witness CApi.WitCtxStake ApiEra)
  updateCertRedeemer reqStakeCred outIx sigIx msw =
    case msw of
      Nothing -> Nothing
      Just (sc, wit) ->
        if sc == reqStakeCred
          then case wit of
            CApi.KeyWitness _ -> Just (sc, wit)
            CApi.ScriptWitness swi sw ->
              Just
                ( sc
                , updateWitRedeemer outIx sigIx swi sw
                )
          else Just (sc, wit)

  updateWdrlRedeemer ::
    CApi.StakeAddress ->
    Integer ->
    Integer ->
    (CApi.StakeAddress, Ledger.Coin, CApi.BuildTxWith CApi.BuildTx (CApi.Witness CApi.WitCtxStake ApiEra)) ->
    (CApi.StakeAddress, Ledger.Coin, CApi.BuildTxWith CApi.BuildTx (CApi.Witness CApi.WitCtxStake ApiEra))
  updateWdrlRedeemer reqStakeAddr outIx sigIx (stakeAddr, coin, CApi.BuildTxWith wit) =
    if stakeAddr == reqStakeAddr
      then case wit of
        CApi.KeyWitness _ -> (stakeAddr, coin, CApi.BuildTxWith wit)
        CApi.ScriptWitness swi sw ->
          ( stakeAddr
          , coin
          , CApi.BuildTxWith $
              updateWitRedeemer outIx sigIx swi sw
          )
      else (stakeAddr, coin, CApi.BuildTxWith wit)

  findSignatoryIndex oreqSigs pkh =
    elemIndex pkh oreqSigs
      -- Impossible to fail since we already included this pkh in @oreqSigs@.
      & fromJust
      & fromIntegral

  addTxFee (CApi.TxFeeExplicit sbe a) (CApi.TxFeeExplicit _sbe b) = CApi.TxFeeExplicit sbe (a + b)

  combineValidityLowerBound CApi.TxValidityNoLowerBound b = b
  combineValidityLowerBound a CApi.TxValidityNoLowerBound = a
  combineValidityLowerBound (CApi.TxValidityLowerBound aeo a) (CApi.TxValidityLowerBound _aeo b) = CApi.TxValidityLowerBound aeo (min a b)

  combineValidityUpperBound (CApi.TxValidityUpperBound _sbe Nothing) b = b
  combineValidityUpperBound a (CApi.TxValidityUpperBound _sbe Nothing) = a
  combineValidityUpperBound (CApi.TxValidityUpperBound sbe (Just a)) (CApi.TxValidityUpperBound _sbe (Just b)) = CApi.TxValidityUpperBound sbe (Just (max a b))

  combineTxInsReference CApi.TxInsReferenceNone b = b
  combineTxInsReference a CApi.TxInsReferenceNone = a
  combineTxInsReference (CApi.TxInsReference beo a) (CApi.TxInsReference _beo b) = CApi.TxInsReference beo (a `union` b)

  combineTxWithdrawals a b updateF = combineTxWithdrawals' a $ case b of
    CApi.TxWithdrawalsNone -> CApi.TxWithdrawalsNone
    CApi.TxWithdrawals sbe ls ->
      CApi.TxWithdrawals
        sbe
        ( map
            updateF
            ls
        )

  combineTxWithdrawals' a CApi.TxWithdrawalsNone = a
  combineTxWithdrawals' CApi.TxWithdrawalsNone b = b
  combineTxWithdrawals' (CApi.TxWithdrawals sbe a) (CApi.TxWithdrawals _sbe b) =
    CApi.TxWithdrawals
      sbe
      (a <> b)

  combineTxCertificates a b updateF = combineTxCertificates' a $ case b of
    CApi.TxCertificatesNone -> CApi.TxCertificatesNone
    CApi.TxCertificates sbe ls ->
      CApi.TxCertificates sbe $ fmap (fmap updateF) ls

  combineTxCertificates' a CApi.TxCertificatesNone = a
  combineTxCertificates' CApi.TxCertificatesNone b = b
  combineTxCertificates' (CApi.TxCertificates sbe a) (CApi.TxCertificates _sbe b) =
    CApi.TxCertificates sbe $ fromList (toList a <> toList b)

  combineMintValue CApi.TxMintNone b = b
  combineMintValue a CApi.TxMintNone = a
  combineMintValue (CApi.TxMintValue sbe a) (CApi.TxMintValue _sbe b) = CApi.TxMintValue sbe (a <> b)

  updateAt :: Int -> (a -> a) -> [a] -> [a]
  updateAt i f xs
    -- Return original list if index is out of bounds
    | i < 0 || i >= length xs = xs
    | otherwise = take i xs ++ [f (xs !! i)] ++ drop (i + 1) xs

  addVal :: CApi.TxOutValue ApiEra -> Natural -> CApi.TxOutValue ApiEra
  addVal (CApi.TxOutValueByron c) toAdd = CApi.TxOutValueByron (c + fromIntegral toAdd)
  addVal (CApi.TxOutValueShelleyBased sb lval) (fromIntegral -> toAdd :: Ledger.Coin) = CApi.TxOutValueShelleyBased sb (Ledger.modifyCoin (+ toAdd) lval)

  -- TODO: Implement robust solution (similar to how Atlas computes for them https://github.com/geniusyield/atlas/blob/bcdb88dccf93a9e41cb58015b452c242b9932a16/src/GeniusYield/Transaction.hs#L413-L424) later. For now it's not needed since we are assuming that our API has built these transactions in first place.
  estimateKeyWitnesses :: CApi.TxBodyContent CApi.BuildTx era -> CApi.UTxO era -> Word
  estimateKeyWitnesses CApi.TxBodyContent {..} _inUtxosWithCollApi =
    1 -- Since we have witness only for collateral.
      + ( case txExtraKeyWits of
            CApi.TxExtraKeyWitnesses _ ks -> length ks & fromIntegral
            CApi.TxExtraKeyWitnessesNone -> 0
        )
