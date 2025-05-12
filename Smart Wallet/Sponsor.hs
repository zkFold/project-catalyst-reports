module ZkFold.Cardano.SmartWallet.Api.Sponsor (
  getBabelTokensRequired,
  getBabelTokensRequiredForAmount,
  findSuitableSponsor,
  applySponsor,
) where

import Cardano.Api qualified as CApi
import Control.Monad.IO.Class (MonadIO (..))
import Data.Foldable (find)
import Data.Set qualified as Set
import GHC.IsList (IsList (fromList))
import GeniusYield.Imports ((&))
import GeniusYield.Transaction.Common (GYTxExtraConfiguration (..))
import GeniusYield.TxBuilder
import GeniusYield.Types
import ZkFold.Cardano.SmartWallet.Constants (sponsorBabelFeeLovelaceThreshold, sponsorUtxoLovelaceRequirement)
import ZkFold.Cardano.SmartWallet.Types
import ZkFold.Cardano.SmartWallet.Utils (valueAtleastLovelace, valueIsAdaOnly, valueMintingPolicies)

-- | User must have tokens equivalent to @sponsorBabelFeeLovelaceThreshold@.
getBabelTokensRequired :: Babel -> Integer
getBabelTokensRequired Babel {..} = getBabelTokensRequiredForAmount Babel {..} sponsorBabelFeeLovelaceThreshold

-- | Get the number of tokens required for a given lovelace amount.
getBabelTokensRequiredForAmount :: Babel -> Integer -> Integer
getBabelTokensRequiredForAmount Babel {..} amount = ceiling (recip bPrice * fromIntegral amount)

sponsorConditionSatisfied :: GYValue -> GYTime -> SponsorCondition -> GYTxSkeleton v -> Bool
sponsorConditionSatisfied valAvailable currentTime sc skel = case sc of
  SCGatedNFT (GatedNFT {..}) -> do
    (gnTimeout >= currentTime)
      && (gytxOuts skel & any (\GYTxOut {..} -> Set.member gnMintingPolicyId (valueMintingPolicies gyTxOutValue)))
  SCBabel b@Babel {..} ->
    -- The reason for adding 1: We'll be subtracting the tokens equivalent to @sponsorBabelFeeLovelaceThreshold@ from this value so that it gets added to the change output towards the sponsor but we still want a residue non-zero token amount left in the output so that fees get computed considering it. Note that after we have computed fees, we'll be adding remaining tokens back (which would imply that there could be an entry for this asset class in the UTxO).
    let tokensRequired = getBabelTokensRequired b + 1
     in valueAssetClass valAvailable (nonAdaTokenToAssetClass bToken) >= tokensRequired

sponsorSatisfied :: GYValue -> GYTime -> Sponsor -> GYTxSkeleton v -> Bool
sponsorSatisfied valAvailable currentTime Sponsor {..} = sponsorConditionSatisfied valAvailable currentTime srCondition

findSuitableSponsor ::
  GYTxQueryMonad m =>
  -- | Available value.
  GYValue ->
  -- | Current time.
  GYTime ->
  [(Sponsor, GYAddress)] ->
  GYTxSkeleton v ->
  m (Maybe ((Sponsor, GYAddress), GYUTxO))
findSuitableSponsor valAvailable currentTime sponsors skel = do
  -- Find those sponsors which are satisfied by the skeleton.
  let satisfiedSponsors = filter (\(sponsor, _) -> sponsorSatisfied valAvailable currentTime sponsor skel) sponsors
      satisfiedSponsorsAddresses = map snd satisfiedSponsors
  -- Filter out those sponsors which don't have enough ADA. We want a ADA-only UTxO.
  utxos <- utxosAtAddresses satisfiedSponsorsAddresses
  case find (\GYUTxO {..} -> valueIsAdaOnly utxoValue && valueAtleastLovelace utxoValue sponsorUtxoLovelaceRequirement) (utxosToList utxos) of
    Nothing -> pure Nothing
    Just utxo -> case find (\(_sponsor, addr) -> addr == utxoAddress utxo) satisfiedSponsors of
      Nothing -> pure Nothing -- absurd case.
      Just sponsor -> pure $ Just (sponsor, utxo)

applySponsor :: (MonadIO m, GYTxBuilderMonad m) => [(Sponsor, GYAddress)] -> GYUTxOs -> GYTxSkeleton v -> GYAddress -> TxBuilderStrategy m -> GYTxExtraConfiguration v -> m GYTx
applySponsor sps utxos skel walletAddr strat ec = do
  let inValue = foldMapUTxOs utxoValue utxos
      outValue = foldMap gyTxOutValue $ gytxOuts skel
      valAvailable = inValue `valueMinus` outValue
  currentTime <- liftIO getCurrentGYTime
  msponsor <- findSuitableSponsor valAvailable currentTime sps skel
  gyLogInfo' "smart-wallet" $ "Found sponsor: " <> (case msponsor of Nothing -> "none"; Just ((_key, addr), utxo) -> "yes, " <> show addr <> " " <> show utxo)
  body <- case msponsor of
    Nothing -> buildTxBodyWithStrategyAndExtraConfiguration strat ec skel
    Just ((Sponsor {srCondition = SCBabel b@Babel {..}}, _), utxo) ->
      let tokensRequired = getBabelTokensRequired b
       in buildTxBodyWithStrategyAndExtraConfiguration
            strat
            ( ec
                { gytxecFeeUtxo = Just utxo
                , gytxecPreBodyContentMapper = \body ->
                    -- Find an output from the last, which has more than @tokensRequired@ amount of tokens and subtract this amount from it so that it get's added to sponsor's change address.
                    let newOuts = removeFromLast bToken tokensRequired (CApi.txOuts body)
                     in body {CApi.txOuts = newOuts}
                , gytxecPostBodyContentMapper = \body ->
                    -- Now we need to add back left-over tokens to the user.
                    let CApi.TxFeeExplicit _sbe fee = CApi.txFee body
                        tokensRequiredForFee = getBabelTokensRequiredForAmount b (fromIntegral fee)
                        tokensLeftOver = tokensRequired - tokensRequiredForFee
                        -- From last, reduce the amount of tokens by @tokensLeftOver@ from the first output that has at least this many tokens.
                        outsRemovedFromLast = removeFromLast bToken tokensLeftOver (CApi.txOuts body)
                        -- From beginning, add @tokensLeftOver@ to the first output with that asset class.
                        finalOuts = addFromBeginning bToken tokensLeftOver outsRemovedFromLast
                     in body
                          { CApi.txOuts = finalOuts
                          , -- TODO: Update Atlas so this won't be needed -- though it's not an issue as we run the scripts as part of build process thus collateral cannot be taken if build is successful.
                            CApi.txTotalCollateral = CApi.TxTotalCollateralNone
                          , CApi.txReturnCollateral = CApi.TxReturnCollateralNone
                          }
                }
            )
            (skel <> mustHaveOutput (mkGYTxOutNoDatum walletAddr (valueSingleton (nonAdaTokenToAssetClass bToken) tokensRequired)))
    Just ((Sponsor {srCondition = SCGatedNFT _}, _), utxo) ->
      buildTxBodyWithStrategyAndExtraConfiguration
        strat
        (ec {gytxecFeeUtxo = Just utxo})
        skel
  case msponsor of
    Nothing -> pure $ unsignedTx body
    Just ((sponsor, _), _) -> pure $ signGYTxBody body [somePaymentSigningKeyToSomeSigningKey $ AGYExtendedPaymentSigningKey (walletKeysToExtendedPaymentSigningKey $ smKeys $ srMnemonic sponsor)]
 where
  -- Remove @tokensRequired@ from the first output (traversing from the last to beginning) that has that many tokens.
  removeFromLast bToken tokensRequired txOuts =
    let apiAC = assetClassToApi $ nonAdaTokenToAssetClass bToken
        subVal = fromList [(apiAC, CApi.Quantity tokensRequired)] & CApi.negateValue
     in fst $
          foldr
            ( \out@(CApi.TxOut outAddr outVal outDat outRefS) (acc, found) ->
                if found
                  then (out : acc, found)
                  else
                    let outVal' = CApi.txOutValueToValue outVal
                        assetAmt = CApi.selectAsset outVal' apiAC
                     in if assetAmt > CApi.Quantity tokensRequired
                          then
                            ( CApi.TxOut
                                outAddr
                                (CApi.TxOutValueShelleyBased CApi.ShelleyBasedEraConway (CApi.toLedgerValue CApi.MaryEraOnwardsConway $ outVal' <> subVal))
                                outDat
                                outRefS
                                : acc
                            , True
                            )
                          else (out : acc, found)
            )
            ([], False)
            txOuts
  addFromBeginning bToken tokensToAdd txOuts =
    let bTokenApi = assetClassToApi $ nonAdaTokenToAssetClass bToken
        addVal = fromList [(bTokenApi, CApi.Quantity tokensToAdd)]
        go [] = []
        go (out@(CApi.TxOut outAddr outVal outDat outRefS) : rest) =
          let outVal' = CApi.txOutValueToValue outVal
              assetAmt = CApi.selectAsset outVal' bTokenApi
           in if assetAmt > CApi.Quantity 0
                then
                  let newOut =
                        CApi.TxOut
                          outAddr
                          (CApi.TxOutValueShelleyBased CApi.ShelleyBasedEraConway (CApi.toLedgerValue CApi.MaryEraOnwardsConway $ outVal' <> addVal))
                          outDat
                          outRefS
                   in newOut : rest
                else
                  out : go rest
     in go txOuts
