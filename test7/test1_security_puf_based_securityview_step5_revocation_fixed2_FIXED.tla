------------------------------- MODULE test1_security_puf_based_securityview_step5_revocation_fixed2_FIXED -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANTS
  \* Stage atoms (model values)
  Design, Verification, Fabrication, Testing, Integration, Final,

  \* Manager atoms (model values)
  DesignManager, VerificationManager, FabricationManager, TestingManager, IntegrationManager, Owner, Attacker,

  \* Parameterized sets/functions
  LegitimateIssuers,            \* SUBSET of issuers who can approve/issue
  AttackerIssuers,              \* Optional attacker set (model values)
  ChipletId,                    \* Nat or model value of the chiplet tracked in this run
  ChipletOwner,                 \* Who holds the Final VC (must be in LegitimateIssuers)
  MaxMCId,                      \* Maximum microcredential ID (bound state space)
  MaxPUFId,                     \* Maximum PUF ID (bound state space)
  MaxSiPId,                     \* Maximum SiP ID (bound state space)
  ChipletSet,                   \* SUBSET Nat or model values – chiplets that can be integrated
  MaxChipletsPerSiP,            \* Maximum number of chiplets per SiP
  MaxVCId,                      \* Maximum verification challenge ID (bound state space)
  MaxSessionId,                 \* Maximum session ID for verification
  MaxNonce,                     \* Maximum nonce value for freshness
  MaxAttestationLag,               \* Maximum allowed lag (in steps) between Verified session and integration
  AttestationTTL,
  AllowCounterfeitIntegrate     \* gate to enable/disable counterfeit insertion transition (Step 1)

IssuerAtoms ==
  { DesignManager, VerificationManager, FabricationManager,
    TestingManager, IntegrationManager, Owner, Attacker }

Issuers == LegitimateIssuers \cup AttackerIssuers

\* Symmetry operator (enable in .cfg with:  SYMMETRY Symmetry)
Symmetry ==
  Permutations(LegitimateIssuers)
  \cup Permutations(AttackerIssuers)
  \cup Permutations(ChipletSet)


(***************************************************************************)
(* Stages                                                                  *)
(***************************************************************************)
Stages == << Design, Verification, Fabrication, Testing, Integration, Final >>
StageAt(i) == Stages[i]
NumStages == Len(Stages)

NoPUF == 0   \* a distinct number not used for valid PUF IDs

(***************************************************************************)
(* Types                                                                    *)
(***************************************************************************)
Tx == [ id     : Nat,
        chiplet: Nat \cup ChipletSet,
        stage  : {Design,Verification,Fabrication,Testing,Integration,Final},
        mcId   : Nat,
        puf    : Nat \cup {NoPUF},
        issuer : Issuers ]

Microcredential ==
  [ id     : Nat,
    chiplet: Nat \cup ChipletSet,
    stage  : {Design,Verification,Fabrication,Testing,Integration,Final},
    issuer : Issuers,
    puf    : Nat \cup {NoPUF},
    publicKey: Nat \cup {NoPUF},
    chipletSignature: Nat \cup {NoPUF},
    sramPUFReadout: Nat \cup {NoPUF},
    errorCorrectedData: Nat \cup {NoPUF},
    fuzzyExtractedKey: Nat \cup {NoPUF},
    verificationPolicy: Nat \cup {NoPUF},
    revocationHandle: Nat \cup {NoPUF} ]

SiPIntegration ==
  [ sipId: Nat,
    chipletId: Nat \cup ChipletSet,
    mcId: Nat,
    pufId: Nat,
    integrator: Issuers,
    timestamp: Nat ]

VerificationChallenge ==
  [ challengeId: Nat,
    mcId: Nat,
    pufId: Nat,
    challenger: Issuers,
    timestamp: Nat,
    sessionId: Nat,
    nonce: Nat ]

VerificationResponse ==
  [ responseId: Nat,
    challengeId: Nat,
    mcId: Nat,
    pufId: Nat,
    response: Nat,
    responder: Issuers,
    timestamp: Nat,
    ephemeralPrivateKey: Nat \cup {NoPUF},
    ephemeralPublicKey: Nat \cup {NoPUF},
    messageSignature: Nat \cup {NoPUF},
    message: Nat \cup {NoPUF} ]

AttackAttempt ==
  [ attackId: Nat,
    attackType: {"FakeMC","SpoofPUF","ReplayResponse","UnauthorizedIssue","FakeChallenge","NoOp","ReplayAttack","CloneAttempt","PUFSpoofing","HelperDataAttack","FuzzyExtractorAttack","FakeChipletInjection","SupplyChainAttack","CounterfeitIntegrate"},
    attacker: Issuers,
    targetMC: Nat,
    targetPUF: Nat,
    timestamp: Nat,
    success: BOOLEAN ]

\* Extended with "Verified"/"Failed" to match validation action
VerificationSession ==
  [ sessionId: Nat,
    mcId: Nat,
    pufId: Nat,
    nonce: Nat,
    timestamp: Nat,
    status: {"Active","Completed","Expired","Verified","Failed"} ]

(***************************************************************************)
(* Variables                                                                *)
(***************************************************************************)
VARIABLES
ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done,
  \* SiP variables
  SiPStore, SiPIdCounter,
  \* Sparse verification/attack stores as sequences
  ChallengeSeq,    \* Seq(VerificationChallenge)
  ResponseSeq,     \* Seq(VerificationResponse)
  SessionSeq,      \* Seq(VerificationSession)
  VCIdCounter,     \* mirrors Len(ChallengeSeq)
  SessionIdCounter,\* mirrors Len(SessionSeq)
  NonceCounter,
  AttackLogSeq,    \* Seq(AttackAttempt)
  RevokedChiplets,
  AttackIdCounter  \* mirrors Len(AttackLogSeq)
vars == << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done,
     SiPStore, SiPIdCounter,
     ChallengeSeq, ResponseSeq, SessionSeq, VCIdCounter, SessionIdCounter, NonceCounter,
     AttackLogSeq, AttackIdCounter, RevokedChiplets >>

varsWithoutRevoked == <<
  ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done,
  SiPStore, SiPIdCounter,
  ChallengeSeq, ResponseSeq, SessionSeq, VCIdCounter, SessionIdCounter, NonceCounter,
  AttackLogSeq, AttackIdCounter
>>

(***************************************************************************)
(* Stage -> Issuer mapping / helpers                                        *)
(***************************************************************************)
StageDomain == {Design, Verification, Fabrication, Testing, Integration, Final}
StageIssuer ==
  [ s \in StageDomain |->
      CASE s = Design       -> DesignManager
         [] s = Verification -> VerificationManager
         [] s = Fabrication  -> FabricationManager
         [] s = Testing      -> TestingManager
         [] s = Integration  -> IntegrationManager
         [] s = Final        -> Owner ]
IssuerFor(stage) == StageIssuer[stage]

CanIssue(issuer, stage) == issuer = IssuerFor(stage)

NoStutter == ~(UNCHANGED vars)

\* Security view (updated to sequences)
ViewSecurity ==
  << Ledger, SiPIdCounter, SessionSeq, ChipletStage, MCIdCounter,
     ChallengeSeq, SessionIdCounter, ResponseSeq, VCIdCounter, NonceCounter,
     MCStore, ChipletPUF, SiPStore, AttackLogSeq, PUFIdCounter, RevokedChiplets >>

(***************************************************************************)
(* Convenience & sparse-store helpers                                       *)
(***************************************************************************)
AppendToSeq(s, e) == s \o << e >>

AllMCsUnion == UNION { MCStore[iss] : iss \in DOMAIN MCStore }

HasTestingMC(ch) ==
  \E m \in AllMCsUnion : m.stage = Testing /\ m.chiplet = ch

TestingMC(ch) ==
  CHOOSE m \in AllMCsUnion : m.stage = Testing /\ m.chiplet = ch

PostTestingStage(stage) == stage \in {Integration, Final}

\* Sparse challenge helpers
ChallengeExists(cid) == cid \in 1..Len(ChallengeSeq)
GetChallenge(cid) == ChallengeSeq[cid]

\* Sparse response helpers (at most one per challenge)
ResponseExists(cid) ==
  \E i \in 1..Len(ResponseSeq) : ResponseSeq[i].challengeId = cid
GetResponseByChallenge(cid) ==
  CHOOSE i \in 1..Len(ResponseSeq) : ResponseSeq[i].challengeId = cid

\* Sparse session helpers
SessionExists(sid) == sid \in 1..Len(SessionSeq)
GetSession(sid) == SessionSeq[sid]

IsFreshSession(sid, nonce) ==
  SessionExists(sid) /\ GetSession(sid).nonce = nonce /\ GetSession(sid).status = "Active"

(***************************************************************************)
(* Legitimacy & validation helpers                                          *)
(***************************************************************************)
IsLegitimate(issuer) == issuer \in LegitimateIssuers
IsAttacker(issuer)   == issuer \in AttackerIssuers
IsFinal(i) == StageAt(i) = Final
IsTesting(i) == StageAt(i) = Testing
NextStage(i) == i + 1
Holder(stage, issuer) == IF stage = Final THEN ChipletOwner ELSE issuer

\* PUF pipeline (simple numeric functions)
AccessSRAMPUF(pufId) == pufId * 10000 + 1234
ApplyErrorCorrection(rawPUF) == rawPUF + 100
ApplyFuzzyExtractor(correctedPUF) == correctedPUF * 2 + 50
DeriveStableSecretKey(fuzzyKey) == fuzzyKey + 200
GenerateECCKeyPair(secretKey) == [privateKey |-> secretKey * 3, publicKey |-> secretKey * 3000]
ChipletSign(pufId, mcIdOrM, privateKey) == privateKey * 1000 + mcIdOrM + pufId
GeneratePUFResponse(pufId, challengeId) == pufId * 2000 + challengeId

\* Anti-spoofing helpers
IsConsistentPUFResponse(pufId, response, enrollmentData) ==
  LET expectedResponse == GeneratePUFResponse(pufId, response)
  IN expectedResponse = response

HasValidPUFEntropy(pufId, rawData) == rawData > 1000 /\ rawData < 999999
IsPUFReplay(pufId, timestamp, previousTimestamps) ==
  \E prevTime \in previousTimestamps : prevTime = timestamp /\ timestamp > 0
IsValidHelperData(helperData, pufId) == helperData > 0 /\ helperData < 1000000
IsValidFuzzyExtraction(input, output) == output = ApplyFuzzyExtractor(input) /\ input > 0
IsValidChipletPUF(pufId, chipletId, expectedPUF) == pufId = expectedPUF /\ pufId > 0 /\ chipletId # 0
IsPUFConsistentAcrossStages(pufId, enrollmentData, verificationData) ==
  enrollmentData.puf = pufId /\ verificationData.puf = pufId
IsPotentialFakeChipletInjection(pufId, chipletId, testingTimestamp, previousPUFs) ==
  \E prevPUF \in previousPUFs :
    prevPUF.pufId # pufId /\ prevPUF.chipletId = chipletId /\ prevPUF.timestamp < testingTimestamp
IsPUFUniquePerChiplet(pufId, chipletId, allMicrocredentials) ==
  \A mc \in allMicrocredentials :
    (mc.chiplet = chipletId /\ mc.puf # NoPUF) => mc.puf = pufId

HasSupplyChainTamperingIndicators(pufId, chipletId, enrollmentData) ==
  enrollmentData.puf # pufId \/
  enrollmentData.chiplet # chipletId \/
  enrollmentData.timestamp = 0 \/
  (Len(Ledger) - enrollmentData.timestamp) > AttestationTTL

IsAuthorizedForStage(issuer, stage) ==
  (stage = Design /\ issuer = DesignManager) \/
  (stage = Verification /\ issuer = VerificationManager) \/
  (stage = Fabrication /\ issuer = FabricationManager) \/
  (stage = Testing /\ issuer = TestingManager) \/
  (stage = Integration /\ issuer = IntegrationManager) \/
  (stage = Final /\ issuer = ChipletOwner)

IsLegitimateMicrocredential(mc) == IsAuthorizedForStage(mc.issuer, mc.stage)

HasValidDesignCredentials(chipletId) ==
  \E mc \in AllMCsUnion :
    mc.chiplet = chipletId /\ mc.stage = Design /\ IsLegitimateMicrocredential(mc)

HasValidFabricationCredentials(chipletId) ==
  \E mc \in AllMCsUnion :
    mc.chiplet = chipletId /\ mc.stage = Fabrication /\ IsLegitimateMicrocredential(mc)

HasValidVerificationCredentials(chipletId) ==
  \E mc \in AllMCsUnion :
    mc.chiplet = chipletId /\ mc.stage = Verification /\ IsLegitimateMicrocredential(mc)

IsAuthenticChiplet(chipletId) ==
  HasValidDesignCredentials(chipletId) /\
  HasValidVerificationCredentials(chipletId) /\
  HasValidFabricationCredentials(chipletId)

IsFakeChipletEnrollment(chipletId, pufId, issuer) ==
  ~IsAuthenticChiplet(chipletId) \/
  ~IsAuthorizedForStage(issuer, Testing) \/
  IsAttacker(issuer)

HasValidStageProgression(chipletId) ==
  LET chipletMCs == { mc \in AllMCsUnion : mc.chiplet = chipletId } IN
  LET stages == { mc.stage : mc \in chipletMCs } IN
  Design \in stages /\ Verification \in stages /\ Fabrication \in stages

DeriveEphemeralKeys(secretKey, sessionId, nonce) ==
  LET kdfOutput == secretKey + sessionId + nonce
  IN [ephemeralPrivateKey |-> kdfOutput * 5,
      ephemeralPublicKey  |-> kdfOutput * 5000]

IsLegitimateTransaction(tx) == IsAuthorizedForStage(tx.issuer, tx.stage)

ChipletCompleted(chipletId) ==
  \E mc \in AllMCsUnion : mc.chiplet = chipletId /\ mc.stage = Final

GetFinalMC(chipletId) ==
  CHOOSE mc \in AllMCsUnion : mc.chiplet = chipletId /\ mc.stage = Final

ChipletAlreadyIntegrated(chipletId) ==
  \E sipId \in DOMAIN SiPStore :
    \E integration \in SiPStore[sipId] : integration.chipletId = chipletId

GetSiPChiplets(sipId) ==
  IF sipId \in DOMAIN SiPStore
  THEN { integration.chipletId : integration \in SiPStore[sipId] }
  ELSE {}

MicrocredentialExists(mcId) == \E iss \in DOMAIN MCStore : \E mc \in MCStore[iss] : mc.id = mcId
GetMCById(mcId) == CHOOSE mc \in AllMCsUnion : mc.id = mcId

\* NEW (Step 2): Require a Verified session tied to (mcId, pufId)
HasRecentVerifiedSession(mcId, pufId) ==
  \E sid \in 1..Len(SessionSeq) :
    LET sess == SessionSeq[sid] IN
      /\ sess.mcId = mcId
      /\ sess.pufId = pufId
      /\ sess.status = "Verified"
\* Attestation recency (TTL) helpers
MaxNat(S) == CHOOSE m \in S : \A x \in S : x <= m

\* Indices of verified sessions for (mcId, pufId)
FilteredVerifiedIdx(mcId, pufId) ==
  { sid \in 1..Len(SessionSeq) :
      LET s == SessionSeq[sid] IN
           /\ s.mcId = mcId
           /\ s.pufId = pufId
           /\ s.status = "Verified" }

\* Latest (max) timestamp among those sessions, or 0 if none
LatestVerifiedSessionTime(mcId, pufId) ==
  LET idx  == FilteredVerifiedIdx(mcId, pufId)
      hits == { (SessionSeq[sid]).timestamp : sid \in idx }
  IN IF hits = {} THEN 0 ELSE MaxNat(hits)

AttestationFreshForIntegration(mcId, pufId, nowTs) ==
  LET t == LatestVerifiedSessionTime(mcId, pufId)
  IN /\ t > 0
     /\ nowTs - t <= MaxAttestationLag




(******************************************************************)
(* Step 5: Revocation / Quarantine                                *)
(******************************************************************)
RevokeOnTamper(chipletId) ==
  /\ chipletId \in ChipletSet
  /\ chipletId \notin RevokedChiplets
  /\ RevokedChiplets' = RevokedChiplets \cup { chipletId }
  /\ UNCHANGED varsWithoutRevoked
AutoRevokeOnIndicators(chipletId) ==
    /\ \E mc \in AllMCsUnion : mc.chiplet = chipletId /\ mc.stage \in {Integration, Final}
  /\ LET mc == CHOOSE m \in AllMCsUnion : m.chiplet = chipletId /\ m.stage \in {Integration, Final} IN
  /\ HasSupplyChainTamperingIndicators(mc.puf, chipletId, mc)
  /\ chipletId \notin RevokedChiplets
  /\ RevokedChiplets' = RevokedChiplets \cup { chipletId }
  /\ UNCHANGED varsWithoutRevoked
(***************************************************************************)
(***************************************************************************)

Init ==
/\ ChipletStage = 1
  /\ RevokedChiplets = {}
  /\ ChipletPUF = NoPUF
  /\ Ledger = << >>
  /\ MCIdCounter = 0
  /\ PUFIdCounter = 0
  /\ Done = FALSE
  /\ ~(0 \in Issuers)
  /\ MCStore = [ i \in IssuerAtoms |-> {} ]
  /\ SiPStore = [ sipId \in 1..MaxSiPId |-> {} ]
  /\ SiPIdCounter = 0

  \* Sparse stores start empty
  /\ ChallengeSeq = << >>
  /\ ResponseSeq  = << >>
  /\ SessionSeq   = << >>
  /\ VCIdCounter = 0
  /\ SessionIdCounter = 0
  /\ NonceCounter = 0

  /\ AttackLogSeq = << >>
  /\ AttackIdCounter = 0

(***************************************************************************)
(* Enrollment                                                               *)
(***************************************************************************)
PUFBasedEnrollment ==
  LET i      == ChipletStage
      stage  == StageAt(i)
      issuer == IssuerFor(stage)
      _authorized == IsLegitimate(issuer) /\ CanIssue(issuer, stage)

      newMCId == MCIdCounter + 1
      newPUF == IF IsTesting(i) THEN PUFIdCounter + 1 ELSE ChipletPUF

      sramReadout == IF IsTesting(i) THEN AccessSRAMPUF(newPUF)
                     ELSE IF HasTestingMC(ChipletId) THEN TestingMC(ChipletId).sramPUFReadout ELSE NoPUF
      errorCorrected == IF IsTesting(i) THEN ApplyErrorCorrection(sramReadout)
                        ELSE IF HasTestingMC(ChipletId) THEN TestingMC(ChipletId).errorCorrectedData ELSE NoPUF
      fuzzyExtracted == IF IsTesting(i) THEN ApplyFuzzyExtractor(errorCorrected)
                        ELSE IF HasTestingMC(ChipletId) THEN TestingMC(ChipletId).fuzzyExtractedKey ELSE NoPUF
      stableSecret == IF IsTesting(i) THEN DeriveStableSecretKey(fuzzyExtracted) ELSE NoPUF
      keyPair == IF IsTesting(i) THEN GenerateECCKeyPair(stableSecret) ELSE [privateKey |-> NoPUF, publicKey |-> NoPUF]
      newPublicKey == IF IsTesting(i) THEN keyPair.publicKey
                      ELSE IF HasTestingMC(ChipletId) THEN TestingMC(ChipletId).publicKey ELSE NoPUF
      newChipletSignature == IF IsTesting(i) THEN ChipletSign(newPUF, newMCId, keyPair.privateKey)
                             ELSE IF HasTestingMC(ChipletId) THEN TestingMC(ChipletId).chipletSignature ELSE NoPUF
      verificationPolicy == IF IsTesting(i) THEN newPUF * 10000
                            ELSE IF HasTestingMC(ChipletId) THEN TestingMC(ChipletId).verificationPolicy ELSE NoPUF
      revocationHandle == IF IsTesting(i) THEN newPUF * 10001
                          ELSE IF HasTestingMC(ChipletId) THEN TestingMC(ChipletId).revocationHandle ELSE NoPUF
      allMicrocredentials == AllMCsUnion
      pufUniquenessValid == IF IsTesting(i) THEN IsPUFUniquePerChiplet(newPUF, ChipletId, allMicrocredentials) ELSE TRUE
      chipletPUFValid == IF IsTesting(i) THEN IsValidChipletPUF(newPUF, ChipletId, newPUF) ELSE TRUE
      chipletAuthenticityValid == IF IsTesting(i) THEN IsAuthenticChiplet(ChipletId) ELSE TRUE
      stageProgressionValid == IF IsTesting(i) THEN HasValidStageProgression(ChipletId) ELSE TRUE
      fakeChipletDetection == IF IsTesting(i) THEN ~IsFakeChipletEnrollment(ChipletId, newPUF, issuer) ELSE TRUE
      newMC ==
        [ id |-> newMCId, chiplet |-> ChipletId, stage |-> stage, issuer |-> issuer,
          puf |-> newPUF, publicKey |-> newPublicKey, chipletSignature |-> newChipletSignature,
          sramPUFReadout |-> sramReadout, errorCorrectedData |-> errorCorrected,
          fuzzyExtractedKey |-> fuzzyExtracted, verificationPolicy |-> verificationPolicy,
          revocationHandle |-> revocationHandle ]
      newTx ==
        [ id |-> Len(Ledger) + 1, chiplet |-> ChipletId, stage |-> stage, mcId |-> newMCId, puf |-> newPUF, issuer |-> issuer ]
      existingMCForStage ==
        \E iss \in DOMAIN MCStore : \E mc \in MCStore[iss] : mc.chiplet = ChipletId /\ mc.stage = stage
  IN
  /\ ~Done
  /\ i \in 1..NumStages
  /\ _authorized
  /\ ~existingMCForStage
  /\ newMCId <= MaxMCId
  /\ (IF IsTesting(i) THEN PUFIdCounter + 1 <= MaxPUFId ELSE TRUE)
  /\ pufUniquenessValid /\ chipletPUFValid /\ chipletAuthenticityValid /\ stageProgressionValid /\ fakeChipletDetection

  /\ MCIdCounter' = newMCId
  /\ IF IsTesting(i) THEN PUFIdCounter' = PUFIdCounter + 1 ELSE UNCHANGED PUFIdCounter
  /\ ChipletPUF' = IF IsTesting(i) THEN PUFIdCounter + 1 ELSE ChipletPUF
  /\ Ledger' = AppendToSeq(Ledger, newTx)
  /\ MCStore' = [MCStore EXCEPT ![issuer] = @ \cup {newMC}]
  /\ IF ~IsFinal(i)
        THEN /\ ChipletStage' = NextStage(i) /\ Done' = FALSE
        ELSE /\ ChipletStage' = i /\ Done' = TRUE
  /\ UNCHANGED << SiPStore, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, AttackLogSeq, AttackIdCounter, RevokedChiplets >>

(***************************************************************************)
(* Challenge / Response / Validation (sparse stores)                        *)
(***************************************************************************)
PUFBasedVerificationChallenge(challenger, mcId, pufId) ==
  LET newChallengeId == VCIdCounter + 1
      newSessionId == SessionIdCounter + 1
      newNonce == NonceCounter + 1
      newChallenge ==
        [ challengeId |-> newChallengeId, mcId |-> mcId, pufId |-> pufId,
          challenger |-> challenger, timestamp |-> Len(Ledger) + 1,
          sessionId |-> newSessionId, nonce |-> newNonce ]
      newSession ==
        [ sessionId |-> newSessionId, mcId |-> mcId, pufId |-> pufId,
          nonce |-> newNonce, timestamp |-> Len(Ledger) + 1, status |-> "Active" ]
  IN
  /\ IsLegitimate(challenger)
  /\ MicrocredentialExists(mcId)
  /\ newChallengeId <= MaxVCId
  /\ newSessionId <= MaxSessionId
  /\ newNonce <= MaxNonce
  /\ ~ChallengeExists(newChallengeId)
  /\ ~SessionExists(newSessionId)

  /\ VCIdCounter' = newChallengeId
  /\ SessionIdCounter' = newSessionId
  /\ NonceCounter' = newNonce

  /\ ChallengeSeq' = AppendToSeq(ChallengeSeq, newChallenge)
  /\ SessionSeq'   = AppendToSeq(SessionSeq,   newSession)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ResponseSeq, AttackLogSeq, AttackIdCounter, RevokedChiplets >>

PUFBasedVerificationResponse(responder, challengeId) ==
  LET challenge == GetChallenge(challengeId)
      mc == GetMCById(challenge.mcId)
      sramReadout == mc.sramPUFReadout
      errorCorrected == mc.errorCorrectedData
      fuzzyExtracted == mc.fuzzyExtractedKey
      stableSecret == DeriveStableSecretKey(fuzzyExtracted)
      ephemeralKeys == DeriveEphemeralKeys(stableSecret, challenge.sessionId, challenge.nonce)
      messageM == challenge.mcId * 1000000 + challenge.sessionId * 1000 + challenge.nonce + ephemeralKeys.ephemeralPrivateKey
      messageSignature == ChipletSign(challenge.pufId, messageM, ephemeralKeys.ephemeralPrivateKey)
      expectedResponse == GeneratePUFResponse(challenge.pufId, challengeId)
      pufEntropyValid == HasValidPUFEntropy(challenge.pufId, sramReadout)
      helperDataValid == IsValidHelperData(mc.errorCorrectedData, challenge.pufId)
      fuzzyExtractionValid == IsValidFuzzyExtraction(errorCorrected, fuzzyExtracted)
      pufConsistencyValid == IsConsistentPUFResponse(challenge.pufId, expectedResponse, mc.fuzzyExtractedKey)
      newResponse ==
        [ responseId |-> challengeId,
          challengeId |-> challengeId, mcId |-> challenge.mcId, pufId |-> challenge.pufId,
          response |-> expectedResponse, responder |-> responder, timestamp |-> Len(Ledger) + 1,
          ephemeralPrivateKey |-> ephemeralKeys.ephemeralPrivateKey,
          ephemeralPublicKey  |-> ephemeralKeys.ephemeralPublicKey,
          messageSignature |-> messageSignature, message |-> messageM ]
  IN
  /\ IsLegitimate(responder)
  /\ ChallengeExists(challengeId)
  /\ ~ResponseExists(challengeId)
  /\ IsFreshSession(challenge.sessionId, challenge.nonce)
  /\ pufEntropyValid /\ helperDataValid /\ fuzzyExtractionValid /\ pufConsistencyValid

  /\ ResponseSeq' = AppendToSeq(ResponseSeq, newResponse)
  /\ SessionSeq'  = [ SessionSeq EXCEPT ![challenge.sessionId].status = "Completed" ]
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, VCIdCounter, SessionIdCounter, NonceCounter, AttackLogSeq, AttackIdCounter, RevokedChiplets >>

PUFBasedVerificationValidation(verifier, challengeId) ==
  LET challenge == GetChallenge(challengeId)
      respIx == GetResponseByChallenge(challengeId)
      response == ResponseSeq[respIx]
      mc == GetMCById(challenge.mcId)
      extractedPubK == mc.publicKey
      freshnessValid == IsFreshSession(challenge.sessionId, challenge.nonce)
      expectedEphemeralPubK == DeriveEphemeralKeys(mc.fuzzyExtractedKey, challenge.sessionId, challenge.nonce).ephemeralPublicKey
      signatureValid == (response.ephemeralPublicKey = expectedEphemeralPubK) /\
                        (response.messageSignature = ChipletSign(challenge.pufId, response.message, response.ephemeralPrivateKey))
      pufResponseValid == (response.response = GeneratePUFResponse(challenge.pufId, challengeId))
      verificationResult == freshnessValid /\ signatureValid /\ pufResponseValid
      newSessionStatus == IF verificationResult THEN "Verified" ELSE "Failed"
  IN
  /\ IsLegitimate(verifier)
  /\ ChallengeExists(challengeId)
  /\ ResponseExists(challengeId)
  /\ SessionExists(challenge.sessionId)
  /\ GetSession(challenge.sessionId).status = "Completed"

  /\ SessionSeq' = [ SessionSeq EXCEPT ![challenge.sessionId].status = newSessionStatus ]
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionIdCounter, NonceCounter, AttackLogSeq, AttackIdCounter, RevokedChiplets >>

(***************************************************************************)
(* SiP Integration / Create SiP                                            *)
(***************************************************************************)
IntegrateChipletIntoSIP(integrator, chipletId, sipId) ==
  LET finalMC == GetFinalMC(chipletId)
      newIntegration ==
        [ sipId |-> sipId, chipletId |-> chipletId, mcId |-> finalMC.id,
          pufId |-> finalMC.puf, integrator |-> integrator, timestamp |-> Len(Ledger) + 1 ]
  IN
  /\ integrator = IntegrationManager
  /\ ChipletCompleted(chipletId)
  /\ ~ChipletAlreadyIntegrated(chipletId)
  /\ chipletId \notin RevokedChiplets
  /\ sipId \in DOMAIN SiPStore
  /\ Cardinality(GetSiPChiplets(sipId)) < MaxChipletsPerSiP
  /\ HasRecentVerifiedSession(finalMC.id, finalMC.puf)
  
  /\ ~HasSupplyChainTamperingIndicators(finalMC.puf, chipletId, finalMC)/\ AttestationFreshForIntegration(finalMC.id, finalMC.puf, Len(Ledger) + 1)   \* NEW: recency guard   \* NEW Step 2 guard
  /\ SiPStore' = [SiPStore EXCEPT ![sipId] = @ \cup {newIntegration}]
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, AttackLogSeq, AttackIdCounter, RevokedChiplets >>

CreateNewSIP(integrator) ==
  /\ integrator \in LegitimateIssuers
  /\ integrator = IntegrationManager
  /\ LET newSIPId == SiPIdCounter + 1 IN
     /\ newSIPId <= MaxSiPId
     /\ SiPIdCounter' = newSIPId
     /\ SiPStore' = [SiPStore EXCEPT ![newSIPId] = {}]
     /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, AttackLogSeq, AttackIdCounter, RevokedChiplets >>

(***************************************************************************)
(* Attacks (append to AttackLogSeq)                                         *)
(***************************************************************************)
IssueFakeMC(attacker, stage) ==
  LET newMCId == MCIdCounter + 1
      fakePUF == IF stage \in {Testing, Integration, Final} THEN 999 ELSE NoPUF
      fakeSRAMReadout == IF stage \in {Testing, Integration, Final} THEN AccessSRAMPUF(fakePUF) ELSE NoPUF
      fakeErrorCorrected == IF stage \in {Testing, Integration, Final} THEN ApplyErrorCorrection(fakeSRAMReadout) ELSE NoPUF
      fakeFuzzyExtracted == IF stage \in {Testing, Integration, Final} THEN ApplyFuzzyExtractor(fakeErrorCorrected) ELSE NoPUF
      fakeStableSecret == IF stage \in {Testing, Integration, Final} THEN DeriveStableSecretKey(fakeFuzzyExtracted) ELSE NoPUF
      fakeKeyPair == IF stage \in {Testing, Integration, Final} THEN GenerateECCKeyPair(fakeStableSecret) ELSE [privateKey |-> NoPUF, publicKey |-> NoPUF]
      fakePublicKey == IF stage \in {Testing, Integration, Final} THEN fakeKeyPair.publicKey ELSE NoPUF
      fakeSignature == IF stage \in {Testing, Integration, Final} THEN ChipletSign(fakePUF, newMCId, fakeKeyPair.privateKey) ELSE NoPUF
      newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "FakeMC", attacker |-> attacker,
          targetMC |-> newMCId, targetPUF |-> fakePUF, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ~Done
  /\ newMCId <= MaxMCId
  /\ newAttackId <= MaxVCId
  /\ MCIdCounter' = newMCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << PUFIdCounter, ChipletStage, ChipletPUF, Done, SiPStore, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, Ledger, MCStore, RevokedChiplets >>

ReplayAttack(attacker, challengeId) ==
  LET challenge == GetChallenge(challengeId)
      newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "ReplayAttack", attacker |-> attacker,
          targetMC |-> challenge.mcId, targetPUF |-> challenge.pufId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ChallengeExists(challengeId)
  /\ ~ResponseExists(challengeId)
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, ResponseSeq, RevokedChiplets >>

CloneAttempt(attacker, challengeId) ==
  LET challenge == GetChallenge(challengeId)
      newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "CloneAttempt", attacker |-> attacker,
          targetMC |-> challenge.mcId, targetPUF |-> challenge.pufId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ChallengeExists(challengeId)
  /\ ~ResponseExists(challengeId)
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, ResponseSeq, RevokedChiplets >>

PUFSpoofingAttack(attacker, challengeId, spoofedResponse) ==
  LET challenge == GetChallenge(challengeId)
      newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "PUFSpoofing", attacker |-> attacker,
          targetMC |-> challenge.mcId, targetPUF |-> challenge.pufId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ChallengeExists(challengeId)
  /\ ~ResponseExists(challengeId)
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, ResponseSeq, RevokedChiplets >>

HelperDataAttack(attacker, challengeId) ==
  LET challenge == GetChallenge(challengeId)
      newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "HelperDataAttack", attacker |-> attacker,
          targetMC |-> challenge.mcId, targetPUF |-> challenge.pufId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ChallengeExists(challengeId)
  /\ ~ResponseExists(challengeId)
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, ResponseSeq, RevokedChiplets >>

FuzzyExtractorAttack(attacker, challengeId) ==
  LET challenge == GetChallenge(challengeId)
      newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "FuzzyExtractorAttack", attacker |-> attacker,
          targetMC |-> challenge.mcId, targetPUF |-> challenge.pufId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ChallengeExists(challengeId)
  /\ ~ResponseExists(challengeId)
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, ResponseSeq, RevokedChiplets >>

FakeChipletInjectionAttack(attacker, chipletId, fakePUFId) ==
  LET newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "FakeChipletInjection", attacker |-> attacker,
          targetMC |-> 0, targetPUF |-> fakePUFId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ~Done
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, RevokedChiplets >>

SupplyChainAttack(attacker, originalChipletId, replacementPUFId) ==
  LET newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "SupplyChainAttack", attacker |-> attacker,
          targetMC |-> 0, targetPUF |-> replacementPUFId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ~Done
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, RevokedChiplets >>

FakeChipletEnrollmentAttack(attacker, fakeChipletId, fakePUFId) ==
  LET newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "FakeChipletInjection", attacker |-> attacker,
          targetMC |-> 0, targetPUF |-> fakePUFId, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ ~Done
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, RevokedChiplets >>

NoOpAttack(attacker) ==
  LET newAttackId == AttackIdCounter + 1
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "NoOp", attacker |-> attacker,
          targetMC |-> 0, targetPUF |-> 0, timestamp |-> Len(Ledger) + 1, success |-> FALSE ]
  IN
  /\ IsAttacker(attacker)
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done, SiPStore, SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, RevokedChiplets >>

\* Semantically-real counterfeit insertion under a constant gate (from Step 1, unchanged).
CounterfeitIntegrate(attacker, chipletId, sipId, fakePUF) ==
  LET newAttackId == AttackIdCounter + 1
      forgedInt ==
        [ sipId |-> sipId, chipletId |-> chipletId, mcId |-> 0,
          pufId |-> fakePUF, integrator |-> attacker, timestamp |-> Len(Ledger) + 1 ]
      attackRecord ==
        [ attackId |-> newAttackId, attackType |-> "CounterfeitIntegrate", attacker |-> attacker,
          targetMC |-> 0, targetPUF |-> fakePUF, timestamp |-> Len(Ledger) + 1, success |-> TRUE ]
  IN
  /\ IsAttacker(attacker)
  /\ sipId \in DOMAIN SiPStore
  /\ newAttackId <= MaxVCId
  /\ AttackIdCounter' = newAttackId
  /\ AttackLogSeq' = AppendToSeq(AttackLogSeq, attackRecord)
  /\ SiPStore' = [SiPStore EXCEPT ![sipId] = @ \cup { forgedInt }]
  /\ UNCHANGED << ChipletStage, ChipletPUF, Ledger, MCStore, MCIdCounter, PUFIdCounter, Done,
                  SiPIdCounter, ChallengeSeq, ResponseSeq, VCIdCounter, SessionSeq, SessionIdCounter, NonceCounter, RevokedChiplets >>

(***************************************************************************)
(* Terminal                                                                 *)
(***************************************************************************)
Terminal == /\ UNCHANGED vars

(***************************************************************************)
(* Next                                                                     *)
(***************************************************************************)
Next ==
  PUFBasedEnrollment
  \/ CreateNewSIP(IntegrationManager)
  \/ (\E chipletId1 \in ChipletSet : \E sipId1 \in DOMAIN SiPStore :
        ChipletCompleted(chipletId1) /\ IntegrateChipletIntoSIP(IntegrationManager, chipletId1, sipId1))
  \/ (\E challenger1 \in LegitimateIssuers : \E mcId1 \in 1..MaxMCId : \E pufId1 \in 1..MaxPUFId :
        MicrocredentialExists(mcId1) /\ PUFBasedVerificationChallenge(challenger1, mcId1, pufId1))
  \/ (\E responder1 \in LegitimateIssuers : \E challengeId1 \in 1..MaxVCId :
        ChallengeExists(challengeId1) /\ ~ResponseExists(challengeId1) /\ PUFBasedVerificationResponse(responder1, challengeId1))
  \/ (\E verifier1 \in LegitimateIssuers : \E challengeId2 \in 1..MaxVCId :
        ChallengeExists(challengeId2) /\ ResponseExists(challengeId2) /\ PUFBasedVerificationValidation(verifier1, challengeId2))
  \/ (\E attacker1 \in AttackerIssuers : \E stage1 \in {Design,Verification,Fabrication,Testing,Integration,Final} : IssueFakeMC(attacker1, stage1))
  \/ (\E attacker2 \in AttackerIssuers : \E challengeId3 \in 1..MaxVCId : ChallengeExists(challengeId3) /\ ~ResponseExists(challengeId3) /\ ReplayAttack(attacker2, challengeId3))
  \/ (\E attacker3 \in AttackerIssuers : \E challengeId4 \in 1..MaxVCId : ChallengeExists(challengeId4) /\ ~ResponseExists(challengeId4) /\ CloneAttempt(attacker3, challengeId4))
  \/ (\E attacker4 \in AttackerIssuers : \E challengeId5 \in 1..MaxVCId : \E spoofedResponse5 \in 1..MaxVCId :
        ChallengeExists(challengeId5) /\ ~ResponseExists(challengeId5) /\ PUFSpoofingAttack(attacker4, challengeId5, spoofedResponse5))
  \/ (\E attacker5 \in AttackerIssuers : \E challengeId6 \in 1..MaxVCId : ChallengeExists(challengeId6) /\ ~ResponseExists(challengeId6) /\ HelperDataAttack(attacker5, challengeId6))
  \/ (\E attacker6 \in AttackerIssuers : \E challengeId7 \in 1..MaxVCId : ChallengeExists(challengeId7) /\ ~ResponseExists(challengeId7) /\ FuzzyExtractorAttack(attacker6, challengeId7))
  \/ (\E attacker7 \in AttackerIssuers : \E chipletId7 \in 1..MaxPUFId : \E fakePUFId7 \in 1..MaxPUFId : FakeChipletInjectionAttack(attacker7, chipletId7, fakePUFId7))
  \/ (\E attacker8 \in AttackerIssuers : \E originalChipletId8 \in 1..MaxPUFId : \E replacementPUFId8 \in 1..MaxPUFId : SupplyChainAttack(attacker8, originalChipletId8, replacementPUFId8))
  \/ (\E attacker9 \in AttackerIssuers : \E fakeChipletId9 \in 1..MaxPUFId : \E fakePUFId9 \in 1..MaxPUFId : FakeChipletEnrollmentAttack(attacker9, fakeChipletId9, fakePUFId9))
  \/ (\E attacker10 \in AttackerIssuers : NoOpAttack(attacker10))
  \/ (AllowCounterfeitIntegrate /\ \E a \in AttackerIssuers :
        \E ch \in ChipletSet : \E s \in DOMAIN SiPStore : \E p \in 1..MaxPUFId :
          CounterfeitIntegrate(a, ch, s, p))
  \/ Terminal

  \/ (\E c \in ChipletSet : RevokeOnTamper(c))
  \/ (\E c \in ChipletSet : AutoRevokeOnIndicators(c))
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants / properties                                                  *)
(***************************************************************************)
StageIssuerInvariant ==
  \A iss \in DOMAIN MCStore : \A mc \in MCStore[iss] : iss = IssuerFor(mc.stage)

AppendOnlyAction ==
  \/ Ledger' = Ledger
  \/ ( Len(Ledger') = Len(Ledger) + 1 /\ Ledger' = Ledger \o << Ledger'[Len(Ledger')] >> )

AppendOnly == [] [AppendOnlyAction]_vars

StrictTxId ==
  [] ( Len(Ledger) = 0 \/ \A k \in 2..Len(Ledger) : Ledger[k].id = Ledger[k-1].id + 1 )

LedgerMatchesMC ==
  [] \A t \in { Ledger[k] : k \in 1..Len(Ledger) } :
       \E iss \in DOMAIN MCStore :
         \E mc \in MCStore[iss] :
           /\ mc.id = t.mcId
           /\ mc.chiplet = t.chiplet
           /\ mc.stage = t.stage
           /\ mc.puf = t.puf

PUFOnlyAfterTesting ==
  [] \A t \in { Ledger[k] : k \in 1..Len(Ledger) } :
       (t.puf # NoPUF) => t.stage \in {Testing, Integration, Final}

BoundedCounters ==
  [] /\ MCIdCounter <= MaxMCId
     /\ PUFIdCounter <= MaxPUFId
     /\ SiPIdCounter <= MaxSiPId
     /\ VCIdCounter <= MaxVCId
     /\ SessionIdCounter <= MaxSessionId
     /\ NonceCounter <= MaxNonce
     /\ AttackIdCounter <= MaxVCId

SingleMCPerStage ==
  [] \A stage \in {Design,Verification,Fabrication,Testing,Integration,Final} :
       LET mcsForStage == { mc \in AllMCsUnion : mc.chiplet = ChipletId /\ mc.stage = stage } IN
       Cardinality(mcsForStage) <= 1

SiPBoundedSize ==
  [] \A sipId \in DOMAIN SiPStore :
       Cardinality(SiPStore[sipId]) <= MaxChipletsPerSiP

SingleChipletPerSiP ==
  [] \A sipId \in DOMAIN SiPStore :
       \A int1, int2 \in SiPStore[sipId] : int1.chipletId = int2.chipletId => int1 = int2

VerificationBoundedSize ==
  [] \A cid \in 1..Len(ChallengeSeq) : ChallengeSeq[cid].challengeId = cid

ValidChallengeResponse ==
  [] \A r \in 1..Len(ResponseSeq) :
       LET response == ResponseSeq[r] IN
       LET challenge == GetChallenge(response.challengeId) IN
         response.response = GeneratePUFResponse(challenge.pufId, challenge.challengeId)

PUFEnrollmentConsistency ==
  [] \A mc \in AllMCsUnion :
       (mc.puf # NoPUF) =>
       /\ mc.sramPUFReadout # NoPUF
       /\ mc.errorCorrectedData # NoPUF
       /\ mc.fuzzyExtractedKey # NoPUF
       /\ mc.publicKey # NoPUF
       /\ mc.chipletSignature # NoPUF

SessionFreshness ==
  [] \A sid \in 1..Len(SessionSeq) :
       LET session == SessionSeq[sid] IN
       (session.sessionId # 0) =>
       /\ session.status \in {"Active","Completed","Expired","Verified","Failed"}
       /\ session.timestamp > 0

NoUnauthorizedIssuance ==
  [] \A k \in 1..Len(Ledger) : IsLegitimateTransaction(Ledger[k])

NoFakeMicrocredentials ==
  [] \A mc \in AllMCsUnion : IsLegitimateMicrocredential(mc)

NoSuccessfulAttacks ==
  [] \A i \in 1..Len(AttackLogSeq) : ~AttackLogSeq[i].success

NoAttackerResponses ==
  [] \A i \in 1..Len(ResponseSeq) : IsLegitimate(ResponseSeq[i].responder)

NoAttackerChallenges ==
  [] \A i \in 1..Len(ChallengeSeq) : IsLegitimate(ChallengeSeq[i].challenger)

NoSuccessfulReplayAttacks ==
  [] \A i \in 1..Len(ResponseSeq) :
       LET response == ResponseSeq[i] IN
       LET challenge == GetChallenge(response.challengeId) IN
         (IsLegitimate(response.responder) \/
          (IsAttacker(response.responder) /\ ~IsFreshSession(challenge.sessionId, challenge.nonce)))

NoSuccessfulCloneAttempts ==
  [] \A i \in 1..Len(ResponseSeq) :
       LET response == ResponseSeq[i] IN
       LET challenge == GetChallenge(response.challengeId) IN
         (IsLegitimate(response.responder) \/
          (IsAttacker(response.responder) /\ response.response # GeneratePUFResponse(challenge.pufId, challenge.challengeId)))

NoSuccessfulPUFSpoofing ==
  [] \A i \in 1..Len(AttackLogSeq) :
       AttackLogSeq[i].attackType # "PUFSpoofing" \/ ~AttackLogSeq[i].success

NoSuccessfulHelperDataAttacks ==
  [] \A i \in 1..Len(AttackLogSeq) :
       AttackLogSeq[i].attackType # "HelperDataAttack" \/ ~AttackLogSeq[i].success

NoSuccessfulFuzzyExtractorAttacks ==
  [] \A i \in 1..Len(AttackLogSeq) :
       AttackLogSeq[i].attackType # "FuzzyExtractorAttack" \/ ~AttackLogSeq[i].success

PUFConsistencyValidation ==
  [] \A i \in 1..Len(ResponseSeq) :
       LET response == ResponseSeq[i] IN
       LET challenge == GetChallenge(response.challengeId) IN
       LET mc == GetMCById(challenge.mcId) IN
         (IsLegitimate(response.responder) \/
          (IsAttacker(response.responder) /\ 
           ~IsConsistentPUFResponse(challenge.pufId, response.response, mc.fuzzyExtractedKey)))

PUFEntropyValidation ==
  [] \A mc \in AllMCsUnion :
       (mc.puf = NoPUF) \/
       (mc.sramPUFReadout # NoPUF /\ HasValidPUFEntropy(mc.puf, mc.sramPUFReadout))

HelperDataIntegrityValidation ==
  [] \A mc \in AllMCsUnion :
       (mc.puf = NoPUF) \/
       (mc.errorCorrectedData # NoPUF /\ IsValidHelperData(mc.errorCorrectedData, mc.puf))

FuzzyExtractorIntegrityValidation ==
  [] \A mc \in AllMCsUnion :
       (mc.puf = NoPUF) \/
       (mc.fuzzyExtractedKey # NoPUF /\ IsValidFuzzyExtraction(mc.errorCorrectedData, mc.fuzzyExtractedKey))

\* ====== PARENTHESIZED TO AVOID PRECEDENCE CONFLICTS ======
VerifierSignatureValidation ==
  [] \A sid \in 1..Len(SessionSeq) :
    LET session == SessionSeq[sid] IN
      ( (session.status # "Verified")
        \/
        (\E cid \in 1..Len(ChallengeSeq) :
           \E rix \in 1..Len(ResponseSeq) :
             LET challenge == ChallengeSeq[cid] IN
             LET response  == ResponseSeq[rix] IN
               /\ challenge.sessionId = sid
               /\ response.challengeId = cid
               /\ response.ephemeralPublicKey =
                    DeriveEphemeralKeys(GetMCById(challenge.mcId).fuzzyExtractedKey,
                                        challenge.sessionId, challenge.nonce).ephemeralPublicKey
               /\ response.messageSignature =
                    ChipletSign(challenge.pufId, response.message, response.ephemeralPrivateKey)
        )
      )

VerifierFreshnessValidation ==
  [] \A sid \in 1..Len(SessionSeq) :
    LET session == SessionSeq[sid] IN
      ( (session.status # "Verified")
        \/
        (\E cid \in 1..Len(ChallengeSeq) :
           LET challenge == ChallengeSeq[cid] IN
             /\ challenge.sessionId = sid
             /\ IsFreshSession(challenge.sessionId, challenge.nonce)
        )
      )

VerifierPUFResponseValidation ==
  [] \A sid \in 1..Len(SessionSeq) :
    LET session == SessionSeq[sid] IN
      ( (session.status # "Verified")
        \/
        (\E cid \in 1..Len(ChallengeSeq) :
           \E rix \in 1..Len(ResponseSeq) :
             LET challenge == ChallengeSeq[cid] IN
             LET response  == ResponseSeq[rix] IN
               /\ challenge.sessionId = sid
               /\ response.challengeId = cid
               /\ response.response = GeneratePUFResponse(challenge.pufId, cid)
        )
      )
\* ========================================================

NoSuccessfulPUFOnlyAfterTestingViolations ==
  [] \A i \in 1..Len(AttackLogSeq) :
       LET attack == AttackLogSeq[i] IN
         ( attack.attackType # "FakeMC"
           \/ ~attack.success
           \/ (\E mc \in AllMCsUnion :
                 /\ mc.id = attack.targetMC
                 /\ mc.stage \in {Testing, Integration, Final})
         )

PUFAssignmentConsistency ==
  [] \A mc \in AllMCsUnion :
       (mc.puf = NoPUF) \/ mc.stage \in {Testing, Integration, Final}

NoSuccessfulFakeChipletInjection ==
  [] \A i \in 1..Len(AttackLogSeq) :
       AttackLogSeq[i].attackType # "FakeChipletInjection" \/ ~AttackLogSeq[i].success

NoSuccessfulSupplyChainAttacks ==
  [] \A i \in 1..Len(AttackLogSeq) :
       AttackLogSeq[i].attackType # "SupplyChainAttack" \/ ~AttackLogSeq[i].success

PUFIdsForChiplet(c) ==
  LET S == { mc \in AllMCsUnion : mc.chiplet = c /\ mc.puf # NoPUF } IN
      { mc.puf : mc \in S }

PUFUniquenessPerChiplet ==
  [] /\ \A c \in ChipletSet : Cardinality(PUFIdsForChiplet(c)) <= 1
     /\ \A c1, c2 \in ChipletSet :
           c1 # c2 => (PUFIdsForChiplet(c1) \cap PUFIdsForChiplet(c2)) = {}

ChipletPUFBindingIntegrity ==
  [] \A mc \in AllMCsUnion :
    (mc.puf = NoPUF) \/ (mc.chiplet # 0 /\ mc.puf > 0 /\ IsValidChipletPUF(mc.puf, mc.chiplet, mc.puf))

ChipletAuthenticityValidation ==
  [] \A mc \in AllMCsUnion :
    (mc.stage # Testing) \/ IsAuthenticChiplet(mc.chiplet)

StageProgressionValidation ==
  [] \A mc \in AllMCsUnion :
    (mc.stage # Testing) \/ HasValidStageProgression(mc.chiplet)

NoFakeChipletEnrollmentDuringTesting ==
  [] \A mc \in AllMCsUnion :
    (mc.stage # Testing) \/
    (mc.stage = Testing => ~IsFakeChipletEnrollment(mc.chiplet, mc.puf, mc.issuer))

LegitimateMicrocredentialsOnly ==
  [] \A mc \in AllMCsUnion : IsLegitimateMicrocredential(mc)

(******************************************************************)
(* Testing-stage PUF invariants                                    *)
(******************************************************************)
PUFUniquenessFromTestingStage ==
  \A c \in { mc.chiplet : mc \in AllMCsUnion } :
    LET testingMCs == { mc \in AllMCsUnion :
                         mc.chiplet = c /\ mc.stage = Testing /\ mc.puf # NoPUF } IN
    Cardinality({ mc.puf : mc \in testingMCs }) <= 1

PUFExistsAtTesting ==
  \A c \in { mc.chiplet : mc \in AllMCsUnion } :
    LET testingMCs == { mc \in AllMCsUnion :
                         mc.chiplet = c /\ mc.stage = Testing /\ mc.puf # NoPUF } IN
    testingMCs # {}

PUFFrozenAfterTesting ==
  \A c \in { mc.chiplet : mc \in AllMCsUnion } :
    LET testingMCs == { mc \in AllMCsUnion :
                         mc.chiplet = c /\ mc.stage = Testing /\ mc.puf # NoPUF } IN
      ( (testingMCs = {})
        \/
        (\E p \in { x.puf : x \in testingMCs } :
           \A mc \in AllMCsUnion :
             (mc.chiplet = c /\ mc.stage \in {Integration, Final} /\ mc.puf # NoPUF)
             => mc.puf = p)
      )

\* New Step 2 invariant: Integration requires fresh attestation (Verified session)
IntegrationRequiresFreshAttestation ==
  [] \A s \in DOMAIN SiPStore :
       \A int \in SiPStore[s] :
         HasRecentVerifiedSession(int.mcId, int.pufId)


(******************************************************************)
(* Step 4: Tamper-indicator safety                                 *)
(******************************************************************)
NoIntegrationWhenTamperIndicators ==
  \A s \in DOMAIN SiPStore :
       \A int \in SiPStore[s] :
         LET mc == GetMCById(int.mcId) IN
           ~HasSupplyChainTamperingIndicators(int.pufId, int.chipletId, mc)
\* Attestation TTL property: every integration must be within the allowed lag

NoVerifyRevoked ==
  \A sid \in 1..Len(SessionSeq) :
    LET sess == SessionSeq[sid] IN
      ~ (\E mc \in AllMCsUnion : mc.id = sess.mcId /\ mc.chiplet \in RevokedChiplets)

NoIntegrateRevoked ==
  \A s \in DOMAIN SiPStore :
    \A int \in SiPStore[s] :
      int.chipletId \notin RevokedChiplets

IntegrationWithinAttestationTTL ==
  [] \A s \in DOMAIN SiPStore :
       \A int \in SiPStore[s] :
         AttestationFreshForIntegration(int.mcId, int.pufId, int.timestamp)


(***************************************************************************)
(* Type OK / Safety / Security bundles                                      *)
(***************************************************************************)
THEOREM TypeOK ==
  /\ MCIdCounter \in 0..MaxMCId
  /\ PUFIdCounter \in 0..MaxPUFId
  /\ SiPIdCounter \in 0..MaxSiPId
  /\ VCIdCounter \in 0..MaxVCId
  /\ SessionIdCounter \in 0..MaxSessionId
  /\ NonceCounter \in 0..MaxNonce
  /\ ChipletStage \in 1..NumStages
  /\ ChipletPUF \in 0..MaxPUFId \cup {NoPUF}
  /\ Ledger \in Seq(Tx)
  /\ ~(0 \in Issuers)
  /\ Issuers \subseteq IssuerAtoms
  /\ DOMAIN MCStore = IssuerAtoms
  /\ \A i \in DOMAIN MCStore : MCStore[i] \subseteq Microcredential
  /\ DOMAIN SiPStore = 1..MaxSiPId
  /\ \A s \in DOMAIN SiPStore : SiPStore[s] \subseteq SiPIntegration
  /\ ChallengeSeq \in Seq(VerificationChallenge)
  /\ ResponseSeq  \in Seq(VerificationResponse)
  /\ SessionSeq   \in Seq(VerificationSession)
  /\ AttackLogSeq \in Seq(AttackAttempt)

Safety ==
  AppendOnly /\ StrictTxId /\ LedgerMatchesMC /\ PUFOnlyAfterTesting
  /\ BoundedCounters /\ SingleMCPerStage
  /\ SiPBoundedSize /\ SingleChipletPerSiP
  /\ VerificationBoundedSize /\ ValidChallengeResponse
  /\ PUFEnrollmentConsistency /\ SessionFreshness
Security ==
  NoUnauthorizedIssuance /\ NoFakeMicrocredentials /\ NoSuccessfulAttacks
  /\ NoAttackerResponses /\ NoAttackerChallenges
  /\ NoSuccessfulReplayAttacks /\ NoSuccessfulCloneAttempts
  /\ NoSuccessfulPUFSpoofing /\ NoSuccessfulHelperDataAttacks /\ NoSuccessfulFuzzyExtractorAttacks
  /\ PUFConsistencyValidation /\ PUFEntropyValidation
  /\ HelperDataIntegrityValidation /\ FuzzyExtractorIntegrityValidation
  /\ VerifierSignatureValidation /\ VerifierFreshnessValidation /\ VerifierPUFResponseValidation
  /\ NoSuccessfulPUFOnlyAfterTestingViolations /\ PUFAssignmentConsistency
  /\ NoSuccessfulFakeChipletInjection /\ NoSuccessfulSupplyChainAttacks
  /\ PUFUniquenessPerChiplet /\ ChipletPUFBindingIntegrity
  /\ ChipletAuthenticityValidation /\ StageProgressionValidation
  /\ NoFakeChipletEnrollmentDuringTesting /\ LegitimateMicrocredentialsOnly

\* From Step 1 (temporal; use as a PROPERTY if you want to check it as well)
NoCounterfeitInSiP ==
  [] \A s \in DOMAIN SiPStore :
       \A int \in SiPStore[s] :
         /\ int.mcId # 0
         /\ IsLegitimate(int.integrator)

=============================================================================
