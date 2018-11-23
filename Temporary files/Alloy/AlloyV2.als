open util/integer

sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

------------- DATA4HELP SIGNATURES -------------

sig FiscalCode {}

sig Time {}

sig Location {
	time: one Time
}

sig HealthStatus {
	time: one Time,
	parameter: some Parameter
}

sig AcquisitionSetData {
	locationAcquisition: some Location,
	healthStatusAcquisition: some HealthStatus
}

sig IndividualPrivacyPolicy {
	IndividualMonitoring: one Bool --Full privacy policy is accepted (individual monitoring)
}

sig UserAttributes {	
	address: one Location, --Location where user lives
}

sig GroupAttributes {	
	area: some Location, --Area where users live
}

sig User {
	fiscalCode: one FiscalCode,
	policy: one IndividualPrivacyPolicy, --Status of policy acceptance
	credentials: one UserAttributes, --User's credentials
	retrievedData: lone AcquisitionSetData --User's set of acquisition acquired
}

sig ThirdParty {}

abstract sig InformationRequest {
	partyApplicant: one ThirdParty, --Third party applicant}			
}

sig IndividualRequest extends InformationRequest {
	fiscalCode: one FiscalCode --Tracked User's fiscal code  (lone beacuse group mode don't have it)
}

sig GroupRequest extends InformationRequest {
	groupAttributes: one GroupAttributes, --Users' attributes on group search (lone beacuse individual mode don't have it)
}

abstract sig InformationAnswer {}

sig IndividualInformationAnswer extends InformationAnswer {
	individualRequest: one IndividualRequest,
	user: one User,
	acquisitionData: one AcquisitionSetData
} {user.policy.IndividualMonitoring = True}

sig GroupInformationAnswer extends InformationAnswer {
	groupRequest: one GroupRequest,
	acquisitionData: some AcquisitionSetData
} {#acquisitionData > 3}	--  3 stands for 1000 

---------- AUTOMATEDSOS SIGNATURES ----------

sig Parameter {
	value : one Int,
	threshold : one Int
}

sig FirstAid {}
	
sig Report {
	user: one User,
	receiver: one FirstAid
}

sig AmbulanceRequest {
	time: one Time,
	report : one Report
}

------------ TRACK4RUN SIGNATURES ------------

sig Map {
	athletesLocation: some Location,
	runEvent : one Run
}

sig Run {
	athletes: some Track4RunUser,
	map: lone Map
} 

sig Track4RunUser extends User {
	watchingRun: lone Run
}

--------------- DATA4HELP FATCS ---------------

fact NoAloneBool {
	all b: Bool | some i: IndividualPrivacyPolicy | b in i.IndividualMonitoring
}

fact HealthStatusInAcquisitionSetData {
	all h: HealthStatus | some a: AcquisitionSetData | h in a.healthStatusAcquisition
}

fact NoSharedHealthStatusBetweenAcquisitionSetData {
	 all s: AcquisitionSetData | all h1,h2: HealthStatus | (h1 in s.healthStatusAcquisition and h2 in s.healthStatusAcquisition) implies h1 = h2
}

fact PrivacyPolicyInUser {
	all p: IndividualPrivacyPolicy | one u: User | p in u.policy
}

fact UserAttInUser {
	all ua: UserAttributes | one u: User | ua in u.credentials
}

fact GroupAttributesInGroupRequest {
	all g: GroupAttributes | one ga: GroupRequest | g in ga.groupAttributes
}

fact ThirdPartyInRequest {
	all t: ThirdParty | some r:InformationRequest | t in r.partyApplicant
}

fact AcquisitionDataInUser {
	all a: AcquisitionSetData | one u: User | a in u.retrievedData
}

fact NoTwoAnswerForSameIndividualRequest {
	all disj i1, i2: IndividualInformationAnswer | i1.individualRequest != i2.individualRequest 
}

fact NoTwoAnswerForSameGroupRequest {
	all disj i1, i2: GroupInformationAnswer | i1.groupRequest != i2.groupRequest 
}

fact NoTwoEqualFiscalCode {
	all disj u1,u2 : User | u1.fiscalCode != u2.fiscalCode
}

fact AnswerToRequestWithRightFiscalCode {
	all i: IndividualInformationAnswer | i.user.fiscalCode = i.individualRequest.fiscalCode
}

fact RightAcquisitionDataAnswerToRequest {
	all i: IndividualInformationAnswer | one u: User | (i.user = u) and (u.retrievedData = i.acquisitionData)
}

------------- AUTOMATEDSOS FACTS -------------

fact NoAloneFirstAid {
	all f: FirstAid | some r: Report | f in r.receiver
}

--------------- TRACK4RUN FACTS ---------------

fact RunnerNotSpectator {
	all disj t1, t2 :Track4RunUser | all r: Run |  (r in t1.watchingRun and t2 in r.athletes) implies ( t1 != t2)
}

fact TwoRunnersNotSameLocation {
	all m:Map | all l1,l2: Location | ((l1 in m.athletesLocation) and (l2 in m.athletesLocation)) implies l1 != l2
}

------------- DATA4HELP PREDICATES -------------

pred IndividualAnswerRegardOnlyPolicyAgreedUsers {
	all i: IndividualInformationAnswer | i.user.policy.IndividualMonitoring = True
}

pred MinimumGroupMembers {
	all g: GroupInformationAnswer | #g.acquisitionData > 3	--  3 stands for 1000 
}

------------TRACK4RUN PREDICATES --------------

fact RunnerMustAcceptIndividualPolicy {
	all r: Track4RunUser | r.policy.IndividualMonitoring = True
}

----------- AUTOMATEDSOS PREDICATES -----------

pred AmbulanceRequestSent {
	all h: HealthStatus | all p: Parameter | one a: AmbulanceRequest | one u: User |
			((h.parameter = p) and (p.value < p.threshold)) implies 
 					((a.time = h.time) and (h in u.retrievedData.healthStatusAcquisition and a.report.user = u))
}

------------- TRACK4RUN PREDICATES -------------

pred SameNumberLocationsAndRunners {
	all m:Map | all r: Run | ((m in r.map) implies (#m.athletesLocation = #r.athletes )
										and r.athletes.retrievedData.locationAcquisition in m.athletesLocation)
}

------------- DATA4HELP ASSERTIONS -------------

assert UserPrivacy {
	IndividualAnswerRegardOnlyPolicyAgreedUsers and MinimumGroupMembers
}

----------- AUTOMATEDSOS ASSERTIONS -----------

assert AmbulanceEmergency {
	IndividualAnswerRegardOnlyPolicyAgreedUsers
}

------------- TRACK4RUN ASSERTIONS -------------

assert WatchingAthletesPosition {
	SameNumberLocationsAndRunners
}

-------------------------------------------------

pred show{}
run show for 4 but exactly 3 HealthStatus, exactly 3 AcquisitionSetData, exactly 3 IndividualInformationAnswer
check WatchingAthletesPosition for 20
check AmbulanceEmergency for 20
check UserPrivacy for 20


