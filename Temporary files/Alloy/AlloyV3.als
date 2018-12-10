open util/integer

------------- DATA4HELP SIGNATURES -------------

sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

sig SecurityNumber {}

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
	securityNumber: one SecurityNumber,
	policy: one IndividualPrivacyPolicy, --Status of policy acceptance
	credentials: one UserAttributes, --User's credentials
	retrievedData: lone AcquisitionSetData --User's set of acquisition acquired
}

sig ThirdParty {}

abstract sig InformationRequest {
	partyApplicant: one ThirdParty, --Third party applicant}			
}

sig IndividualRequest extends InformationRequest {
	securityNumber: one SecurityNumber --Tracked User's fiscal code  (lone beacuse group mode don't have it)
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
}

sig Run {
	athletes: some Track4RunUser,
	map: one Map
} {#athletes > 1}

sig Track4RunUser extends User {}

sig Track4RunSpectator extends Track4RunUser {
	watchingRun: one Run
}

-------------------------------------------------------- FACTS --------------------------------------------------------

--------------- DATA4HELP FACTS ---------------

fact NoAloneBool {
	all b: Bool | some i: IndividualPrivacyPolicy | b in i.IndividualMonitoring
}


fact HealthStatusInAcquisitionSetData {
	all h: HealthStatus | one a: AcquisitionSetData | h in a.healthStatusAcquisition
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
	all disj u1,u2 : User | u1.securityNumber != u2.securityNumber 
}
fact AnswerToRequestWithRightFiscalCode {
	all i: IndividualInformationAnswer | i.user.securityNumber = i.individualRequest.securityNumber 
}

fact RightAcquisitionDataAnswerToRequest {
	all i: IndividualInformationAnswer | one u: User | (i.user = u) and (u.retrievedData = i.acquisitionData)
}

fact NoMoreThanOneHealthStatusWithSameTimeForTheSameIndividual {
	all h1, h2: HealthStatus | all u: User | (h1 in u.retrievedData.healthStatusAcquisition and h2 in u.retrievedData.healthStatusAcquisition 
	and h1.time = h2.time) implies h1 = h2 
}

fact NoMoreThanOneLocationWithSameTimeForTheSameIndividual {
	all l1,l2: Location | all u: User | (l1 in u.retrievedData.locationAcquisition and l2 in u.retrievedData.locationAcquisition
	and l1.time = l2.time) implies l1 = l2 
}

------------- AUTOMATEDSOS FACTS -------------


fact NoAloneFirstAid {
	all f: FirstAid | some r: Report | f in r.receiver
}

fact AmbulanceRequestSentThereIsParamDown {
	 all a: AmbulanceRequest | some h: HealthStatus | some p: Parameter |
			(h in a.report.user.retrievedData.healthStatusAcquisition and a.time = h.time and p in h.parameter and p.value < p.threshold)
}

fact AmbulanceRequestSent {
	all h: HealthStatus | one a: AmbulanceRequest |
			((h.parameter.value < h.parameter.threshold)) implies 
 					((a.time = h.time) and (h in a.report.user.retrievedData.healthStatusAcquisition))
}


--------------- TRACK4RUN FACTS ---------------

fact RunnerNotSpectator {
	all t1, t2 :Track4RunSpectator | all r: Run |  (r in t1.watchingRun and t2 in r.athletes) implies ( t1 != t2)
}

fact NoLocationInMoreMaps {
	all l: Location | all m1, m2: Map | (l in m1.athletesLocation and l in m2.athletesLocation) implies m1 = m2
}


fact EveryLocationInAMapHasTheSameTime {
	all l1,l2: Location | all m: Map | (l1 in m.athletesLocation and l2 in m.athletesLocation) implies l1.time = l2.time
}

fact NoMapWithoutRun {
	all m: Map | one r: Run | r.map = m
}

fact SameNumberLocationsAndRunners {
	all m:Map | all r: Run | (m in r.map)  implies (#m.athletesLocation = #r.athletes )
}


fact MapLocationsAreRunnersLocations {
	all t : Track4RunUser | all r: Run | some l: Location |  t in r.athletes implies  (l in r.map.athletesLocation and l in t.retrievedData.locationAcquisition)
}

fact MapLocationsAreRunnersLocations2 {
	 all r: Run | all l: Location | some t : Track4RunUser | l in r.map.athletesLocation implies (t in r.athletes and l in t.retrievedData.locationAcquisition)
}

-------------------------------------------------------- PREDICATES --------------------------------------------------------

------------- DATA4HELP PREDICATES -------------

pred IndividualAnswerRegardOnlyPolicyAgreedUsers {
	all i: IndividualInformationAnswer | i.user.policy.IndividualMonitoring = True
}

pred MinimumGroupMembers {
	all g: GroupInformationAnswer | #g.acquisitionData > 3	--  3 stands for 1000 
}

----------- AUTOMATEDSOS PREDICATES -----------

pred AmbulanceRequestSent {
	all h: HealthStatus | one a: AmbulanceRequest |
			((h.parameter.value < h.parameter.threshold)) implies 
 					((a.time = h.time) and (h in a.report.user.retrievedData.healthStatusAcquisition))
}


------------- TRACK4RUN PREDICATES -------------

pred MapLocationsAreRunnersLocations {
	all t : Track4RunUser | all r: Run | some l: Location |  t in r.athletes implies  (l in r.map.athletesLocation and l in t.retrievedData.locationAcquisition)

}

-------------------------------------------------------- ASSERTIONS --------------------------------------------------------

------------- DATA4HELP ASSERTIONS -------------

assert UserPrivacy {
	IndividualAnswerRegardOnlyPolicyAgreedUsers and MinimumGroupMembers
}

----------- AUTOMATEDSOS ASSERTIONS -----------

assert AmbulanceEmergency { 
	AmbulanceRequestSent
}

------------- TRACK4RUN ASSERTIONS -------------

assert WatchingAthletesPosition { 
	MapLocationsAreRunnersLocations 
}

---------------------------------------------------------------------------------------------------------------------------

pred show {
	IndividualAnswerRegardOnlyPolicyAgreedUsers and MinimumGroupMembers and AmbulanceRequestSent
	and MapLocationsAreRunnersLocations
}

run show for 6  but exactly 1 Run,  2 Track4RunSpectator, 1 IndividualInformationAnswer, 1 AmbulanceRequest

check WatchingAthletesPosition for 20
check AmbulanceEmergency for 10
check UserPrivacy for 20


