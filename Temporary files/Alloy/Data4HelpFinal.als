open util/integer


sig Bool {}
one sig True extends Bool {}
one sig False extends Bool {}

sig FiscalCode {}
 
sig Location{}

sig HealthStatus{}

sig AcquisitionSetData
{
	locationAcquisition: some Location,
	healthStatusAcquisition: some HealthStatus
}

sig IndividualPrivacyPolicy
{
	IndividualMonitoring: one Bool --Full privacy policy is accepted (individual monitoring)
}

sig UserAttributes
{	
	address: one Location, --Location where user lives
}

sig GroupAttributes
{	
	area: some Location, --Area where users live
}

sig User
{
	fiscalCode : one FiscalCode,
	policy: one IndividualPrivacyPolicy, --Status of policy acceptance
	credentials: one UserAttributes, --User's credentials
	retrievedData: some AcquisitionSetData --User's set of acquisition acquired
}


sig ThirdParty{}

abstract sig InformationRequest
{
	partyApplicant: one ThirdParty, --Third party applicant}			
}

sig IndividualRequest extends InformationRequest
{
	fiscalCode: one FiscalCode --Tracked User's fiscal code  (lone beacuse group mode don't have it)
}

sig GroupRequest extends InformationRequest
{
	groupAttributes: one GroupAttributes, --Users' attributes on group search (lone beacuse individual mode don't have it)
}

abstract sig InformationAnswer{}

sig IndividualInformationAnswer extends InformationAnswer
{
	individualRequest: one IndividualRequest,
	user: one User,
	acquisitionData: one AcquisitionSetData
} {user.policy.IndividualMonitoring = True}

sig GroupInformationAnswer extends InformationAnswer {
	groupRequest: one GroupRequest,
	acquisitionData: some AcquisitionSetData
} {#acquisitionData > 3}									----  3 stands for 1000 

----------------------------------------------------

-------- FATCTS ----------

fact HealthStatusInAcquisitionSetData
{
	all h: HealthStatus | some a: AcquisitionSetData | h in a.healthStatusAcquisition
}
fact PrivacyPolicyInUser
{
	all p: IndividualPrivacyPolicy | one u: User | p in u.policy
}
fact UserAttInUser
{
	all ua: UserAttributes | one u: User | ua in u.credentials
}
fact GroupAttributesInGroupRequest
{
	all g: GroupAttributes | one ga: GroupRequest | g in ga.groupAttributes
}
fact ThirdPartyInRequest
{
	all t: ThirdParty | some r:InformationRequest | t in r.partyApplicant
}
fact AcquisitionDataInUser
{
	all a: AcquisitionSetData | one u: User | a in u.retrievedData
}
fact NoTwoAnswerForSameIndividualRequest
{
 all disj i1, i2: IndividualInformationAnswer | i1.individualRequest != i2.individualRequest 
}
fact NoTwoAnswerForSameGroupRequest
{
 all disj i1, i2: GroupInformationAnswer | i1.groupRequest != i2.groupRequest 
}
fact NoTwoEqualFisalCode
{
	all disj u1,u2 : User | u1.fiscalCode != u2.fiscalCode
}
fact AnswerToRequestWithRightFiscalCode
{
	all i: IndividualInformationAnswer | i.user.fiscalCode = i.individualRequest.fiscalCode
}
fact RightAcquisitionDataAnswerToRequest
{
	all i: IndividualInformationAnswer | one u: User | (i.user = u) and (u.retrievedData = i.acquisitionData)
}


-------- PREDS ----------

pred IndividualAnswerRegardOnlyPolicyAgreedUsers
{
	all i: IndividualInformationAnswer | i.user.policy.IndividualMonitoring = True
}

pred MinimumGroupMembers
{
	all g: GroupInformationAnswer | #g.acquisitionData > 3				----  3 stands for 1000 
}
-------- ASSERT -------------

assert UserPrivacy
{
	IndividualAnswerRegardOnlyPolicyAgreedUsers and MinimumGroupMembers
}

pred show{}
check UserPrivacy for 20
run show for 2 but exactly 2 GroupInformationAnswer

