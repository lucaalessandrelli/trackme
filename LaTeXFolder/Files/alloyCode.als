open util/integer
open util/boolean

sig Location
{
	coordX: one Int, --Latitude position
	coordY: one Int --Longitude position
}

sig HealthStatus
{
	hearthRate: one Int, --Number of hearth beat per minute
	bloodPressure: one Int, --Blood pressure
	caloriesConsumation: one Int, --Colories consumed per minute
	pedometer: one Int --Step counted per minute
}

sig AcquisitionSetData
{
	userAcq: one User,
	locationAcquisition: set Location,
	healthStatusAcquisition: set HealthStatus
}

sig PrivacyPolicy
{
	standard: one Bool, --Standard privacy policy is accepted (group tracking)
	full: one Bool --Full privacy policy is accepted (individual tracking)
}

sig UserAtttributes
{	
	age: one Int, --Age of the user
	address: one Location, --Location where user lives
	job: one Int , --User's id job (i.e. 1=student, 2=worker, 3=enterpreneur,..)
	--The other credentials are useless here
}

sig GroupAttributes
{	
	age: one Int, --Age of users
	area: set Location, --Area where users live
	job: one Int , --User's id job (i.e. 1=student, 2=worker, 3=enterpreneur,..)
}

sig User
{
	fiscalCode: one String, --Fiscal code
	policy: one PrivacyPolicy, --Status of policy acceptnace
	credentials: one GroupAttributes, --User's credentials
	retrievedData: set AcquisitionSetData --User's set of acquisition acquired
}

sig ThirdParty
{
	idCode: one Int --Identification code of companies inside the system
	--The other credentials are useless here
}

sig AcquisitionMode
{
	type: one Bool, --0 group mode, 1 single mode
	groupAttributes: lone GroupAttributes, --Users' attributes on group search (lone beacuse individual mode don't have it)
	usercCode: lone String --Tracked User's fiscal code  (lone beacuse group mode don't have it)
}

sig InformationRequest
{
	partyApplicant: one ThirdParty, --Third party applicant
	acquistionMode: one AcquisitionMode, --Group mode or individual mode
}

sig InformationAnswer 
{
	request: one InformationRequest,
	acquisitionData: set AcquisitionSetData
}

--All user has accepted policy
fact UserAcceptFirstPolicyPart
{
	all u: User | u.policy.standard = True
}

--User and retrieved data are linked
fact UserAreLinkedToRetrievedData
{
	all u: User | all d: AcquisitionSetData |  (d in u.retrievedData implies d.userAcq = u) and (d.userAcq = u implies d in u.retrievedData) 
}


--Group mode acquisition answer respect attributes requested
fact GroupModeAttributesRespected 
{
	all a: InformationAnswer |  a.request.acquistionMode.type = False implies 
		a.acquisitionData.userAcq.credentials.age = a.request.acquistionMode.groupAttributes.age and
		a.acquisitionData.userAcq.credentials.job = a.request.acquistionMode.groupAttributes.job
}

--Group mode acquisition answer respect location requested
fact GroupModeDataLocationRespected
{
	all a: InformationAnswer | a.request.acquistionMode.type = False implies 
		all d: a.acquisitionData.locationAcquisition | d in a.request.acquistionMode.groupAttributes.area
}

--Group answer only if involve users are >= 1000
fact GroupModePrivacy
{
	all a: InformationAnswer |  a.request.acquistionMode.type = False implies 
		#a.acquisitionData >= 1000
}

--Single answer only if user accept policy
fact IndividualModePrivacy
{
	all a: InformationAnswer | a.request.acquistionMode.type = True implies 
		  a.acquisitionData.userAcq.policy.full = True
}

--Check for User's privacy validation
assert NoGroupAnswerWithFewUsers
{
	no a: InformationAnswer |  a.request.acquistionMode.type = False and #a.acquisitionData < 1000
}

assert NoSingleAnswerWithUserNotAgree
{
	no a: InformationAnswer |  a.request.acquistionMode.type = True and  a.acquisitionData.userAcq.policy.full = False
}


check NoGroupAnswerWithFewUsers
check NoSingleAnswerWithUserNotAgree

pred show () {}

run show for 2

