open util/integer
open util/boolean

--sig Date
--{
	--day: one Int,
	--month: one Int,
	--year: one Int
--}
--{day >= 1 and day <= 31 and month>=1 and month<=12 and year>=2000}

--sig Time
--{
	--hour: one Int,
	--minute: one Int,
	--second: one Int
--}
--{hour >= 1 and hour <= 24 and minute>=0 and minute<=59 second>=0 and secoond<=59}

sig Location
{
	coordX: one Int, --Latitude position
	coordY: one Int --Longitude position
}

sig HealthStatus
{
	HearthRate: one Int, --Number of hearth beat per minute
	BloodPressure: one Int, --Blood pressure
	CaloriesConsumation: one Int, --Colories consumed per minute
	Pedometer: one Int --Step counted per minute
}

sig AcquisitionSetData
{
	User: one User,
	LocationAcquisition: set Location,
	HealthStatusAcquisition: set HealthStatus
}

sig PrivacyPolicy
{
	Standard: one Bool, --Standard privacy policy is accepted (group tracking)
	Full: one Bool --Full privacy policy is accepted (individual tracking)
}

sig UserAtttributes
{	
	Age: one Int, --Age of the user
	Address: one Location, --Location where user lives
	Job: one Int , --User's id job (i.e. 1=student, 2=worker, 3=enterpreneur,..)
	--The other credentials are useless here
}

sig GroupAtttributes
{	
	Age: one Int, --Age of users
	Area: set Location, --Area where users live
	Job: one Int , --User's id job (i.e. 1=student, 2=worker, 3=enterpreneur,..)
}

sig User
{
	FiscalCode: one String, --Fiscal code
	Policy: one PrivacyPolicy, --Status of policy acceptnace
	Credentials: one GroupAttributes, --User's credentials
	RetrievedData: set AcquisitionSetData --User's set of acquisition acquired
}

sig ThirdParty
{
	IdCode: one Int --Identification code of companies inside the system
	--The other credentials are useless here
}

sig AcquisitionMode
{
	Type: one Bool, --0 group mode, 1 single mode
	GroupAttributes: lone GroupAttributes, --Users' attributes on group search (lone beacuse individual mode don't have it)
	UsercCode: lone String --Tracked User's fiscal code  (lone beacuse group mode don't have it)
}

sig InformationRequest
{
	PartyApplicant: one ThirdParty, --Third party applicant
	AcquiistionMode: one AcquisitionMode, --Group mode or individual mode
}

sig InformationAnswer 
{
	Request: one InformationRequest,
	AcquisitionData: set AcquisitionSetData
}

--All user has accepted policy
fact UserAccqptFirstPolicyPart
{
	all u: User | u.PrivacyPolicy.Standard = 1
}

--User and retrieved data are linked
fact UserAreLinkedToRetrievedData
{
	all u: User | all d: RetrievedData |  (d in u.RetrievedData implies d.User = u) and (d.User = u implies d in u.RetrievedData) 
}


--Group mode acquisition answer respect attributes requested
fact GroupModeAttributesRespected 
{
	all a: InformationAnswer |  a.Request.AcquisitionMode.Type = 0 implies 
		a.AcquisitionData.User.UserAttributes.Age = a.Request.AcquisitionMode.GroupAttributes.Age and
		a.AcquisitionData.User.UserAttributes.Job = a.Request.AcquisitionMode.GroupAttributes.Job and
		a.AcquisitionData.User.UserAttributes.Address in a.Request.AcquisitionMode.GroupAttributes.Area
}

--Group mode acquisition answer respect location requested
fact GroupModeDataLocationRespected
{
	all a: InformationAnswer |  a.Request.AcquisitionMode.Type = 0 implies 
		all d: a.AcquisitonData.LocationAcquisition | d in a.Request.AcquisitionMode.GroupAttributes.Area
}

--Group answer only if involve users are >= 1000
fact GroupModePrivacy
{
	all a: InformationAnswer |  a.Request.AcquisitionMode.Type = 0 implies 
		sum x: a.AcquisitonData | x >= 1000
}

--Single answer only if user accept policy
fact IndividualModePrivacy
{
	all a: InformationAnswer |  a.Request.AcquisitionMode.Type = 1 implies 
		 a.AcquisitionData.User.PrivacyPolicy.Full = 1
}
