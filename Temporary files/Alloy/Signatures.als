open util/integer
open util/boolean

sig Date
{
	day: one Int,
	month: one Int,
	year: one Int
}
{day >= 1 and day <= 31 and month>=1 and month<=12 and year>=2000}

sig Time
{
	hour: one Int,
	minute: one Int,
	second: one Int
}
{hour >= 1 and hour <= 24 and minute>=0 and minute<=59 second>=0 and secoond<=59}

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
	DateAcquisition: one Date,
	TimeAcquisition: one Time,
	LocationAcquisition: one Location,
	HealthStatusAcquisition: lone HealthStatus
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

sig User
{
	FiscalCode: one String, --Fiscal code
	Policy: one PrivacyPolicy, --Status of policy acceptnace
	Credentials: one UserAttributes, --User's credentials
	RetrievedData: set AcquisitionSetData --User's set of acquisition acquired
}

sig ThirdParty
{
	IdCode: one Int --Identification code of companies inside the system
	--The other credentials are useless here
}

sig AcquisitionType 
{
	Type: one Bool, --0 on-demand, 1 live
	StartTime: one Time, --Initial time monitor
	StartDate: one Date, -- Initial date monitor
	EndTime: lone Time -- End time monitor (lone beacuse live don't have end time)
	EndDate: lone Date -- End date monitor (lone beacuse live don't have end dates)
}

sig AcquisitionMode
{
	Type: one Bool, --0 group mode, 1 single mode
	GroupAttributes: lone UserAttributes, --Users' attributes on group search (lone beacuse individual mode don't have it)
	UsercCode: lone String --Tracked User's fiscal code  (lone beacuse group mode don't have it)
}

sig InformationRequest
{
	PartyApplicant: one ThirdParty, --Third party applicant
	AcquisitionType: one AcquisitionType, --Live or on-demand acquisition
	AcquiistionMode: one AcquisitionMode --Group mode or individual mode
}


