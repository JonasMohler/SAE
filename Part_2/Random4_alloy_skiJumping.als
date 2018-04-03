/*
 * Signatures
 *
 * Your model should contain the following (and potentially other) signatures.
 * If necessary, you have to make some of the signatures abstract and
 * make them extend other signatures.
 */

/*
 * General questions:
 * 1) difference between static & dynamic, ie when to use fact & pred -> use fact for things that are always true &
 *    pred as bool to check temp or specific properties
 * 2) are there field restrictions? not realy
 * 3) what is best? -> it is the team(s) with the highest score of a phase (mostly only one!)
 * -> Email with how to use ordering incomming, wait!
 */
 
//introduces ordering
//TODO: define stepping
open util/ordering[Time]
 
abstract sig Athlete {	
	citizenOf: some Country
}
sig FemaleAthlete, MaleAthlete extends Athlete {}

sig Country {
	athletes: some Athlete
}

sig Discipline {
	event: some Event
}

abstract sig Event {
	phase: some Phase,
	teams: set Team,
	medals: set Medal,
}{
	#teams >= 3
	#medals >=3
}

sig Score{
	map: Team -> overallPoints
}

sig Location {}

abstract sig Medal {
	winner: one Team 
}

sig BronzeMedal, SilverMedal, GoldMedal extends Medal {}

sig Performance {
	location: one Location,
	startTime: one Time,
	endTime: one Time,
	score: one Score,
	teams: some Team
} {
	isBefore[startTime, endTime]
}

sig Phase {
	performance: set Performance,
	nextPhase: lone Phase,
	first: one Phase
}

sig Team {
	members: some Athlete,
	country: Country,
	medals: set Medal,
	performances: some Performance
}

// TODO: should there be an relation between time and phase (for ordering)?
sig Time {
	after: lone Time
	first: one Time
}


/*
* facts
*/

// True iff medals are correctly distributed
fact medal_distribution {
	all e: Event | #(GoldMedal & e.medals) = 1 implies ((#(SilverMedal & e.medals) = 1 and #(BronzeMedal & e.medals) >= 1) or (#(SilverMedal & e.medals) >= 2 and #(BronzeMedal & e.medals) = 0))
	all e:Event | #(GoldMedal & e.medals) = 2 implies (#(SilverMedal & e.medals)  = 0 and #(BronzeMedal & e.medals) >= 1)
	all e:Event | #(GoldMedal & e.medals) >= 3 implies (#(SilverMedal & e.medals) = 0 and #(BronzeMedal & e.medals) = 0)
}

//Changed #t to #t.members
// In the Team Event Teams are of size 4
fact teamEventHas4ManTeams {
	all e:Event, t:Team | e in MensTeamEvent implies #t.members = 4
}

//Changed #t to #t.members
// In the Individual Event Teams consist of one athlete
fact OnePersonTeamInIndividualEvent {
	all e:Event, t:Team | e in MensIndividualEvent implies #t.members = 1
}

//Only Men in Men Event
fact OnlyMenInMenEvent {
	all e:Event, t:Team | (e in MensTeamEvent or e in MensIndividualEvent) implies t.members in MaleAthlete
}

// True iff score only exists if its performance exists
fact score_only_exists_with_its_performance {
	all s: Score | one p: Performance | s = p.score
}

// True iff a performance only exists as part of a phase
fact performace_part_of_a_phase {
	all pe: Performance | some pa: Phase | pe in pa.performance
}

// True iff a location has some performances
fact location_has_some_performances {
	all l: Location | some p: Performance | l = p.location
}


/*
 * Predicates
 */
 
// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {
	t2 in t1.*after and not t1 in t2.*after
}

// True iff p1 is strictly before p2.
pred phaseIsBefore[p1, p2: Phase] {
	//lt[p1, p2]
	p2 in p1.*nextPhase and not p1 in p2.*nextPhase
}

// True iff m is a gold medal.
pred isGoldMedal[m : Medal] {
	m in GoldMedal
}

// True iff m is a silver medal.
pred isSilverMedal[m : Medal] {
	m in SilverMedal
}

// True iff m is a bronze medal.
pred isBronzeMedal[m: Medal] {
	m in BronzeMedal
}

// True iff t is among the best teams in phase p.
//TODO
pred isAmongBest[t: Team, p: Phase] {
	//t in getBest[p]
	//proposal without extra function
	no t':Team - t | t in p.performance.teams
				and t' in p.performance.teams 
				and (add[p.performance.score.map[t'].distance,p.performance.score.map[t'].pointsFromJudges] > add[p.performance.score.map[t].distance,p.performance.score.map[t].pointsFromJudges])
	
}

/*
 * Functions
 */

// Returns all the events offered by the discipline d.
fun getEvents[d: Discipline] : set Event { d.event } 

// Returns all the teams which participate in the event e.
fun getEventParticipants[e: Event] : set Team { e.teams}

// Returns all the phases of the event e.
fun getPhases[e: Event] : set Phase { e.phase }

// Returns all the performances which take place within the phase p.
fun getPerformances[p: Phase] : set Performance { p.performance }

// Returns the set of medals handed out for the event e.
fun getMedals[e: Event] : set Medal { e.medals}

// Returns the start time of the performance p.
fun getStart[p : Performance] : Time { p.startTime }

// Returns the end time of the performance p.
fun getEnd[p: Performance] : Time { p.endTime}

// Returns the location of the performance p.
fun getLocation[p: Performance] : Location { p.location } 

// Returns all the teams which participate in the performance p.
fun getParticipants[p: Performance] : set Team { p.teams }

// Returns all the athletes which belong to the team t.
fun getMembers[t: Team] : set Athlete { t.members}

// Returns the team which won the medal m.
fun getWinner[m: Medal] : Team {m.winner}


/////////////////////////////////////////////////////////
//Sport Specific

sig SkiJumping extends Discipline {}

sig MensIndividualEvent extends Event {} 
sig MensTeamEvent extends Event{} 

sig overallPoints{
	distance: Int,
	pointsFromJudges: Int	
}

sig qualifyingPhase extends Phase {}{ #performance.teams = 50}
sig finalFirstPhase extends Phase {}{ #performance.teams = 50}
sig finalSecondPhase extends Phase {}{ #performance.teams = 30}

////////////////////////////////////////////////////////
//Instances
pred static_instance_1 {
	#Performance = 7
	#Location = 2
	#Time = 4
}

pred static_instance_2 {
	some a:Athlete | some disj p,p':Performance | a in p.teams.members 
										and a in p'.teams.members
										and p.endTime.next = p'.startTime
}

pred static_instance_3 {
	some c:Country | all e:Event | c not in e.teams.country 
}

pred static_instance_4 {
	//TODO
	//probably should not be possible
	
}

pred static_instance_5 {
	//TODO
	//probably should not be possible
	
}

pred static_instance_6 {
	// really not sure about this one, i think gm/bm are probably just single medals from a set and not sets themselves , but somehow it compiles...
	some d:SkiJumping | some e:d.event | some gm,bm:e.medals | gm in GoldMedal and #gm = 1
													and bm in BronzeMedal and #bm >= 1 
}

run static_instance_3



