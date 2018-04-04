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

sig Event {
	phase: some Phase,
	teams: set Team,
	medals: set Medal,
}

sig Score{}

sig Location {}

abstract sig Medal {
	winner: one Team 
}

sig BronzeMedal, SilverMedal, GoldMedal extends Medal {}

sig Performance {
	inPhase: one Phase,
	location: one Location,
	startTime: one Time,
	endTime: one Time,
	score: one Score,
	teams: some Team
}

sig Phase {
	performance: set Performance,
	nextPhase: lone Phase,

}

sig Team {
	members: some Athlete,
	country: Country,
	medals: set Medal,
	performances: some Performance
}


sig Time {
	after: lone Time
}


/*
* facts
*/


//i think this should already be covered by phase/time properties
fact startTime_not_endTime{
	all p:Performance | p.startTime != p.endTime
}

// a team consists of either male or female athletes.
fact no_unisex_events{
	all e:Event | all disj m,m':e.teams.members | (m in FemaleAthlete implies m' in FemaleAthlete)
									and (m in MaleAthlete implies m' in MaleAthlete)
}

//events exclusive to disciplines
fact events_in_one_discipline {
	all disj d,d':Discipline | d.event != d'.event
}

//medals belong to a specific event
fact medal_event_relation {
	all disj e,e':Event, m:Medal | m in e.medals implies not m in e'.medals
}


//A team winning a medal is the winner of that medal
fact teams_win_medals_won_by_team {
	all m:Medal, t:Team | m in t.medals iff t in m.winner
}

//A performance is in a phase if and only if a phase has that performance
fact performance_phase_relation {
	all pe:Performance, pa:Phase | pe in pa.performance iff pa in pe.inPhase
}


// True iff score only exists if its performance exists
fact score_only_exists_with_its_performance {
	all s: Score | one p: Performance | s = p.score
}

fact performance_is_only_in_one_phase {
	all disj p,p':Phase | p.performance != p'.performance
}


// True iff a performance only exists as part of a phase
fact performace_part_of_a_phase {
	all pe: Performance | some pa: Phase | pe in pa.performance
}

// True iff a location has some performances
fact location_has_some_performances {
	all l: Location | some p: Performance | l = p.location
}

// True iff medals are correctly distributed
fact medal_distribution {
	all e:Event | #(GoldMedal & e.medals) >= 1
	all e: Event | #(GoldMedal & e.medals) = 1 implies ((#(SilverMedal & e.medals) = 1 and #(BronzeMedal & e.medals) >= 1) or (#(SilverMedal & e.medals) >= 2 and #(BronzeMedal & e.medals) = 0))
	all e:Event | #(GoldMedal & e.medals) = 2 implies (#(SilverMedal & e.medals)  = 0 and #(BronzeMedal & e.medals) >= 1)
	all e:Event | #(GoldMedal & e.medals) >= 3 implies (#(SilverMedal & e.medals) = 0 and #(BronzeMedal & e.medals) = 0)
}


fact rules_of_time {

	//times are ordered 
	all disj t,t':Time | t in t'.^after implies (t' not in t.^after)
	all t:Time | t != t.after
	no disj t,t':Time | t.after = t'.after
}

fact ordering_of_phases {
	all disj p,p':Phase | p in p'.nextPhase implies (p' not in p.nextPhase)
	all p:Phase | p != p.nextPhase
}

fact phase_time_ordering {
	all disj ph1,ph2:Phase|all pe1:ph1.performance,pe2:ph2.performance | ph2 in ph1.nextPhase implies pe2.startTime in pe1.endTime.^after
}


// True iff at least 3 medals & 3 teams per event
fact three_medals_and_teams_per_event {
	all e: Event | #e.medals >= 3 and #e.teams >= 3
}


// True iff startTime is strictly before endTime
fact start_before_end {

	all p: Performance | p.startTime in p.endTime.^after
}

//Only one performance at a location at the same time
fact one_performance_per_time_per_place {
	all disj p,p':Performance | p.location = p'.location implies (p.endTime in p'.startTime.^after or p'.endTime in p.startTime.^after)

}

//if a team starts for a country, all the athletes of that team must be citizens of that country
fact athletes_in_same_country_as_team{
	all t:Team | all a:t.members | t.country in a.citizenOf  
}

//being an athlete of a country means being a citizen of that country
fact starting_for_country_reqs_citizenship {
	all c:Country,a:Athlete | a in c.athletes implies c in a.citizenOf
}

//athletes start in exactly one team
fact no_start_without_team {
	all a:Athlete | some t:Team | a in t.members
	all a:Athlete, disj t,t':Team | a in t.members implies a not in t'.members
}
//athletes represent only the country of the team they're in
fact team_country_athletes {
	all a:Athlete,t:Team,c:Country | a in c.athletes iff (a in t.members and t.country = c)
}



/*
 * Predicates
 */


// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {
	t2 in t1.^after and not t1 in t2.^after	
}

// True iff p1 is strictly before p2.
pred phaseIsBefore[p1, p2: Phase] {

	p2 in p1.^nextPhase and not p1 in p2.^nextPhase
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
	/*no t':Team - t | t in p.performance.teams
				and t' in p.performance.teams 
				and (add[p.performance.score.map[t'].distance,p.performance.score.map[t'].pointsFromJudges] > add[p.performance.score.map[t].distance,p.performance.score.map[t].pointsFromJudges])
	*/
}

///// Our Predicates /////


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

// Returns all the teams which paricipate in the performance p.
fun getParticipants[p: Performance] : set Team { p.teams }

// Returns all the athletes which belong to the team t.
fun getMembers[t: Team] : set Athlete { t.members}

// Returns the team which won the medal m.
fun getWinner[m: Medal] : Team {m.winner}


//Instances
pred static_instance_1 {
	//impossible, as no more than one performance can be at a single location at any point in time
	#Performance = 7
	#Location = 2
	#Time = 4
}

pred static_instance_2 {
	some a:Athlete | some disj p,p':Performance | a in p.teams.members 
										and a in p'.teams.members
										and p.endTime.after = p'.startTime
}

pred static_instance_3 {
	some c:Country | all e:Event | c not in e.teams.country 
}

pred static_instance_4 {
	//TODO
	//probably should not be possible
	
}

run static_instance_2



