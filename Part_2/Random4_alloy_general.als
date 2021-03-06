/*
 * Signatures
 *
 * Your model should contain the following (and potentially other) signatures.
 * If necessary, you have to make some of the signatures abstract and
 * make them extend other signatures.
 */


abstract sig Athlete {	
	citizenOf: some Country
}

sig FemaleAthlete, MaleAthlete extends Athlete {}

sig Country {}

sig Discipline {
	event: some Event
}

sig Event {
	phase: some Phase,
	teams: set Team,
	medals: some Medal
}

sig Score{}

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
}

sig Phase {
	performance: some Performance,
	nextPhase: lone Phase,


}

sig Team {
	members: some Athlete,
	country: one Country,

}


sig Time {
	after: lone Time
}


/*
* facts
*/

// event only exists as a part of a discipline
fact event_only_with_discipline {
	all e: Event | one d:Discipline | e in d.event
}

//phase only exists as a part of an event
fact phase_only_with_event {
	all p: Phase | one e: Event | p in e.phase
}


// next phase must be in the same event
fact next_phase_in_same_event {
	all e: Event, p, p': Phase | (p in e.phase and p' in p.^nextPhase) => p' in e.phase 
}


// a team consists of either male or female athletes.
fact no_unisex_teams{
	all t:Team |all m,m':t.members | m in FemaleAthlete iff m' in FemaleAthlete
}

//medals belong to a specific event
fact medal_event_relation {
	all disj e,e':Event, m:Medal | m in e.medals implies ( m not in e'.medals )
}

// A score only exists if its performance exists
fact score_only_exists_with_its_performance {
	all s: Score | one p: Performance | s in p.score
}


// A performance only exists as part of a phase
fact performace_part_of_a_phase {
	all pe: Performance | one pa: Phase | pe in pa.performance
}

// Each location must have some performances
fact location_has_some_performances {
	all l: Location | some p: Performance | l = p.location
}


// Medals are correctly distributed
fact medal_distribution {
	all e:Event | #(GoldMedal & e.medals) >0
	all e:Event | (#(GoldMedal & e.medals) = 1 implies ((#(SilverMedal & e.medals) = 1) and #(BronzeMedal & e.medals) >= 1) or (#(SilverMedal & e.medals) >= 2 and #(BronzeMedal & e.medals) = 0))
	all e:Event | (#(GoldMedal & e.medals) = 2 implies #(SilverMedal & e.medals)  = 0 and #(BronzeMedal & e.medals) >= 1) 
	all e:Event | (#(GoldMedal & e.medals) >= 3 implies #(SilverMedal & e.medals)  = 0 and #(BronzeMedal & e.medals) = 0) 
}


//times are ordered
fact rules_of_time { 
	all disj t,t':Time | t in t'.^after implies (t' not in t.^after)
	all t:Time | t != t.after
	no disj t,t':Time | t.after = t'.after
}

fact ordering_of_phases {
	all disj p,p':Phase | p in p'.nextPhase implies (p' not in p.nextPhase)
	all p:Phase | p != p.nextPhase
}

// Phase are ordered by time
fact phase_time_ordering {
	all disj ph1,ph2:Phase|all pe1:ph1.performance,pe2:ph2.performance | ph2 in ph1.nextPhase implies pe2.startTime in pe1.endTime.^after
}


// There must be at least 3 medals & 3 teams per event
fact three_medals_and_teams_per_event {
	all e: Event | #e.medals >= 3 and #e.teams >= 3
}


// startTime is strictly before endTime
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


//athletes start in exactly one team
fact no_start_without_team {
	all a:Athlete | some t:Team | a in t.members
	all a:Athlete, disj t,t':Team | a in t.members implies a not in t'.members
}


//athletes can only be at one performance at a time
fact athletes_at_only_one_place_a_time {
	all a:Athlete,disj p,p':Performance | (a in p.teams.members and a in p'.teams.members ) implies 
							(p.endTime in p'.startTime.^after or  p'.endTime in p.startTime.^after)							
}
fact no_medal_without_performance {
	all m:Medal,e:Event,p:e.phase.performance,t:Team | (t in m.winner and m in e.medals) implies t in p.teams
}

fact teams_only_win_one_medal_per_event {
	all e:Event, t:Team,disj m,m':e.medals | t in m.winner implies t not in m'.winner 
}

fact no_team_without_performance {
	all t:Team | some p:Performance | t in p.teams
}

fact no_medals_without_event {
	all m:Medal | one e:Event | m in e.medals
}

fact male_teams_and_female_teams_different_events {
	all e:Event, disj m,m': e.teams.members | m in FemaleAthlete iff m' in FemaleAthlete 
	all p:Performance, disj m,m':p.teams.members | m in FemaleAthlete iff m' in FemaleAthlete		
								
}

fact no_medal_without_participation {
	no t:Team,e:Event, m:e.medals | t in m.winner and not t in e.teams
}

fact teams_not_in_performance_if_not_in_event {
	no t:Team,e:Event,p:Performance | t not in e.teams and t in p.teams and p in e.phase.performance
}



/*
 * Predicates
 */


// True iff t1 is strictly before t2.
pred isBefore[t1, t2: Time] {
	t2 in t1.^after	
}


// True iff p1 is strictly before p2.
pred phaseIsBefore[p1, p2: Phase] {

	p2 in p1.^nextPhase
}

// True iff m is a gold medal.
pred isGoldMedal[m : Medal] {
	m in GoldMedal and #m >= 1
}

// True iff m is a silver medal.
pred isSilverMedal[m : Medal] {
	m in SilverMedal and #m >= 1
}

// True iff m is a bronze medal.
pred isBronzeMedal[m: Medal] {
	m in BronzeMedal and #m >= 1
}

// True iff t is among the best teams in phase p. -> team(s) with the highest score 
// Only for sport specific part
pred isAmongBest[t: Team, p: Phase] {

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
fun getWinner[m: Medal] : Team {m.winner

}


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
										and p.startTime.after = p'.endTime
}

pred static_instance_3 {
	some c:Country | no a:Athlete | c in a.citizenOf
}

pred static_instance_4 {

	some a:Athlete, d:Discipline, disj e,e' :d.event, m:e.medals,m':e'.medals | m in GoldMedal and m' in GoldMedal and  a in m.winner.members and a in m'.winner.members	

}
pred show{

}

run static_instance_4 for 6 but 3 Country, 2 Performance, 1 Discipline, 2 Event, 4 Team

