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
	all e:Event | (#(GoldMedal & e.medals) = 1 and ((#(SilverMedal & e.medals) = 1) and #(BronzeMedal & e.medals) >= 1) or (#(SilverMedal & e.medals) >= 2 and #(BronzeMedal & e.medals) = 0))
			or (#(GoldMedal & e.medals) = 2 and #(SilverMedal & e.medals)  = 0 and #(BronzeMedal & e.medals) >= 1) 
			or (#(GoldMedal & e.medals) >= 3 and #(SilverMedal & e.medals)  = 0 and #(BronzeMedal & e.medals) = 0) 
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
	all a:Athlete, disj p,p':Performance | ((a in p.teams.members) and (a in p'.teams.members)) implies
								((p.endTime in p'.startTime.^after) or ( p'.endTime in p.startTime.^after))
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
						
								
}

fact no_medal_without_participation {
	no t:Team,e:Event, m:e.medals | t in m.winner and not t in e.teams
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


/////////////////////////////////////////////////////////
//Sport Specific

sig SkiJumping extends Discipline {}//{event in (MensIndividualEvent + MensTeamEvent)}

sig MensIndividualEvent extends Event {}{phase in (qualifyingPhase + finalPhase)}
sig MensTeamEvent extends Event{} {phase in (qualifyingPhase + finalPhase)}

sig Points{
	total = distance.add[pointsFromJudges],
	distance: Int,
	pointsFromJudges: Int	
}{
	distance >= 0 and
	pointsFromJudges >=0
}

sig OverallPoints extends Score{
	ranking: Team one -> one Points
}


sig qualifyingPhase extends Phase {}
sig finalPhase extends Phase {}

sig qualifyingRound extends Performance {}{ #teams = 50}
sig finalFirstRound extends Performance {}{ #teams = 50}
sig finalSecondRound extends Performance {} { #teams = 30}


/*
facts
*/


// SkiJumping Events has exactly 2 phase
fact has_two_phases{
	all e: SkiJumping.event |  #e.phase = 2
}

// MensIndividuall has only one athlete per team
fact only_one_member_in_individual{
	all t: MensIndividualEvent.teams | #t.members = 1
}

// MensTeam has 4 athlete per team
fact four_member_in_team{
	all t: MensTeamEvent.teams | #t.members = 4
}

// if a skiJumping performance it has an overall score and the list is as long as many teams there are
fact skiPerformance_has_overallPoints{
	all p: qualifyingRound | p.score in OverallPoints and #p.score.ranking = 50
	all p: finalFirstRound | p.score in OverallPoints and #p.score.ranking = 50
	all p: finalSecondRound | p.score in OverallPoints and #p.score.ranking = 30
}

// qualyPhase has eactly one performance
fact qualy_only_one_performance{
	all pa: qualifyingPhase | #pa.performance = 1
}

// finalPhase has eactly two performance
fact final_has_two_performances{
	all pa: finalPhase | #pa.performance = 2
}

// qualyRound is only in qualyPhase
fact qualyRound_only_in_qualyPhase {
	all pe: Performance, pa: qualifyingPhase | pe in pa.performance => pe in qualifyingRound
}

// finalRounds are only in finalPhase
fact finalRounds_only_in_finalPhase {
	all pe: Performance, pa: finalPhase | pe in pa.performance => pe in finalFirstRound or pe in finalSecondRound
}

// qualyPhase is strictly before finalPhase
fact qualyPhase_before_finalPhase {
	all p, p': Phase | p in qualifyingPhase and p' in finalPhase => phaseIsBefore[p, p']
}

////////////////////////////////////////////////////////
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
	some c:Country | all e:Event | c not in e.teams.country 
}

pred static_instance_4 {
/*	some a: Athlete, d: Discipline | some disj t, t': Team | a in t.members and a in t'.members and
										t in d.event.teams and t' in d.event.teams and
										isGoldMedal[t.medals] and isGoldMedal[t'.medals]
*/
	some a:Athlete, d:Discipline, disj e,e' :d.event, m:e.medals,m':e'.medals | m in GoldMedal and m' in GoldMedal and  a in m.winner.members and a in m'.winner.members	

}

pred static_instance_5 {
	some d: SkiJumping | some e: d.event | some t: e.teams, p: e.phase| (GoldMedal in e.medals and GoldMedal.winner = t) and not isAmongBest[t, p]
	
}

pred static_instance_6 {
	// really not sure about this one, i think gm/bm are probably just single medals from a set and not sets themselves , but somehow it compiles...
	some d:SkiJumping | some e:d.event | some gm,bm:e.medals | gm in GoldMedal and #gm = 1
													and bm in BronzeMedal and #bm >= 1 
}

run static_instance_5 for 10 but exactly 1 SkiJumping
