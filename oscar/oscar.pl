/*
 *      oscar.pl
 *
 *		Students edit this program to complete the assignment.
 */

:-consult(wp).

candidate_number(17655).

map_object(c(_), p(_, _)).
map_object(o(_), p(_, _)).

object_path(map_object(_, _), Path) :-
	is_list(Path).

objects_list(Oracles, Chargers) :-
	is_list(Oracles),
	is_list(Chargers).

path(Depth, Path) :-
	integer(Depth),
	is_list(Path).

solve_task(Task,Cost):-
	agent_current_position(oscar,P),
	%solve_task_bt(Task,[c(0,P),P],0,R,Cost,_NewPos),!,	% prune choice point for efficiency
	solve_task_top(Task,[[c(0,P), P]],R,Cost,_NewPos),
	reverse(R,[_Init|Path]),
	agent_do_moves(oscar,Path).

solve_task_top(go(Target),[[c(0,P), P]],R,Cost,NewPos) :-
    map_distance(P, Target, Dist),
    solve_task_astar(go(Target),[[Dist, c(0,P), P]],R,Cost,NewPos).

solve_task_top(Task,[[c(0,P), P]],R,Cost,NewPos) :-
    solve_task_bf(Task,[[c(0,P), P]],R,Cost,NewPos).

%% backtracking depth-first search, needs to be changed to agenda-based A*
solve_task_bt(Task,Current,Depth,RPath,[cost(Cost),depth(Depth)],NewPos) :-
	achieved(Task,Current,RPath,Cost,NewPos).
solve_task_bt(Task,Current,D,RR,Cost,NewPos) :-
	Current = [c(F,P)|RPath],
	search(P,P1,R,C),
	\+ memberchk(R,RPath), % check we have not been here already
	D1 is D+1,
	F1 is F+C,
	solve_task_bt(Task,[c(F1,P1),R|RPath],D1,RR,Cost,NewPos). % backtracking search

solve_task_astar(Task,Current,RPath,CostList,NewPos) :-
   % Because this is bf the first item in RPath will always be the shortest
   Current = [CurList | _],
   CurList = [ _ | Cur],
   Cur = [c(Depth, _) | _],
   CostList = [cost(Cost), depth(Depth)],
   achieved(Task,Cur,RPath,Cost,NewPos).
solve_task_astar(go(Target),Current,RR,Cost,NewPos) :-
   Current = [CurList | OtherRPaths],
   CurList = [_ | Cur],
   Cur = [c(_,P)|RPath],
   children(P, Children, RPath),
   calc_children_costs_astar(Target, Cur, Children, ChildrenCosts),
   append(OtherRPaths, ChildrenCosts, NewRPath),
   sort(NewRPath, SortedRPath),
   solve_task_astar(go(Target), SortedRPath, RR, Cost, NewPos).

% (Children, [c(C,P),P])
calc_children_costs_astar(Target, Cur, Children, ChildCosts) :-
   do_children_costs_astar(Target, Cur, Children, [], ChildCosts).

do_children_costs_astar(_, _, [], ChildCosts, ChildCosts).
do_children_costs_astar(Target, Cur, [Child|Children], PastCosts, ChildCosts) :-
   Cur = [c(OldDepth, _)|RPath],
   Depth is OldDepth+1,
   map_distance(Child, Target, Dist),
   do_children_costs_astar(Target, Cur, Children, [[Dist, c(Depth, Child) | [Child|RPath]] | PastCosts], ChildCosts).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds a list of objects that we haven't already found.
%% In the case of oracles they haven't already been visited.
%% @param FoundObjects [map_object]: A list of objects we already know about
%% @returns MapObjects [map_object]: The existing list of objects with the new
%list appended to it
%% @param CurPos p: Current agent position
%% @returns OraclePath [p]: The path to the nearest oracle
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_find_stuff(FoundObjects, MapObjects, CurPos, OraclePath) :-
	find_stuff(FoundObjects, MapObjects, [path(0, [CurPos])], OraclePath).

find_stuff(MapObjects, MapObjects, Paths, _) :-
	Paths = [NextPath | _],
	NextPath = path(Depth, _),
	Depth >= 10, % Limits the search depth to 10
	!.
find_stuff(FoundObjects, MapObjects, Paths, OraclePath) :-
	Paths = [CurPath | OtherPaths],
	CurPath = path(_, [CurPos | RestOfPath]),
	% Find the empty spaces around us (That aren't already in this path)
	children(CurPos, Children, RestOfPath),
	calc_children_costs(CurPath, Children, ChildrenCosts),
	append(OtherPaths, ChildrenCosts, NewPaths),
	% Find the oracles and stations around us that we don't already know about
	FoundObjects = objects_list(Oracles, Chargers),
	child_oracles(CurPos, NewOracles, Oracles),
	% Set the Oracle path if we found an oracle and the path hasn't been set
	% already
	(NewOracles = [_|_], var(OraclePath) -> OraclePath = CurPath
	; true),
	child_chargers(CurPos, NewChargers, Chargers),
	append(Oracles, NewOracles, FoundOracles),
	append(Chargers, NewChargers, FoundChargers),
	% Continue recursing
	find_stuff(objects_list(FoundOracles, FoundChargers), MapObjects, NewPaths, OraclePath).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all the unqueried oracles around us that we don't already know about
%% @param Pos p: The position to search around
%% @returns NewOracles [map_object]: The list of oracles we found
%% @param OldOracles [map_object]: The list of oracles we already know about
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
child_oracles(Pos, NewOracles, OldOracles) :-
	findall(map_object(o(OID), NewPos), map_adjacent(Pos, NewPos, o(OID)), AllOracles),
	% Filter out those that have been queried
	filter_oracles(AllOracles, [], NonVisitedOracles),
	% Filter out those that we already know about
	do_filter_objects(NonVisitedOracles, OldOracles, NewOracles).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all the unqueried chargers around us that we don't already know about
%% @param Pos p: The position to search around
%% @returns NewChargers [map_object]: The list of chargers we found
%% @param OldChargers [map_object]: The list of chargers we already know about
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
child_chargers(Pos, NewChargers, OldChargers) :-
	findall(map_object(c(CID), NewPos), map_adjacent(Pos, NewPos, c(CID)), AllChargers),
	% Filter out those that we already know about
	do_filter_objects(AllChargers, OldChargers, NewChargers).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filters the objects out of Unfiltered that already exist in ExistingObjs
%% @param Unfiltered []: The list of objects to filter
%% @param ExistingObjs []: The list of objects to filter out of Unfiltered
%% @returns Filtered []: The filtered list
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
do_filter_objects(Unfiltered, ExistingObjs, Filtered) :-
	filter_objects(Unfiltered, ExistingObjs, [], Filtered).

filter_objects([], _, Filtered, Filtered).
filter_objects([Next | OtherObjs], ExistingObjs, Filtered, Valids) :-
	( memberchk(Next, ExistingObjs) ->
		filter_objects(OtherObjs, ExistingObjs, Filtered, Valids)
	;  filter_objects(OtherObjs, ExistingObjs, [Next | Filtered], Valids)
	).

solve_task_bf(Task,Current,RPath,CostList,NewPos) :-
   % Because this is bf the first item in RPath will always be the shortest
   Current = [Cur | _],
   Cur = [c(Depth, _) | _],
   CostList = [cost(Cost), depth(Depth)],
   achieved(Task,Cur,RPath,Cost,NewPos).
solve_task_bf(Task,Current,RR,Cost,NewPos) :-
   Current = [Cur | OtherRPaths],
   Cur = [c(_,P)|RPath],
   children(P, Children, RPath),
   calc_children_costs(Cur, Children, ChildrenCosts),
   append(OtherRPaths, ChildrenCosts, NewRPath),
   solve_task_bf(Task, NewRPath, RR, Cost, NewPos).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all of the empty positions around Current that haven't already been
%visited.
%% @param Current p: The position to search around
%% @returns Children [p]: The empty positions around Current
%% @param RPath [p]: The already visited positions in this path
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
children(Current, Children, RPath) :-
   findall(NewPos, map_adjacent(Current, NewPos, empty), AllChildren),
   filter_children(AllChildren, RPath, Children).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Calculates the path to and the cost of a position around the current one
%% @param Cur path: The path to the current position
%% @param Children [p]: The positions surround the current one
%% @returns ChildCosts [path]: The paths to the Children positions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
calc_children_costs(Cur, Children, ChildCosts) :-
   do_children_costs(Cur, Children, [], ChildCosts).

do_children_costs(_, [], ChildCosts, ChildCosts).
do_children_costs(CurPath, [Child|Children], PastCosts, ChildCosts) :-
   CurPath = path(OldDepth, Path),
   Depth is OldDepth+1,
   do_children_costs(CurPath, Children, [path(Depth, [Child | Path]) | PastCosts], ChildCosts).

achieved(go(Exit),Current,RPath,Cost,NewPos) :-
	Current = [c(Cost,NewPos)|RPath],
	( Exit=none -> true
	; otherwise -> RPath = [Exit|_]
	).
achieved(find(O),Current,RPath,Cost,NewPos) :-
	Current = [c(Cost,NewPos)|RPath],
	( O=none    -> true
	; otherwise -> RPath = [Last|_],map_adjacent(Last,_,O)
	).

search(F,N,N,1):-
	map_adjacent(F,N,empty).

filter_children(Children, RPath, Valids) :-
   filter_loop(Children, RPath, [], Valids).

filter_loop([], _, Valids, Valids).
filter_loop([Child|Children], RPath, Filtered, Valids) :-
   (\+ memberchk(Child, RPath) ->
      filter_loop(Children, RPath, [Child|Filtered], Valids)
   ; filter_loop(Children, RPath, Filtered, Valids)
   ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% A data structure containing the actor name and it's links
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
actor_data(actor_name, Links) :-
   actor(actor_name),
   is_list(Links).

find_identity(A):-
   findall(A, actor(A), ActorNames),
   create_actor_data(ActorNames, Actors),
   keep_filtering_actors(Actors, Actor, objects_list([],[]), []),
   Actor = actor_data(A, _),
   !.

keep_filtering_actors([Actor], Actor, _, _).
keep_filtering_actors(Unfiltered, Actor, FoundObjects, []) :-
    agent_current_position(oscar, CurPos),
	do_find_stuff(FoundObjects, Objects, CurPos, ClosestOracle),
	ClosestOracle = path(_, PathFromOracle),
	reverse(PathFromOracle, [_ | PathToOracle]),
	agent_do_moves(oscar, PathToOracle),
	Objects = objects_list([map_object(Oracle, _)|RemainingOracles], _),
	% TODO: Find nearest unqueried oracle and go to it
	agent_ask_oracle(oscar, Oracle, link, Link),
	filter_actors(Unfiltered, Link, Filtered),
	Filtered = [Actor|_],
	keep_filtering_actors(Filtered, Actor, FoundObjects, RemainingOracles).

keep_filtering_actors(Unfiltered, Actor, FoundObjects, RemainingOracles) :-
    agent_current_position(oscar, CurPos),
    do_get_closest_oracle(CurPos, RemainingOracles, ClosestOracle),
    ClosestOracle = map_object(Oracle, Pos),
    solve_task_top(go(Pos),[[c(0,CurPos), CurPos]],R,Cost,_),
	write(R).

do_get_closest_oracle(CurPos, [Oracle|Oracles], Closest):-
    Oracle = map_object(_, Pos),
    map_distance(CurPos, Pos, D),
    get_closest_oracle(CurPos, Oracles, Oracle, Closest, D).

get_closest_oracle(_, [], Closest, Closest, _).
get_closest_oracle(CurPos, [Oracle|Oracles], OldOracle, Closest, OldDistance):-
    Oracle = map_object(_, Pos),
    map_distance(CurPos, Pos, D),
    (D =< OldDistance -> NewDistance = D, NewOracle = Oracle
    ; NewDistance = OldDistance, NewOracle = OldOracle),
    get_closest_oracle(CurPos, Oracles, NewOracle, Closest, NewDistance).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Finds all of the links for the given ActorNames and puts them into actor_data
%% @param ActorNames [string]: The list of actor names
%% @returns Actors [actor_data]: The list of actor data
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
create_actor_data(ActorNames, Actors) :-
   do_create_actor_data(ActorNames, [], Actors).

do_create_actor_data([], Actors, Actors).
do_create_actor_data([CurActor|ActorNames], Processed, Actors) :-
   wp(CurActor, WT),
   findall(L, wt_link(WT, L), Links),
   do_create_actor_data(ActorNames, [actor_data(CurActor, Links)|Processed], Actors).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filters the list of actor_data to only those which have the given link
%% @param Unfiltered [actor_data]: The list of actors to filter
%% @param Link: The link which filtered actors must all have
%% @returns Filtered: The filtered list of actors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
filter_actors(Unfiltered, Link, Filtered) :-
   do_filter_actors(Unfiltered, Link, [], Filtered).

do_filter_actors([], _, Filtered, Filtered).
do_filter_actors([Actor|Unfiltered], Link, Filtering, Filtered) :-
   Actor = actor_data(_,Links),
   (memberchk(Link, Links) -> do_filter_actors(Unfiltered, Link, [Actor|Filtering], Filtered)
   ; do_filter_actors(Unfiltered, Link, Filtering, Filtered)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Filters a list of oracles to only those which haven't already been visited
%% @param Unfiltered [map_object]: The list of oracles to filter
%% @param Filtered []:
%% @returns Unqueried [map_object]: The list of unqueried oracles
filter_oracles([], Unqueried, Unqueried).
filter_oracles([Next | Unfiltered], Filtered, Unqueried) :-
	Next = map_object(o(OID), Pos),
	(agent_check_oracle(oscar, OID) -> filter_oracles(Unfiltered, Filtered, Unqueried)
	; filter_oracles(Unfiltered, [map_object(o(OID), Pos) | Filtered], Unqueried)
	).

%%% command shell %%%

shell:-
	get_input(Input),
	handle_input(Input).

handle_input(Input):-
	( Input = stop -> true
	; Input = reset -> ailp_reset,shell
	; Input = [H|T] -> handle_input(H),handle_input(T),shell
	; callable(Input,G,R) -> ( call(G) -> show_response(R) ; show_response('This failed.') ),shell
	; otherwise -> show_response('Unknown command, please try again.'),shell
	).

% get input from user
get_input(Input):-
	write('? '),read(Input).

% show answer to user
show_response(R):-
	( R=shell(Response)   -> writes('! '),writes(Response),writes(nl)
	; R=console(Response) -> term_to_atom(Response,A),do_command([oscar,console,A])
	; R=both(Response)    -> show_response(shell(Response)),show_response(console(Response))
	; R=agent(Response)   -> term_to_atom(Response,A),do_command([oscar,say,A])
	; R=[H|T]             -> show_response(H),show_response(T)
	; R=[]                -> true
	; otherwise           -> writes(['! ',R])
	).

writes(A):-
	( A=[]      -> nl
	; A=nl      -> nl
	; A=[H|T]   -> writes(H),writes(T)
	; A=term(T) -> write(T)
	; otherwise -> write(A)
	).

% callable(+Command, +Goal, ?Response)
callable(call(G),call(G),G).
callable(topup(S),agent_topup_energy(oscar,S),agent(topup)).
callable(energy,agent_current_energy(oscar,E),both(current_energy(E))).
callable(position,agent_current_position(oscar,P),both(current_position(P))).
callable(ask(S,Q),agent_ask_oracle(oscar,S,Q,A),A).
callable(Task,solve_task(Task,Cost),[console(Task),shell(term(Cost))]):-
	task(Task).

task(go(_Pos)).
task(find(_O)).	% oracle o(N) or charging station c(N)
